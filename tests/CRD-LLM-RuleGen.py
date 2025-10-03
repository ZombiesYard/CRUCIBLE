# crd_rulegen.py
import os, re, sys, json, shutil, subprocess, tempfile, textwrap, hashlib
from pathlib import Path
from typing import List, Tuple
import typer
import ruamel.yaml as ry
import datetime
import ast
from openai import OpenAI, APIConnectionError, APIStatusError, RateLimitError 

APP = typer.Typer(help="CRD 3-D Rule Generator (LLM → patch → run)")
_OAI_CLIENT = None
# ---- config ----
CRD_ROOT = Path(os.environ.get("CRD_ROOT", ".")).resolve()
FOUR_FILES = [
    "crdesigner/verification_repairing/verification/formula_ids.py",
    "crdesigner/verification_repairing/verification/groups_handler.py",
    "crdesigner/verification_repairing/verification/hol/formula_collection.py",
    "crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py",
]

# --- RAG (read-only code context) config ---
RAG_ENABLED = False  # default off; can enable via --rag
# Read-only scan directories (relative to CRD_ROOT); prioritize "functions/predicates/managers", etc.
RAG_DIRS = [
    "crdesigner/verification_repairing/verification/hol/functions",
    "crdesigner/verification_repairing/verification/hol",
    "crdesigner/verification_repairing",  # user can add more directories here
]
# Only scan these file patterns
RAG_GLOBS = ["**/*.py"]
# Read-only context max character count (to avoid token explosion)
RAG_MAX_CHARS = 16000

#openai SDK
OPENAI_MODEL = os.environ.get("OPENAI_MODEL", "gpt-4o")
OPENAI_API_KEY = os.environ.get("OPENAI_API_KEY")

def save_artifacts(prompt: str, response: str, yml: str, patch: str, smoke_log: str = "", code_ctx: str = "", rag_ctx: str = ""):
    tsdir = Path(CRD_ROOT) / ".llm_artifacts" / datetime.datetime.now().strftime("%Y%m%d-%H%M%S")
    tsdir.mkdir(parents=True, exist_ok=True)
    (tsdir / "prompt.txt").write_text(prompt, encoding="utf-8")
    (tsdir / "response.txt").write_text(response, encoding="utf-8")
    (tsdir / "yaml.yml").write_text(yml, encoding="utf-8")
    (tsdir / "patch.diff").write_text(patch, encoding="utf-8")
    if code_ctx:
        (tsdir / "code_context.txt").write_text(code_ctx, encoding="utf-8")
    if rag_ctx:
        (tsdir / "read_only_api.txt").write_text(rag_ctx, encoding="utf-8")
    if smoke_log:
        (tsdir / "smoke.log").write_text(smoke_log, encoding="utf-8")


# ==================== Formula String Normalization ====================
# Adapted from normalize_formula_strings.py

TARGET_NAMES = {"formulas", "subformulas"}
_src_text = ""  # module-level cache for AST source segment extraction


def _json_q(s: str) -> str:
    """JSON-quote (double quotes, proper escaping, keep non-ASCII)."""
    return json.dumps(s, ensure_ascii=False)


def _find_target_annassigns(tree: ast.AST) -> List[Tuple[ast.ClassDef, ast.AnnAssign]]:
    """
    Find `formulas: Dict[str, str] = {...}` and `subformulas: Dict[str, str] = {...}`
    assignments inside class bodies.
    """
    out: List[Tuple[ast.ClassDef, ast.AnnAssign]] = []
    for node in tree.body:
        if isinstance(node, ast.ClassDef):
            for ch in node.body:
                if isinstance(ch, ast.AnnAssign) and isinstance(ch.target, ast.Name):
                    if ch.target.id in TARGET_NAMES and isinstance(ch.value, ast.Dict):
                        out.append((node, ch))
    return out


def _collapse_value_to_str(v_node: ast.AST) -> str:
    """
    Convert a value node to a single-line string:
    - If it's a single string constant: return it as-is.
    - If it's adjacent string constants: try literal_eval to merge.
    - Else: fallback to source text and collapse newlines to spaces.
    """
    global _src_text
    if isinstance(v_node, ast.Constant) and isinstance(v_node.value, str):
        return v_node.value

    seg = ast.get_source_segment(_src_text, v_node)
    if seg is None:
        seg = str(v_node)

    try:
        lit = ast.literal_eval(seg)
        if isinstance(lit, str):
            return lit
    except Exception:
        pass

    return " ".join(seg.splitlines())


def _render_dict_block(d: ast.Dict, indent: str) -> str:
    """
    Render { "k": "v", ... } with uniform style:
    - key/value JSON-quoted
    - one entry per line with trailing comma
    - values are guaranteed single-line strings
    """
    global _src_text
    inner = indent + " " * 4
    parts = ["{"]

    for k_node, v_node in zip(d.keys, d.values):
        # key
        if isinstance(k_node, ast.Constant) and isinstance(k_node.value, str):
            key_txt = _json_q(k_node.value)
        else:
            k_src = ast.get_source_segment(_src_text, k_node) or str(k_node)
            key_txt = _json_q(k_src)

        # value → single-line string
        val = _collapse_value_to_str(v_node).replace("\n", " ")
        # micro-normalizations around '||'
        val = re.sub(r"\s+\|\|\s+", " || ", val)
        val = re.sub(r"\)\s+\|\|", ") ||", val)
        val_txt = _json_q(val)

        parts.append(f"{inner}{key_txt}: {val_txt},")

    parts.append(indent + "}")
    return "\n".join(parts)


def _lint_dict_values(d: ast.Dict, where: str) -> None:
    """
    Light linter: warn about common typos that break the ANTLR parser.
    - Unbalanced parentheses
    - Suspicious '||' placement at column 0 or right after '('
    """
    global _src_text
    for k_node, v_node in zip(d.keys, d.values):
        key = ast.get_source_segment(_src_text, k_node)
        expr = _collapse_value_to_str(v_node).replace("\n", " ")
        if not isinstance(key, str):
            key = str(key)

        # count parentheses
        if expr.count("(") != expr.count(")"):
            print(f"[LINT] Unbalanced parentheses in {where} key={key!r}: {expr!r}")

        # suspicious '||' (e.g., startswith '||', or '(||' )
        for m in re.finditer(r"\|\|", expr):
            i = m.start()
            prev = expr[i - 1] if i > 0 else ""
            if prev in {"", "(", "|"}:
                print(f"[LINT] Suspicious '||' placement in {where} key={key!r}: {expr!r}")


def normalize_formula_and_subformula_strings(path: Path) -> bool:
    """
    Normalize HOL formula strings in formula_collection.py:
    - Collapse adjacent string literals into a single string.
    - Render both `formulas` and `subformulas` dicts so that each value is a single-line string.
    - Preserve indentation; create a .bak backup.
    - Run a light linter to warn about unbalanced parentheses or suspicious '||' placements.
    
    Returns True if file was modified, False otherwise.
    """
    global _src_text
    _src_text = path.read_text(encoding="utf-8")

    try:
        tree = ast.parse(_src_text)
    except SyntaxError as e:
        print(f"[ERROR] Invalid Python syntax: {path}\n{e}")
        return False

    ann_list = _find_target_annassigns(tree)
    if not ann_list:
        print(f"[INFO] No formulas/subformulas dicts found in {path.name}. Skipped.")
        return False

    lines = _src_text.splitlines()
    repls = []

    # Lint pass (before rewriting)
    for cls, ann in ann_list:
        d = ann.value
        if isinstance(d, ast.Dict):
            _lint_dict_values(d, where=f"{cls.name}.{ann.target.id}")

    for _, ann in ann_list:
        d = ann.value
        if not (isinstance(d, ast.Dict) and hasattr(d, "lineno") and hasattr(d, "end_lineno")):
            continue

        start_line = d.lineno - 1
        end_line = d.end_lineno - 1
        start_col = d.col_offset
        end_col = getattr(d, "end_col_offset", None)

        indent = " " * start_col
        new_block = _render_dict_block(d, indent)

        line0 = lines[start_line]
        prefix = line0[:start_col]
        suffix = lines[end_line][end_col:] if end_col is not None else lines[end_line][:]
        repls.append((start_line, end_line, prefix, new_block, suffix))

    if not repls:
        print(f"[INFO] Found target names in {path.name} but could not locate dict blocks to replace (already normalized?).")
        return False

    # Apply replacements in reverse order to avoid shifting line numbers
    new_lines = lines[:]
    for start_line, end_line, prefix, new_block, suffix in sorted(repls, key=lambda x: x[0], reverse=True):
        block_text = prefix + new_block + suffix
        new_lines[start_line:end_line + 1] = [block_text]

    new_text = "\n".join(new_lines)
    if new_text != _src_text:
        bak = path.with_suffix(path.suffix + ".bak")
        bak.write_text(_src_text, encoding="utf-8")
        path.write_text(new_text, encoding="utf-8")
        print(f"[OK] Normalized: {path.name}  (backup: {bak.name})")
        return True

    print(f"[OK] {path.name} already normalized. No changes.")
    return False

# ==================== End Formula String Normalization ====================


def summarize_docstring(ds: str, limit: int = 160) -> str:
    if not ds:
        return ""
    first = ds.strip().splitlines()[0].strip()
    return (first[:limit] + "…") if len(first) > limit else first

def sig_from_args(args: ast.arguments) -> str:
    parts = []
    # Python 3.10: posonlyargs, args, vararg, kwonlyargs, kw_defaults, kwarg, defaults
    def fmt_arg(a: ast.arg) -> str:
        return a.arg

    # position-only
    for a in getattr(args, "posonlyargs", []):
        parts.append(fmt_arg(a))
    if getattr(args, "posonlyargs", []):
        parts.append("/")

    # normal args with defaults
    defaults = list(args.defaults or [])
    num_no_default = len(args.args) - len(defaults)
    for idx, a in enumerate(args.args):
        if idx < num_no_default:
            parts.append(fmt_arg(a))
        else:
            parts.append(f"{fmt_arg(a)}=…")  # do not show default value

    # varargs
    if args.vararg:
        parts.append(f"*{fmt_arg(args.vararg)}")
    elif args.kwonlyargs:
        parts.append("*")  # explicit separator

    # kwonly with defaults
    for a, d in zip(args.kwonlyargs, args.kw_defaults or []):
        if d is None:
            parts.append(fmt_arg(a))
        else:
            parts.append(f"{fmt_arg(a)}=…")

    # kwargs
    if args.kwarg:
        parts.append(f"**{fmt_arg(args.kwarg)}")

    return "(" + ", ".join(parts) + ")"

def extract_api_surface(py_path: Path) -> str:
    """
    read a single .py file, output:
    - Top-level functions: def name + signature + first line of docstring
    - (optional) class methods: for brevity, currently not expanding; can add specific class names if needed
    """
    try:
        txt = py_path.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return ""
    try:
        tree = ast.parse(txt)
    except Exception:
        return ""

    lines = [f"# READONLY FILE: {py_path.as_posix()}"]
    for node in tree.body:
        if isinstance(node, ast.FunctionDef):
            ds = ast.get_docstring(node) or ""
            sig = sig_from_args(node.args)
            lines.append(f"def {node.name}{sig}")
            sd = summarize_docstring(ds)
            if sd:
                lines.append(f'  """{sd}"""')
        elif isinstance(node, ast.ClassDef):
            # only display class names to avoid long output; can add whitelist for specific classes (e.g., FormulaManager)
            lines.append(f"class {node.name}: ...")
    return "\n".join(lines) + "\n"

def collect_read_only_context(dirs: List[str], globs: List[str], max_chars: int) -> str:
    acc, total = [], 0
    # exclude four writable files outside the whitelist
    writables = { (CRD_ROOT / p).resolve().as_posix() for p in FOUR_FILES }

    files = []
    for d in dirs:
        base = (CRD_ROOT / d).resolve()
        if not base.exists():
            continue
        for pat in globs:
            files.extend(sorted([p for p in base.glob(pat) if p.is_file() and p.name.endswith(".py")],
                                key=lambda x: x.as_posix()))
    # delete duplicates (overlap from different dirs/patterns)
    seen = set()
    for py in files:
        px = py.resolve().as_posix()
        if px in seen or px in writables:
            continue
        seen.add(px)
        block = extract_api_surface(py)
        if not block:
            continue
        if total + len(block) > max_chars:
            acc.append("\n# --- TRUNCATED: reached RAG_MAX_CHARS ---\n")
            break
        acc.append(block); total += len(block)
    return "\n".join(acc)


def _get_openai_client() -> OpenAI:
    global _OAI_CLIENT
    if _OAI_CLIENT is None:
        # support custom base_url and organization, may be used
        _OAI_CLIENT = OpenAI(
            api_key=os.environ.get("OPENAI_API_KEY"),
        )
    return _OAI_CLIENT

def run(cmd: List[str], cwd: Path = None, check=True) -> subprocess.CompletedProcess:
    p = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    if check and p.returncode != 0:
        raise RuntimeError(f"cmd failed: {' '.join(cmd)}\nstdout:\n{p.stdout}\nstderr:\n{p.stderr}")
    return p

def git_clean_tree_or_die():
    st = run(["git", "status", "--porcelain"], cwd=CRD_ROOT).stdout.strip()
    if st:
        raise RuntimeError("Git tree not clean. Commit/stash your changes first.")

def new_branch(slug: str):
    name = f"llm-rules/{slug}"
    p = run(["git", "rev-parse", "--verify", "--quiet", name], cwd=CRD_ROOT, check=False)
    if p.returncode == 0:
        name += "-" + datetime.datetime.now().strftime("%H%M%S")
    run(["git", "checkout", "-b", name], cwd=CRD_ROOT)


CODE_CTX_MAX_CHARS = 100000 
def collect_file_slices(paths: List[str], context=1200) -> str:
    parts = []
    total = 0
    for rel in paths:
        p = CRD_ROOT / rel
        txt = p.read_text(encoding="utf-8")
        parts.append(f"# FILE: {rel}\n{txt}\n")
        total += len(txt)
    return "\n\n".join(parts)

def build_prompt(nl_rules: str, code_context: str, ro_api: str = "", diff_only: bool = False) -> str:
    """
    Anchor-first, family-gated prompt that prevents example bias (e.g., vertical_clearance leakage).
    Always emits OPS; DIFF is optional and must pass strict hygiene checks.
    """
    import textwrap

    FOUR_FILES = [
        "crdesigner/verification_repairing/verification/formula_ids.py",
        "crdesigner/verification_repairing/verification/groups_handler.py",
        "crdesigner/verification_repairing/verification/hol/formula_collection.py",
        "crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py",
    ]

    RULE_ONTOLOGY = """
    ### Rule identification & ontology (MUST do this first)

    1) Decide the semantic KIND and ARITY:
    - kind: lanelet | lanelet_pair | network
    - arity: 1 (lanelet) or 2 (lanelet_pair). For pairwise constraints (distance/clearance/relative angle), use arity=2.

    2) Pick a FAMILY:
    - Use one of the known families IF AND ONLY IF it exactly matches the user's intent:
        * grade_limit         — longitudinal grade along centerline (Δz/Δs)
        * bank_angle_limit    — transverse slope/camber across boundaries (Δz/Δw or angle)
        * vertical_clearance  — height gap between two overlapping lanelets
    - Otherwise choose: novel

    3) Define identifiers (deterministically from the NL intent):
    - rule_key       : lower_snake_case, concise noun phrase (e.g., min_plan_radius)
    - enum_name      : UPPER_SNAKE_CASE in LaneletFormulaID (e.g., MIN_PLAN_RADIUS)
    - predicate_name : lower_snake verb phrase, polarity “too_*” or “*_sufficient”
                        (e.g., is_plan_radius_too_small / is_grade_too_steep)
    - Keep naming consistent across files.

    4) If family == novel:
    - You MUST write a small spec for the measurement (what to compute), including:
        * data sources (centerline vertices / polygons / adjacencies),
        * gating/guards (XY overlap? minimal segment length? 2-D compatibility?),
        * thresholds with reasonable defaults and units,
        * polarity (negative predicate returns True on violation),
        * exception policy (log + conservative result).
    - The measurement MUST be implementable using existing imports and utilities only.

    5) Output these fields in the FIRST YAML block in addition to the required keys:
    family, family_reason, kind, arity, rule_key, enum_name, predicate_name, defaults
    """.strip()

    FAMILY_SPECS = """
    ### Canonical specs for known families (use ONLY if matched)
    - grade_limit (kind=lanelet, arity=1):
        * metric : max(|Δz|/Δs) over consecutive centerline samples
        * 2D     : if center_vertices has <3 columns → PASS (compat)
        * guards : skip segments with Δs≈0 (min_seg_len_m), filter non-finite grades
        * polarity: is_grade_too_steep(l, *, max_grade_pct) → True iff grade > max_grade_pct/100
        * defaults: max_grade_pct=8.0 unless user says otherwise
        * exceptions: warning + return True (conservative for “too_*”)

    - bank_angle_limit (kind=lanelet, arity=1):
        * metric : transverse slope across left/right boundaries (Δz/Δw) or bank angle
        * 2D     : if Z missing → PASS
        * polarity: is_bank_angle_too_large(l, *, max_bank_pct) → True on violation
        * defaults: max_bank_pct=6.0 (example) unless user provides
        * exceptions: conservative True

    - vertical_clearance (kind=lanelet_pair, arity=2):
        * gating : XY intersection required (ignore tiny overlaps via area_tol_m2/length_tol_m)
        * 2D     : if either lanelet lacks Z → PASS
        * metric : dz = |mean(z1) − mean(z2)|
        * epsilon: if dz < eps_same_layer_m → PASS (same layer)
        * polarity: is_vertical_clearance_too_low(l1,l2,*,min_clearance_m) → True iff dz < min_clearance_m
        * defaults: min_clearance_m=5.0 unless user provides
        * exceptions: conservative True

    ### Novel-family contract (family=novel; MUST supply all below)
    - Describe the metric in one sentence and in 3–6 lines of pseudocode.
    - State kind and arity explicitly. Examples:
        * “min_plan_radius” (lanelet, arity=1): compute discrete turning radius along centerline using 3-point circle;
        skip collinear triplets (infinite radius), require ≥3 points, default min_radius_m=10.0.
        * “min_spacing_between_lanelets” (lanelet_pair, arity=2): min XY distance between polygons with small-overlap gating.
    - Guards & compatibility:
        * 2D → pass if Z needed but missing (unless metric is purely XY).
        * Degenerate/zero-length segments → skip.
        * Use area/length tolerances to ignore tiny overlaps when relevant.
    - Polarity & exceptions:
        * Prefer negative predicates “too_*” that return True on violation.
        * On exception: log warning and return True for negative predicates.
    - Determinism: no randomness, no recursion, bounded loops only.
    """.strip()

    HARD_FORBIDS = """
    ### Hard constraints (STRICT)
    - Use ONLY the identifiers you declare in the FIRST YAML block:
    enum_name, rule_key, predicate_name. Do NOT emit identifiers from unrelated families.
    - The mapping in `formula_collection.py` MUST be inserted under `LaneletFormulas.formulas`
    (NOT GeneralFormulas), as a ONE-LINE PARENTHESIZED STRING value.
    - No numeric kwargs inside formula strings. Thresholds live inside the predicate signature.
    - New predicates MUST be module-scope in `lanelet_predicates.py` (def at column 0).

    ### Generic anchoring rules (no family leakage)
    - `verification/formula_ids.py`:
    Add `enum_name` under `class LaneletFormulaID(enum.Enum):` keeping 4-space indent.
    - `verification/groups_handler.py`:
    Append `LaneletFormulaID.<enum_name>` to an existing `SpecificationGroup(..., formulas=[ ... ])`
    that already contains other lanelet formula IDs. Preserve indentation and trailing comma.
    - `verification/hol/formula_collection.py`:
    Insert into `class LaneletFormulas: formulas = { ... }` a line:
        "<rule_key>": "( !(Is_<predicate_name>(<vars_without_kwargs>)) || <vars_in_L> )",
    where <vars_without_kwargs> is `l` for arity=1, or `l1, l2` for arity=2, and `<vars_in_L>`
    is `l in L` or `l1, l2 in L` respectively.
    - `verification/hol/functions/predicates/lanelet_predicates.py`:
    Implement or extend `predicate_name` with OPTIONAL kwargs only; keep existing imports unchanged.

    ### Diff skeleton (family-agnostic; DO NOT hardcode previous examples)
    python_patch: |
    --- crdesigner/verification_repairing/verification/formula_ids.py
    +++ crdesigner/verification_repairing/verification/formula_ids.py
    @@ -<old>,<n> +<new>,<m> @@
    <6+ BEFORE context>
    +    {{ENUM_NAME}} = "{{rule_key}}"
    <6+ AFTER context>

    --- crdesigner/verification_repairing/verification/groups_handler.py
    +++ crdesigner/verification_repairing/verification/groups_handler.py
    @@ -<old>,<n> +<new>,<m> @@
    <6+ BEFORE context (a formulas=[...])>
    +                    LaneletFormulaID.{{ENUM_NAME}},
    <6+ AFTER context>

    --- crdesigner/verification_repairing/verification/hol/formula_collection.py
    +++ crdesigner/verification_repairing/verification/hol/formula_collection.py
    @@ -<old>,<n> +<new>,<m> @@
    <6+ BEFORE context inside LaneletFormulas.formulas>
    +                "{{rule_key}}": "( !(Is_{{predicate_name}}({{ARGS}})) || {{IN_L}} )",
    <6+ AFTER context>

    --- crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py
    +++ crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py
    @@ -<old>,<n> +<new>,<m> @@
    <6+ BEFORE context>
    +def {{predicate_name}}({{SIG}}) -> bool:
    +    ...
    <6+ AFTER context>

    Where:
    - {{ENUM_NAME}}      = enum_name
    - {{ARGS}}           = "l" (arity=1) OR "l1, l2" (arity=2)
    - {{IN_L}}           = "l in L" OR "l1, l2 in L"
    - {{SIG}}            = "l: Lanelet, *, <optional kwargs>" OR
                            "lanelet_0: Lanelet, lanelet_1: Lanelet, *, <optional kwargs>"
    """.strip()

    NO_NUMERIC_IN_FORMULAS = """
    ### Formula mapping policy
    - In `formula_collection.py`, DO NOT pass numeric kwargs inside formula strings.
    - Values MUST be **double-quoted single-line strings**. Examples:
        "slope_limit": "!(Is_grade_too_steep(l)) || l in L",
        "bank_angle_limit": "!(Is_bank_angle_too_large(l)) || l in L",
        "clearance_limit": "!(Is_vertical_clearance_too_low(l1, l2)) || l1, l2 in L"
    - Thresholds/defaults live in predicate signatures in `lanelet_predicates.py`.
    """.strip()

    UNIFIED_DIFF_HYGIENE = """
    ### Unified diff hygiene (STRICT)
    1) Headers at column 0:
       --- <path>
       +++ <same path>
    2) At least one '@@ ' per changed file; hunk lines start with ' ' or '+' or '-' or '\\\\'.
    3) Anchor-based: include ≥6 verbatim BEFORE and ≥6 AFTER lines; NEVER guess line numbers.
    4) Minimal touch; no unrelated reformatting.
    5) If uncertain, DROP that file’s diff; still produce complete ops.
    """.strip()

    ANCHORING_RULES = """
    ### Anchoring rules (no absolute line numbers)
    - formula_ids.py: insert enum under class LaneletFormulaID(enum.Enum) next to existing members (4-space indent).
    - groups_handler.py: append enum into an existing SpecificationGroup that already lists LaneletFormulaID.* geometry checks.
      Fallback: the first SpecificationGroup.
    - formula_collection.py: upsert into
        class LaneletFormulas:
            formulas: Dict[str, str] = { ... }
      If the same key exists in GeneralFormulas.formulas, REMOVE it there.
    - lanelet_predicates.py: add predicate at module scope.
      Preferred anchor: just above `def has_stop_line(lanelet: Lanelet):` (or the last predicate).
    """.strip()

    GENERIC_PATCH_SKELETON = """
    ## Example diff skeleton (generic; NEVER reuse these identifiers; fill with your chosen quartet)
    python_patch: |
    --- crdesigner/verification_repairing/verification/formula_ids.py
    +++ crdesigner/verification_repairing/verification/formula_ids.py
    @@ -<old>,<n> +<new>,<m> @@
     <BEFORE x6>
    +    <ENUM_NAME> = "<RULE_KEY>"
     <AFTER x6>

    --- crdesigner/verification_repairing/verification/groups_handler.py
    +++ crdesigner/verification_repairing/verification/groups_handler.py
    @@ -<old>,<n> +<new>,<m> @@
     <BEFORE x6>
    +                    LaneletFormulaID.<ENUM_NAME>,
     <AFTER x6>

    --- crdesigner/verification_repairing/verification/hol/formula_collection.py
    +++ crdesigner/verification_repairing/verification/hol/formula_collection.py
    @@ -<old>,<n> +<new>,<m> @@
     <BEFORE x6>   # inside LaneletFormulas.formulas
    +            "<RULE_KEY>": "!(Is_<PRED_NAME>(<l_or_l1l2>)) || <L_or_L1L2>",
     <AFTER x6>

    --- crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py
    +++ crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py
    @@ -<old>,<n> +<new>,<m> @@
     <BEFORE x6>
    +def <pred_name>(...):
    +    ...
     <AFTER x6>
    """.strip()

    OPS_SCHEMA = """
    ### Ops schema (MANDATORY; must be inside the FIRST YAML block)
    family: <grade_limit | bank_angle_limit | vertical_clearance>
    rule_key: <lower_snake_case_key>         # e.g., grade_limit
    enum_name: <UPPER_SNAKE_ENUM>            # e.g., GRADE_LIMIT
    predicate_name: <predicate_function>     # e.g., is_grade_too_steep

    ops:
      - type: add_enum_member
        file: crdesigner/verification_repairing/verification/formula_ids.py
        enum_class: LaneletFormulaID
        name: <ENUM_NAME>
        value: <rule_key>

      - type: add_to_group
        file: crdesigner/verification_repairing/verification/groups_handler.py
        insert_near_anchor: <an existing LaneletFormulaID.* in that list>
        add: LaneletFormulaID.<ENUM_NAME>

      - type: upsert_formula_mapping
        file: crdesigner/verification_repairing/verification/hol/formula_collection.py
        key: <rule_key>
        value: "<EXPR>"   # MUST be a double-quoted one-line string; no numeric kwargs inside

      - type: ensure_predicate
        file: crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py
        name: <predicate_name>
        code: |
          def <predicate_name>(...):
              # module-scope; optional kwargs with safe defaults; deterministic; guards for 2-D, degeneracy, GEOSException
              ...
    """.strip()

    out_contract_when_full = (
        "1) FIRST fenced YAML block (MANDATORY) with keys:\n"
        "   antlr_patch: \"NO_CHANGE\"\n"
        "   python_patch: unified diff (only the four files), or empty if any file fails hygiene\n"
        "   family, rule_key, enum_name, predicate_name (see ops schema)\n"
        "   ops: a complete semantic plan\n"
        "2) Then four full replacement files (same four) if not diff-only.\n"
        "3) End with a short post-check list.\n"
        "If any DIFF file fails hygiene, DROP that file from python_patch but keep full ops."
    )
    out_contract_when_diff_only = (
        "1) FIRST fenced YAML block (MANDATORY) with keys:\n"
        "   antlr_patch: \"NO_CHANGE\"\n"
        "   python_patch: unified diff (only the four files), or empty if any file fails hygiene\n"
        "   family, rule_key, enum_name, predicate_name\n"
        "   ops: a complete semantic plan\n"
        "2) Then a short post-check list.\n"
        "**Do NOT output full files in this mode.**"
    )
    OUTPUT_CONTRACT = out_contract_when_full if not diff_only else out_contract_when_diff_only

    SYSTEM = textwrap.dedent(f"""
    You are a senior ANTLR/HOL engineer and Python geomatics developer for CRD 3-D validation.
    Edit ONLY these four files. Never touch Formula.g4. Be deterministic and compile-ready.
    Keep 2-D behavior bit-for-bit identical when Z is missing (predicates must pass and never raise).
    Logging via: `log3d = logging.getLogger("crdesigner.verification.3d")`.
    **No-op is forbidden**: for any new rule you MUST (a) add enum; (b) add to a group; (c) add formula mapping; (d) ensure predicate.

    {RULE_ONTOLOGY}
    {FAMILY_SPECS}
    {HARD_FORBIDS}
    {NO_NUMERIC_IN_FORMULAS}
    {UNIFIED_DIFF_HYGIENE}
    {ANCHORING_RULES}
    """).strip()

    ro_block = f"""
    ## Read-only API surface (context; DO NOT modify these files)
    {ro_api if ro_api else "(no extra context)"}
    """.rstrip()

    USER = textwrap.dedent(f"""
    # CRD 3-D Validation — Robust Minimal-Change Prompt (Family-gated, Anchor-based)

    ## Output contract
    {OUTPUT_CONTRACT}

    ## Example (generic skeleton; NEVER reuse identifiers literally)
    {GENERIC_PATCH_SKELETON}

    ### Ops schema (MANDATORY; use exactly these fields)
    {OPS_SCHEMA}

    ---
    ## Step 1 — Current code (trimmed for anchors)
    {code_context}
    {ro_block}

    ---
    ## Step 2 — Understand the natural-language rule(s)
    - Classify into exactly ONE family from the matrix.
    - Derive identifiers:
        enum_name  = <UPPER_SNAKE> from the rule (must be new or an extension)
        rule_key   = <lower_snake> used as dict key
        predicate_name = function name consistent with polarity (e.g., *_too_* returns True on violation)
    - Extract thresholds/semantics into a LATER fenced YAML block named `requirements:` (NOT the first YAML).
    - If user text supplies numbers (e.g., "2%"), use them; otherwise safe defaults per the chosen spec.

    ### Natural-language rule(s)
    {nl_rules}

    ---
    ## Step 3 — Produce BOTH
    - A strictly-valid unified diff (if possible), AND
    - A complete ops plan (ALWAYS).
      If diff hygiene fails for any file, DROP that file from python_patch but keep ops.

    ---
    ## Step 4 — Post-check (acceptance criteria)
    - family/enum_name/rule_key/predicate_name are consistent and appear in the expected places ONLY.
    - formula_collection: value is a **double-quoted single line**; placed inside LaneletFormulas.formulas; if present in GeneralFormulas, remove there.
    - lanelet vs lanelet_pair variables: use `l` and `|| l in L` for single, `l1, l2` and `|| l1, l2 in L` for pair.
    - Predicates: pure, deterministic, Z-missing PASS, degeneracy guards, no division-by-zero, GEOSException guarded.
    """).strip()

    return f"<SYSTEM>\n{SYSTEM}\n</SYSTEM>\n\n<USER>\n{USER}\n</USER>\n"




def call_llm(prompt: str) -> str:
    """
    Use OpenAI official SDK's Responses API to call gpt-4o.
    - By default read model name from OPENAI_MODEL (gpt-4o if unset)
    - Return plain text (the model-generated full message body)
    - Raise exceptions with context on errors
    """
    model_name = OPENAI_MODEL
    client = _get_openai_client()
    try:
        # The Responses API supports passing the entire prompt as input
        resp = client.responses.create(
            model=model_name,
            input=prompt,
            temperature=0,           # set to 0 for deterministic output
            #max_output_tokens=120000, # uncomment to enable long output; not set for server to decide
            timeout=float(globals().get("_OPENAI_REQ_TIMEOUT", 120.0))          # seconds, adjust as needed
        )
        # The official SDK aggregates text attributes
        text = resp.output_text
        if not text or not isinstance(text, str):
            raise RuntimeError("LLM response is empty or not text.")
        return text
    except RateLimitError as e:
        raise RuntimeError(f"[OpenAI] Rate limit exceeded: {e}") from e
    except APIConnectionError as e:
        raise RuntimeError(f"[OpenAI] Connection failed: {e}") from e
    except APIStatusError as e:
        # 例如 400/401/5xx 等
        code = getattr(e, "status_code", "?")
        rid = getattr(e, "request_id", None)
        raise RuntimeError(f"[OpenAI] Status error({code}) req_id={rid}: {e}") from e
    except Exception as e:
        raise RuntimeError(f"[OpenAI] Unknown error: {e}") from e

def extract_yaml_and_patch(text: str) -> Tuple[str, str]:
    """
    From **all** ```yaml fenced blocks, locate the one that contains antlr_patch/python_patch.
    Compatible with the case where requirements YAML is output first, followed by patch YAML.
    """
    blocks = re.findall(r"```yaml\s*(.*?)\s*```", text, re.S | re.I)
    chosen = None
    yaml = ry.YAML(typ="safe")
    for blk in blocks:
        try:
            data = yaml.load(blk)
            if isinstance(data, dict) and "antlr_patch" in data and "python_patch" in data:
                chosen = blk
                break
        except Exception:
            continue
    if not chosen:
        #Degrade: scan the plain text area (to avoid the model not using fenced blocks)
        start = re.search(r"^\s*antlr_patch\s*:\s*", text, re.M)
        if not start:
            raise RuntimeError("not found YAML with antlr_patch/python_patch. Hint: ensure patch YAML is the first fenced `yaml` block.")
        end = re.search(r"^```", text[start.start():], re.M)
        chosen = text[start.start():(start.start() + (end.start() if end else len(text)))]
        data = yaml.load(chosen)
    else:
        data = yaml.load(chosen)

    if not isinstance(data, dict) or "antlr_patch" not in data or "python_patch" not in data:
        raise RuntimeError("YAML 缺少 antlr_patch/python_patch。")
    if str(data["antlr_patch"]).strip() != "NO_CHANGE":
        raise RuntimeError('antlr_patch must be "NO_CHANGE".')
    patch = data["python_patch"]
    if ("--- " not in patch) or ("+++ " not in patch):
        raise RuntimeError("python_patch is not a valid unified diff.")
    if "@@ " not in patch:
        raise RuntimeError("python_patch is missing hunk marker (@@), suspected empty change.")
    return chosen, patch

def ensure_patch_only_four_files(patch: str):
    allowed = set(FOUR_FILES)
    def norm(s: str) -> str:
        if s.startswith(("a/", "b/")): s = s[2:]
        return Path(s).as_posix()
    bad, devnull_used = [], False
    touched = set()
    old_path = new_path = None
    for line in patch.splitlines():
        if line.startswith("--- "):
            p = line[4:].strip()
            if p in ("a/dev/null", "b/dev/null"):
                devnull_used = True
                old_path = None
            else:
                old_path = norm(p)
        elif line.startswith("+++ "):
            p = line[4:].strip()
            if p in ("a/dev/null", "b/dev/null"):
                devnull_used = True
                new_path = None
            else:
                new_path = norm(p)
            # check parir-wise
            for q in (old_path, new_path):
                if q is None:  # dev/null involves addition/deletion/renaming
                    continue
                if (".." in q.split("/")):
                    bad.append(q); continue
                if q not in allowed:
                    bad.append(q)
            if old_path: touched.add(old_path)
            if new_path: touched.add(new_path)
    if devnull_used:
        raise RuntimeError("patch involves addition/deletion/renaming (dev/null), forbidden.")
    if bad:
        raise RuntimeError(f"patch touches disallowed files: {sorted(set(bad))}")
    if not touched:
        raise RuntimeError("patch does not modify any whitelisted files.")

def _diff_added_lines_for_file(patch: str, relpath: str) -> List[str]:
    cur = None
    added = []
    def norm(p: str) -> str:
        if p.startswith(("a/", "b/")): p = p[2:]
        return Path(p).as_posix()
    for line in patch.splitlines():
        if line.startswith(("--- ", "+++ ")):
            p = line[4:].strip()
            if p in ("a/dev/null", "b/dev/null"):
                cur = None
            else:
                cur = norm(p)
        elif line.startswith("+") and not line.startswith("+++ "):
            if cur == relpath:
                added.append(line[1:])
    return added

def _new_ids_from_formula_ids(added_lines: List[str]) -> List[tuple[str, str]]:
    pairs = []
    for ln in added_lines:
        m = re.match(r'\s*([A-Z0-9_]+)\s*=\s*"([^"]+)"', ln)
        if m:
            pairs.append((m.group(1), m.group(2)))  # (CONST_NAME, "string_key")
    return pairs

def enforce_minimal_semantic_changes(patch: str):
    ids_added = _diff_added_lines_for_file(patch, FOUR_FILES[0])
    new_pairs = _new_ids_from_formula_ids(ids_added)
    if not new_pairs:
        raise RuntimeError("formula_ids.py did not add any LaneletFormulaID enum.")

    groups_added = _diff_added_lines_for_file(patch, FOUR_FILES[1])
    formulas_added = _diff_added_lines_for_file(patch, FOUR_FILES[2])

    for const, key in new_pairs:
        if not any(f"LaneletFormulaID.{const}" in ln for ln in groups_added):
            raise RuntimeError(f"groups_handler.py did not add {const} to the default group.")
        key_pat = re.compile(rf'["\']{re.escape(key)}["\']\s*:')
        if not any(key_pat.search(ln) for ln in formulas_added):
            raise RuntimeError(f"formula_collection.py did not add formula mapping for key '{key}:'.")
    

def call_llm_stream(prompt: str) -> str:
    client = _get_openai_client()
    with client.responses.stream(
        model=OPENAI_MODEL,
        input=prompt,
        temperature=0,
        #max_output_tokens=120000,
        timeout=float(globals().get("_OPENAI_REQ_TIMEOUT", 120.0))

    ) as stream:
        # gather the final response after the stream ends
        final = stream.get_final_response()
        return final.output_text

def call_llm_with_retry(prompt: str, reason: str = "", retries: int = 1, *, diff_only: bool = False) -> str:
    note_tail = "Produce the minimal patch only." if diff_only else "Produce the minimal patch and full files."
    full = prompt if not reason else prompt + (
        f"\n\n[SYSTEM NOTE]\nPrevious attempt failed: {reason}\n"
        f"Follow the contract. No-op forbidden. {note_tail}\n"
    )
    try:
        return call_llm(full)
    except Exception as e:
        if "Timeout" in str(e) or "timed out" in str(e):
            try:
                return call_llm_stream(full)
            except Exception:
                pass
        if retries > 0:
            return call_llm_with_retry(prompt, reason=str(e), retries=retries-1, diff_only=diff_only)
        raise



def apply_patch(patch: str):

    def _has_cmd(name: str) -> bool:
        from shutil import which
        return which(name) is not None
    
    import tempfile
    from pathlib import Path

    with tempfile.TemporaryDirectory() as td:
        pf = Path(td) / "patch.diff"
        pf.write_text(patch, encoding="utf-8")

        #first, strict checking (context matching)
        chk = subprocess.run(["git", "apply", "-p1", "--check", str(pf)],
                             cwd=CRD_ROOT, text=True, capture_output=True)
        if chk.returncode == 0:
            subprocess.check_call(["git", "apply", "-p1", str(pf)], cwd=CRD_ROOT)
            return

        #If it fails, try 3-way (to handle offset/minor conflicts)
        three = subprocess.run(["git", "apply",  "-p1", "--3way", "--check", str(pf)],
                               cwd=CRD_ROOT, text=True, capture_output=True)
        if three.returncode == 0:
            subprocess.check_call(["git", "apply",  "-p1", "--3way", str(pf)], cwd=CRD_ROOT)
            return

        # If all else fails, try GNU patch (more lenient, last resort)
        if _has_cmd("patch"):
            dry = subprocess.run(["patch", "-p1", "--dry-run", "-i", str(pf)],
                                 cwd=CRD_ROOT, text=True, capture_output=True)
            if dry.returncode == 0:
                subprocess.check_call(["patch", "-p1", "-i", str(pf)], cwd=CRD_ROOT)
                return

            # Last resort: ignore whitespace changes
            dry_l = subprocess.run(["patch", "-p1", "-l", "--dry-run", "-i", str(pf)],
                                   cwd=CRD_ROOT, text=True, capture_output=True)
            if dry_l.returncode == 0:
                subprocess.check_call(["patch", "-p1", "-l", "-i", str(pf)], cwd=CRD_ROOT)
                return
        else:
            dry = subprocess.CompletedProcess(args=[], returncode=1, stderr="patch command not found")


        # All attempts failed, raise with logs
        raise RuntimeError(
            "patch could not be applied automatically.\n"
            f"git apply --check stderr:\n{chk.stderr}\n\n"
            f"git apply --3way --check stderr:\n{three.stderr}\n\n"
            f"patch --dry-run stderr:\n{dry.stderr}\n"
        )
    
def preflight_openai() -> None:
    client = _get_openai_client()
    try:
        _ = client.responses.create(
            model=OPENAI_MODEL,               
            input="preflight",
            temperature=0,
            max_output_tokens=32,
            timeout=30.0
        )
    except Exception as e:
        raise RuntimeError(
            f"[Preflight] OpenAI connection failed: {e}\n"
            "Please check: whether OPENAI_API_KEY is effective in the current shell; whether OPENAI_BASE_URL is set; whether there is a proxy causing a timeout."
        )

def normalize_patch(raw: str) -> str:
    """
    Clean and "self-heal" LLM-generated unified diff:
    1) Remove ```diff/``` fences and CRLF;
    2) Truncate from the first (possibly indented) '--- ';
    3) Left-align file headers/hunk headers (---/+++/@@);
    4) Fix lines in hunk body without prefix (add ' ');
    5) Recalculate and rewrite hunk header line counts (@@ -a,b +c,d @@);
    6) Fix indentation issues in added lines.
    """
    s = raw.strip()


    #get rid of ```diff or ``` fences
    import re
    s = re.sub(r"^```(?:diff)?\s*", "", s)
    s = re.sub(r"\s*```$", "", s)

    #uniform line ending: CRLF -> LF
    s = s.replace("\r\n", "\n")

    #from the first (possibly indented) '--- ' to start
    m = re.search(r"(?m)^\s*---\s", s)
    if m:
        s = s[m.start():]

    # Left-align file headers/hunk headers (---/+++/@@)
    s = re.sub(r"(?m)^\s+(?=(--- |\+\+\+ |@@ ))", "", s)

    lines = s.split("\n")
    out = []
    i, n = 0, len(lines)
    current_file = None
    
    while i < n:
        ln = lines[i]

        # File header: copy directly and record the current file
        if ln.startswith('--- '):
            out.append(ln)
            # Extract file path
            path = ln[4:].strip()
            if path.startswith('a/'):
                path = path[2:]
            current_file = path
            i += 1
            continue
            
        if ln.startswith('+++ '):
            out.append(ln)
            i += 1
            continue

        # Enter a hunk: @@ -a,b +c,d @@ (trailer optional)
        if ln.startswith('@@ '):
            m = re.match(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@(.*)$', ln)
            if not m:
                # Irregular header, copy directly
                out.append(ln)
                i += 1
                continue

            old_start = int(m.group(1))
            old_len_in_hdr = m.group(2)
            new_start = int(m.group(3))
            new_len_in_hdr = m.group(4)
            trailer = m.group(5) or ""

            # Collect the body of this hunk until the next @@ / file header / end
            body_start = i + 1
            j = body_start
            while j < n and not (lines[j].startswith('@@ ') or lines[j].startswith('--- ') or lines[j].startswith('+++ ')):
                j += 1
            hunk_body = lines[body_start:j]

            # Fix: any line not starting with ' ' / '+' / '-' / '\' gets a prefix space; empty lines become ' '
            # Also fix indentation issues
            fixed_body = []
            for b in hunk_body:
                if b == "":
                    fixed_body.append(" ")
                elif b[0] in (" ", "+", "-", "\\"):
                    # For added lines, ensure correct indentation
                    if b.startswith('+'):
                        content = b[1:]
                        # Check if it's Python code and needs indentation
                        if current_file and current_file.endswith('.py'):
                            # If content is not empty and does not start with whitespace, it may need indentation
                            # Determine this based on the indentation pattern in the context
                            if content and not content.startswith((' ', '\t')):
                                # Find the preceding context lines to determine indentation
                                indent = ""
                                for prev in reversed(fixed_body):
                                    if prev.startswith((' ', '+')):
                                        prev_content = prev[1:] if prev[0] in ('+', '-') else prev
                                        if prev_content.strip():  # Non-empty line
                                            # Extract indentation
                                            indent_match = re.match(r'^(\s*)', prev_content)
                                            if indent_match:
                                                indent = indent_match.group(1)
                                                break
                                # Apply indentation
                                if indent:
                                    fixed_body.append('+' + indent + content)
                                else:
                                    fixed_body.append(b)
                            else:
                                fixed_body.append(b)
                        else:
                            fixed_body.append(b)
                    else:
                        fixed_body.append(b)
                else:
                    fixed_body.append(" " + b)

            # Recalculate line counts
            old_count = sum(1 for b in fixed_body if b.startswith(' ') or b.startswith('-'))
            new_count = sum(1 for b in fixed_body if b.startswith(' ') or b.startswith('+'))

            # Rewrite hunk header
            new_hdr = f"@@ -{old_start},{old_count} +{new_start},{new_count} @@{trailer}"
            out.append(new_hdr)
            out.extend(fixed_body)

            i = j
            continue

        # Other lines (e.g., diff noise), copy directly
        out.append(ln)
        i += 1

    s = "\n".join(out).rstrip() + "\n"
    return s

def fix_unified_diff(patch: str) -> str:
    """
    recompute old/new line counts in each hunk header '@@ -a,b +c,d @@',
    ignoring the original b/d which are often incorrect.
    Only lines starting with ' ', '+', '-' are counted as hunk body.
    """
    lines = patch.replace("\r\n", "\n").splitlines()
    out = []
    i = 0

    def is_file_hdr(k: int) -> bool:
        return k < len(lines) and lines[k].startswith(("--- ", "+++ "))

    while i < len(lines):
        ln = lines[i]

        # skip non-header lines until find '--- '
        if not ln.startswith("--- "):
            i += 1
            continue

        # --- old
        out.append(ln); i += 1
        if i >= len(lines) or not lines[i].startswith("+++ "):
            raise RuntimeError("Malformed diff: missing '+++' after '---'.")
        # +++ new
        out.append(lines[i]); i += 1

        # Process all hunks for this file
        while i < len(lines) and not lines[i].startswith("--- "):
            if lines[i].startswith("@@ "):
                # Parse @@ -a[,b] +c[,d] @@<trail>
                m = re.match(r'^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@(.*)$', lines[i])
                if not m:
                    raise RuntimeError(f"Malformed hunk header: {lines[i]}")
                old_start = int(m.group(1))
                new_start = int(m.group(2))
                trailer = m.group(3) or ""
                i += 1

                # Collect hunk body until the next hunk or file
                body = []
                while i < len(lines) and not lines[i].startswith(("@@ ", "--- ")):
                    line = lines[i]
                    if line == "" or line[0] not in " +-\\":
                        body.append(" " + line)
                    else:
                        body.append(line)
                    i += 1

                old_cnt = sum(1 for b in body if b.startswith((" ", "-")))
                new_cnt = sum(1 for b in body if b.startswith((" ", "+")))
                out.append(f"@@ -{old_start},{old_cnt} +{new_start},{new_cnt} @@{trailer}")
                out.extend(body)
                continue
            else:
                # Copy the empty line at the end of the file
                out.append(lines[i]); i += 1

    fixed = "\n".join(out)
    if not fixed.endswith("\n"):
        fixed += "\n"
    return fixed

def _fix_formula_ids_indentation(p: Path) -> bool:
    """
    Let the LaneletFormulaID(enum.Enum) members be uniformly indented with 4 spaces.
    Return whether the file was modified.
    """
    try:
        txt = p.read_text(encoding="utf-8")
    except Exception:
        return False
    lines = txt.splitlines(keepends=False)
    out = []
    i, n = 0, len(lines)
    changed = False

    while i < n:
        ln = lines[i]
        out.append(ln)
        # anchor to class LaneletFormulaID(enum.Enum):
        if re.match(r'^\s*class\s+LaneletFormulaID\s*\(\s*enum\.Enum\s*\)\s*:', ln):
            i += 1
            # class: to the next non-indented line (col 0 class/def or EOF)
            while i < n:
                cur = lines[i]
                # break on next top-level class/def/@ or EOF
                if re.match(r'^[^\s#]', cur) or re.match(r'^\s*(class|def|@)\b', cur) and not cur.startswith(" "):
                    break
                # modify only lines like UPPER = "..."
                m = re.match(r'^(\s*)([A-Z0-9_]+)\s*=\s*(".*")\s*,?\s*$', cur)
                if m:
                    # 4 spaces indent uniformly
                    want = "    " + m.group(2) + " = " + m.group(3)
                    if cur != want:
                        out.append(want)
                        changed = True
                    else:
                        out.append(cur)
                else:
                    out.append(cur)
                i += 1
            continue  # the i of the outer loop is already advanced
        i += 1

    if changed:
        p.write_text("\n".join(out) + "\n", encoding="utf-8")
    return changed

def _hoist_vertical_clearance_predicate(p: Path) -> bool:
    """
    If is_vertical_clearance_too_low is mistakenly indented inside another function,
    "de-indent" the entire function block and ensure it's at module top-level (move to file end if needed).
    Return whether the file was modified.
    may not be Used, the program is mostly using 'ops' to apply changes now.
    """
    try:
        txt = p.read_text(encoding="utf-8")
    except Exception:
        return False

    #find the function definition (possibly indented)
    m = re.search(r'(?m)^(?P<indent>[ \t]+)def\s+is_vertical_clearance_too_low\s*\(', txt)
    if not m:
        # if not find the indented version, either already top-level or function not present
        return False

    indent = m.group("indent")
    start = m.start()

    #calculate the function block's end: from the line after definition, until a non-empty line with indent <= indent (or EOF)
    lines = txt.splitlines(keepends=True)

    # replace the start position with line index
    prefix = txt[:start]
    start_line = prefix.count("\n")

    # estimate block end
    end_line = start_line + 1
    while end_line < len(lines):
        ln = lines[end_line]
        # empty line, skip directly
        if re.match(r'^\s*$', ln):
            end_line += 1
            continue
        #if next line's indent is less than or equal to current indent (and not a decorator), break
        if not ln.startswith(indent) and not ln.startswith(indent.replace("\t", " ")):
            break
        end_line += 1

    block = "".join(lines[start_line:end_line])

    #remove one level of indent(indent) from each line in block
    dedented = re.sub(rf'(?m)^{re.escape(indent)}', "", block)

    # remove old block from original text
    before = "".join(lines[:start_line])
    after = "".join(lines[end_line:])

    # goal: append to file end (ensure top-level)
    new_txt = before + after
    if not new_txt.endswith("\n\n"):
        new_txt = new_txt.rstrip() + "\n\n"
    new_txt += dedented.lstrip()  # top-level function definition
    if not new_txt.endswith("\n"):
        new_txt += "\n"

    if new_txt != txt:
        p.write_text(new_txt, encoding="utf-8")
        return True
    return False

def post_apply_fixups() -> None:
    """

    After applying the patch but before syntax check, do two fixes:
      1) Uniformly indent LaneletFormulaID members with 4 spaces;
      2) Hoist is_vertical_clearance_too_low to module top-level if mistakenly indented inside another function.
    If modified, git add the changed file.

    """
    enum_path = CRD_ROOT / FOUR_FILES[0]
    pred_path = CRD_ROOT / FOUR_FILES[3]
    changed = False
    try:
        if enum_path.exists() and _fix_formula_ids_indentation(enum_path):
            run(["git", "add", str(enum_path)], cwd=CRD_ROOT)
            changed = True
    except Exception as e:
        typer.echo(f"    ⚠️  fix LaneletFormulaID indentation failed: {e}")
    try:
        if pred_path.exists() and _hoist_vertical_clearance_predicate(pred_path):
            run(["git", "add", str(pred_path)], cwd=CRD_ROOT)
            changed = True
    except Exception as e:
        typer.echo(f"    ⚠️  fix is_vertical_clearance_too_low scope failed: {e}")
    if changed:
        typer.echo("    ✓ Automatically fix indentation/scope and stage changes")

def _compute_enum_indent(file_rel: str) -> str:
    """
    Not Used anymore, the program is mostly using 'ops' to apply changes now.
    Scan the target file to infer the indentation used for Enum members (default to 4 spaces).
    """
    try:
        txt = (CRD_ROOT / file_rel).read_text(encoding="utf-8")
    except Exception:
        return "    "
    for ln in txt.splitlines():
        m = re.match(r'^(\s+)[A-Z0-9_]+\s*=\s*"', ln)
        if m:
            return m.group(1)
    return "    "

def sanitize_patch_indentation(patch: str) -> str:
    """
    fix the indentation of new lines added by LLM to match the surrounding context.
    1) formula_ids.py: align new Enum members with existing ones;
    2) lanelet_predicates.py: ensure new is_/has_/are_ predicate functions are at module top-level (no indent).
    Only modify lines starting with '+'; do not change context or deletions.
    """
    enum_file = FOUR_FILES[0]  # formula_ids.py
    pred_file = FOUR_FILES[3]  # lanelet_predicates.py
    enum_indent = _compute_enum_indent(enum_file)

    def norm_path(p: str) -> str:
        if p.startswith(("a/", "b/")):
            p = p[2:]
        return Path(p).as_posix()

    out = []
    current = None
    for ln in patch.splitlines():
        if ln.startswith("--- "):
            out.append(ln)
            continue
        if ln.startswith("+++ "):
            current = norm_path(ln[4:].strip())
            out.append(ln)
            continue

        # only handle added lines
        if ln.startswith("+"):
            raw = ln[1:]
            # 1) Enum member alignment
            if current == enum_file:
                m = re.match(r'^(\s*)([A-Z0-9_]+)\s*=\s*"(?:[^"\\]|\\.)*"\s*,?\s*$', raw)
                if m:
                    # Replace current indentation with existing indentation in enum
                    rest = raw[len(m.group(1)):]
                    ln = "+" + enum_indent + rest.lstrip()

            # 2) Predicate function top-level
            if current == pred_file and re.match(r'^\+\s+def\s+(?:is_|has_|are_)[a-z0-9_]*\s*\(', ln, re.I):
                ln = "+" + raw.lstrip()

        out.append(ln)
    s = "\n".join(out)
    if not s.endswith("\n"):
        s += "\n"
    return s

def add_ab_prefixes(patch: str) -> str:
    out = []
    for ln in patch.splitlines():
        if ln.startswith('--- '):
            path = ln[4:].strip()
            if not path.startswith(('a/', 'b/', '/dev/null')):
                ln = f"--- a/{path}"
        elif ln.startswith('+++ '):
            path = ln[4:].strip()
            if not path.startswith(('a/', 'b/', '/dev/null')):
                ln = f"+++ b/{path}"
        out.append(ln)
    s = "\n".join(out)
    if not s.endswith("\n"):
        s += "\n"
    return s

TRUST_DIFF_ONLY_FOR = {
    "crdesigner/verification_repairing/verification/hol/formula_collection.py",
}

PREFER_OPS_FOR = {
    "crdesigner/verification_repairing/verification/formula_ids.py",
    "crdesigner/verification_repairing/verification/groups_handler.py",
    "crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py",
}

def _run(cmd, cwd=None, input_bytes=None, check=False):
    p = subprocess.run(
        cmd, cwd=cwd, input=input_bytes, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    if check and p.returncode != 0:
        raise RuntimeError(f"cmd failed: {' '.join(cmd)}\nSTDOUT:\n{p.stdout.decode()}\nSTDERR:\n{p.stderr.decode()}")
    return p.returncode, p.stdout.decode(), p.stderr.decode()

def normalize_diff_headers(patch: str) -> str:
    """
    Align indented diff headers to the left, remove CR, and unify line endings.
    """

    lines = patch.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    out = []
    for ln in lines:
        raw = ln.lstrip()
        if raw.startswith(("--- ", "+++ ", "@@ ")):
            out.append(raw)
        else:
            out.append(ln)
    return "\n".join(out).strip() + "\n"

def _strip_ab_prefix(path: str) -> str:
    # support 'a/xxx' or 'b/xxx'
    if path.startswith("a/") or path.startswith("b/"):
        return path[2:]
    return path

def split_patch_by_file(patch: str):
    """
    Split a unified diff into per-file chunks, returning [(old_path, new_path, chunk_str), ...].
    """
    patch = normalize_diff_headers(patch)
    lines = patch.splitlines(True)
    i, n = 0, len(lines)
    out = []
    while i < n:
        if lines[i].startswith("--- "):
            # parse old path
            old_path = lines[i].strip().split(" ", 1)[1]
            # the next line must be +++
            if i + 1 >= n or not lines[i + 1].startswith("+++ "):
                # if not paired, skip to next file block (let git apply reject it)
                j = i + 1
                while j < n and not lines[j].startswith("--- "):
                    j += 1
                i = j
                continue
            new_path = lines[i + 1].strip().split(" ", 1)[1]
            norm_new = _strip_ab_prefix(new_path)
            # collect until the next '--- ' (next file)
            j = i + 2
            while j < n and not lines[j].startswith("--- "):
                j += 1
            chunk = "".join(lines[i:j])
            out.append(( _strip_ab_prefix(old_path), norm_new, chunk ))
            i = j
        else:
            i += 1
    return out

def filter_patch_files_keep_only(patch: str, keep_paths: set) -> str:
    """
    Keep only the trusted file chunks, discard others.
    """
    parts = split_patch_by_file(patch)
    kept = []
    for old_path, new_path, chunk in parts:
        path = _strip_ab_prefix(new_path)
        if path in keep_paths:
            kept.append(chunk)
    return "".join(kept)

def git_apply_check(patch: str, repo: Path) -> (bool, str):
    """
    Strictly check if the patch can be applied (no fuzzing).
    """
    # use git apply --check; if fails return False + stderr.
    rc, _out, err = _run(["git", "apply", "--check", "-p0", "--whitespace=nowarn"], cwd=repo, input_bytes=patch.encode())
    return rc == 0, err

def git_apply_strict(patch: str, repo: Path):
    """
    Apply the patch strictly (no fuzz).
    """
    # --index to stage changes, --reject to generate .rej on failure for diagnosis
    _run(["git", "apply", "--index", "-p0", "--reject", "--whitespace=nowarn", "--verbose"],
         cwd=repo, input_bytes=patch.encode(), check=True)

def insert_predicate_module_scope(file_path: Path, func_src: str, anchor_before: str = "def has_stop_line("):
    """
    Insert func_src (a complete function with def at col 0) before the anchor line.
    If a function with the same name already exists (top-level), remove the old one before inserting (idempotent).
    """
    text = file_path.read_text(encoding="utf-8")
    func_src = func_src.replace("\r\n", "\n").replace("\r", "\n").strip("\n") + "\n\n"
    # format the function: def at col 0, body indented by 4 spaces
    # LLM often adds an extra leading space before def
    func_src = re.sub(r"^\s*def\s+", "def ", func_src, count=1, flags=re.M)

    # get function name
    m = re.match(r"def\s+([A-Za-z_]\w*)\s*\(", func_src)
    if not m:
        raise RuntimeError("ensure_predicate: 无法解析函数名")
    fname = m.group(1)

    # remove existing top-level def with the same name (idempotent)
    # use a coarse-grained regex: from 'def name(' to the next 'def ' or end of file
    pattern = re.compile(rf"^def\s+{re.escape(fname)}\s*\(.*?(?=^def\s|\Z)", re.S | re.M)
    text = re.sub(pattern, "", text)

    # find the anchor line; insert before it with a blank line
    idx = text.find(anchor_before)
    if idx == -1:
        # append to file end with two newlines
        text = text.rstrip() + "\n\n" + func_src
    else:
        # find the start of the anchor line
        head = text[:idx]
        tail = text[idx:]
        # ensure head ends with two newlines to avoid merging with previous code
        head = head.rstrip("\n") + "\n\n"
        text = head + func_src + tail

    file_path.write_text(text, encoding="utf-8")

def diff_has_real_changes(patch: str) -> bool:
    """
    At least one real + or - (excluding file headers +++/---).
    """
    for ln in patch.splitlines():
        if ln.startswith('+++ ') or ln.startswith('--- '):
            continue
        if ln.startswith('+') or ln.startswith('-'):
            return True
    return False

def patch_applies_cleanly(patch: str) -> Tuple[bool, str]:
    import tempfile, shutil
    with tempfile.TemporaryDirectory() as td:
        pf = Path(td) / "patch.diff"
        pf.write_text(patch, encoding="utf-8")

        logs = []

        chk = subprocess.run(["git", "apply", "-p1", "--check", str(pf)],
                             cwd=CRD_ROOT, text=True, capture_output=True)
        if chk.returncode == 0:
            return True, ""
        logs.append(f"git apply --check:\n{chk.stderr or chk.stdout}")

        three = subprocess.run(["git", "apply", "-p1", "--3way", "--check", str(pf)],
                               cwd=CRD_ROOT, text=True, capture_output=True)
        if three.returncode == 0:
            return True, ""
        logs.append(f"git apply --3way --check:\n{three.stderr or three.stdout}")

        # ignore whitespace differences(check only, not apply)
        ig1 = subprocess.run(["git", "apply", "-p1", "--ignore-space-change", "--check", str(pf)],
                             cwd=CRD_ROOT, text=True, capture_output=True)
        if ig1.returncode == 0:
            return True, ""
        logs.append(f"git apply --ignore-space-change --check:\n{ig1.stderr or ig1.stdout}")

        ig2 = subprocess.run(["git", "apply", "-p1", "--ignore-whitespace", "--check", str(pf)],
                             cwd=CRD_ROOT, text=True, capture_output=True)
        if ig2.returncode == 0:
            return True, ""
        logs.append(f"git apply --ignore-whitespace --check:\n{ig2.stderr or ig2.stdout}")

        if shutil.which("patch"):
            dry = subprocess.run(["patch", "-p1", "--dry-run", "-i", str(pf)],
                                 cwd=CRD_ROOT, text=True, capture_output=True)
            if dry.returncode == 0:
                return True, ""
            logs.append(f"patch --dry-run:\n{dry.stderr or dry.stdout}")

            # again ignore whitespace differences
            dry_l = subprocess.run(["patch", "-p1", "-l", "--dry-run", "-i", str(pf)],
                                   cwd=CRD_ROOT, text=True, capture_output=True)
            if dry_l.returncode == 0:
                return True, ""
            logs.append(f"patch -l --dry-run:\n{dry_l.stderr or dry_l.stdout}")
        else:
            logs.append("patch command not found")

        return False, "\n\n".join(logs)

def forbid_numeric_kwargs_in_formula_collection(patch: str):
    """
    if any added line in formula_collection.py contains Is_*(...) with '=', raise an error.
    """
    added = _diff_added_lines_for_file(patch, FOUR_FILES[2])
    pattern = re.compile(r'Is_[A-Za-z0-9_]+\([^)]*=[^)]*\)')  # if there is an '=', it means explicit kwargs are passed.
    bad = [ln for ln in added if pattern.search(ln)]
    if bad:
        example = "\n".join(bad[:3])
        raise RuntimeError(
            "Detected passing explicit numeric kwargs to formula string in formula_collection.py (not allowed).\n"
            "Please call only the predicate name, the threshold is defined by the predicate default parameters.\n"
            f"Example:\n{example}"
        )

def extract_ops_from_response(full_text: str) -> list[dict]:
    """
    Ops parse
    """
    blocks = re.findall(r"```yaml\s*(.*?)\s*```", full_text, re.S | re.I)
    yaml = ry.YAML(typ="safe")
    for blk in blocks:
        try:
            data = yaml.load(blk)
        except Exception:
            continue
        if isinstance(data, dict) and isinstance(data.get("ops"), list):
            return data["ops"]
    return []

def _read_lines(relpath: str) -> list[str]:
    """
    text/AST tool
    """
    p = CRD_ROOT / relpath
    return p.read_text(encoding="utf-8").splitlines(keepends=False)

def _write_lines(relpath: str, lines: list[str]) -> None:
    p = CRD_ROOT / relpath
    p.write_text("\n".join(lines) + "\n", encoding="utf-8")

def _ensure_newline_eof(relpath: str) -> None:
    p = CRD_ROOT / relpath
    s = p.read_text(encoding="utf-8")
    if not s.endswith("\n"):
        p.write_text(s + "\n", encoding="utf-8")

def op_add_enum_member(file: str, enum_class: str, name: str, value: str) -> bool:
    """
    In the specified file, within the class <enum_class>(enum.Enum):, append `    NAME = "value"`.
    If it already exists, do nothing. Returns whether a change was made.
    """
    lines = _read_lines(file)
    # locate class
    start = None
    for i, ln in enumerate(lines):
        if re.match(rf'^\s*class\s+{re.escape(enum_class)}\s*\(\s*enum\.Enum\s*\)\s*:', ln):
            start = i
            break
    if start is None:
        return False
    # find class body range (until next top-level block)
    end = start + 1
    while end < len(lines):
        ln = lines[end]
        if re.match(r'^[^\s#]', ln):  # new top-level statement
            break
        end += 1
    pat = re.compile(rf'^\s*{re.escape(name)}\s*=\s*["\']{re.escape(value)}["\']\s*,?\s*$')
    for i in range(start + 1, end):
        if pat.match(lines[i]):
            return False
    # find the last existing member and insert after it
    insert_at = end
    for i in range(end - 1, start, -1):
        if re.match(r'^\s*[A-Z0-9_]+\s*=\s*["\']', lines[i]):
            insert_at = i + 1
            break
    lines.insert(insert_at, f'    {name} = "{value}"')
    _write_lines(file, lines)
    return True

def op_add_to_group(relpath: str, insert_near_anchor: str, add: str) -> bool:
    """
    In groups_handler.py, append the enum `add` to the formulas list containing `insert_near_anchor`.
    If the anchor is not found, do a two-level fallback (priority 2 group containing STOP_LINE_REFERENCES; if not, the first formulas list).
    Idempotent: if already exists, do not add again.
    """
    p = CRD_ROOT / relpath
    s = p.read_text(encoding="utf-8")

    if add in s:
        # may already be in some group; do not add again
        return False

    # lightweight parsing: grab all formulas=[ ... ] blocks and their start/end positions
    blocks = []
    i = 0
    while True:
        i = s.find("formulas", i)
        if i < 0: break
        j = s.find("[", i)
        if j < 0: break
        # match brackets
        bal = 0; end = None
        for k in range(j, len(s)):
            c = s[k]
            if c == "[": bal += 1
            elif c == "]":
                bal -= 1
                if bal == 0:
                    end = k
                    break
        if end is None: break
        blocks.append((i, j, end))
        i = end + 1

    def block_text(sp): return s[sp[1]:sp[2]+1]

    # find the block with the anchor
    target = None
    for sp in blocks:
        if insert_near_anchor in block_text(sp):
            target = sp; break

    # Second fallback: priority=2 and contains STOP_LINE_REFERENCES
    if target is None:
        for sp in blocks:
            bt = block_text(sp)
            # look back at which SpecificationGroup this formulas belongs to (simple lookahead 200 characters)
            head = s[max(0, sp[0]-200):sp[0]]
            if "priority=2" in head and "LaneletFormulaID.STOP_LINE_REFERENCES" in bt:
                target = sp; break

    # fallback to the first formulas list containing LaneletFormulaID.
    if target is None and blocks:
        for sp in blocks:
            if "LaneletFormulaID." in block_text(sp):
                target = sp; break

    if target is None:
        raise RuntimeError("No insertable formulas found")

    bt = block_text(target)
    # Idempotent check: if already exists, do not add
    if add in bt:
        return False

    # Insert before ']', automatically add comma
    inner = bt[1:-1]
    need_comma = inner.strip() and not inner.rstrip().endswith(",")
    sep = ",\n" if need_comma else "\n"

    # Indentation: find the indentation of the last line
    indent_m = re.search(r"\n([ \t]+)\]", bt)
    indent = indent_m.group(1) if indent_m else " " * 20
    ins = f"{sep}{indent}{add}\n"

    new_bt = bt[:-1] + ins + "]"
    new_s = s[:target[1]] + new_bt + s[target[2]+1:]
    p.write_text(new_s, encoding="utf-8")
    _ensure_newline_eof(relpath)
    return True


def op_upsert_formula_mapping(relpath: str, key: str, value: str) -> bool:
    """
    mapping upsert only in LaneletFormulas.formulas:
        "key": "<value-as-string>"
    Rules:
      - If the same key exists in GeneralFormulas, remove it first.
      - The final value is forced to be a **string** (if LLM gives an unquoted expression, it will be automatically quoted).
      - Insert at the **end** of LaneletFormulas.formulas, preserving dictionary style and indentation.
    """
    import re
    p = CRD_ROOT / relpath
    text = p.read_text(encoding="utf-8")

    # ---- helpers -----------------------------------------------------------
    def _ensure_quoted(v: str) -> str:
        """
        Ensure that the value is a string literal. If it is not quoted, double quotes will be added.
        """
        v = v.strip()
        if len(v) >= 2 and ((v[0] == v[-1] == '"') or (v[0] == v[-1] == "'")):
            return v
        return f'"{v}"'

    def find_map_block(s: str, class_name: str):
        """
        Find the outermost {...} block of formulas in class <class_name>: ... formulas ... { ... }.
        Return (pos_formulas, pos_lbrace, pos_rbrace)
        """
        i = s.find(f"class {class_name}:")
        if i < 0:
            return None
        j = s.find("formulas", i)
        if j < 0:
            return None
        k = s.find("{", j)
        if k < 0:
            return None
        bal = 0
        end = None
        for t in range(k, len(s)):
            c = s[t]
            if c == "{":
                bal += 1
            elif c == "}":
                bal -= 1
                if bal == 0:
                    end = t
                    break
        if end is None:
            return None
        return (j, k, end)

    def get_block(s: str, span):
        j, k, e = span
        return s[k:e + 1]

    def remove_key(block: str, the_key: str):
        """
        Delete the entire line with the specified key from the dictionary block (value may be quoted or unquoted).
        Allow optional trailing comma, and clean up any dangling ', }' afterwards.
        """
        # pair one line: "key": <any non-newline content> [optional comma] [newline]
        pat = r'(?m)^[ \t]*["\']%s["\'][ \t]*:[ \t]*[^\n]*\n?' % re.escape(the_key)
        nb, cnt = re.subn(pat, "", block)
        if cnt:
            # Let ", }" → " }"
            nb = re.sub(r",\s*([}\n])", r"\1", nb)
        return nb, cnt > 0

    def insert_pair(block: str, the_key: str, the_val: str):
        """
        Insert a line `"key": value,` before the closing '}' of the dictionary block,
        """
        inner = block[1:-1]
        need_comma = inner.strip() and not inner.rstrip().endswith(",")
        sep = ",\n" if need_comma else "\n"
        # get indentation (look for the first entry); if not found, use 8 spaces
        m = re.search(r"\n([ \t]+)[\"']", block)
        indent = (m.group(1) if m else "        ")
        line = f'{indent}"{the_key}": {the_val},\n'
        return block[:-1] + sep + line + "}"

    # remove existing key from GeneralFormulas if any
    changed = False
    g_span = find_map_block(text, "GeneralFormulas")
    if g_span:
        g_block = get_block(text, g_span)
        nb, removed = remove_key(g_block, key)
        if removed:
            text = text[:g_span[1]] + nb + text[g_span[2] + 1:]
            changed = True

    # upsert to LaneletFormulas.formulas
    l_span = find_map_block(text, "LaneletFormulas")
    if not l_span:
        raise RuntimeError("LaneletFormulas.formulas not found")
    l_block = get_block(text, l_span)

    # let value be a string literal
    value_quoted = _ensure_quoted(value)

    # replace if exists (old value may be quoted or not)
    # Capture: indentation, colon and whitespace, old value (to end of line), trailing comma/whitespace/newline
    pat_line = (
        r'(?m)^'                               # start of line
        r'([ \t]*)'                            # 1: indent
        r'["\']%s["\']'                        #    "key"
        r'([ \t]*:[ \t]*)'                     # 2: colon and whitespace
        r'([^\n]*?)'                           # 3: old value (to end of line, may be unquoted)
        r'([ \t]*,?[ \t]*\n?)'                 # 4: trailing comma/whitespace/newline
    ) % re.escape(key)

    if re.search(pat_line, l_block):
        def _repl(m):
            indent, colon, _old, tail = m.group(1), m.group(2), m.group(3), m.group(4)
            # Force comma and newline (consistent with insert style)
            newline = "" if tail.endswith("\n") else "\n"
            return f'{indent}"{key}"{colon}{value_quoted},{newline}'
        new_l_block, nsub = re.subn(pat_line, _repl, l_block)
        if nsub and new_l_block != l_block:
            text = text[:l_span[1]] + new_l_block + text[l_span[2] + 1:]
            changed = True
    else:
        # If not exists, insert at the end of LaneletFormulas
        new_l_block = insert_pair(l_block, key, value_quoted)
        text = text[:l_span[1]] + new_l_block + text[l_span[2] + 1:]
        changed = True

    if changed:
        p.write_text(text, encoding="utf-8")
        _ensure_newline_eof(relpath)
    return changed


def _normalize_top_level_function(snippet: str) -> str:
    """
    Normalize any def snippet to: def at col 0; function body non-empty and minimum indent 4 spaces.
    """
    import textwrap, ast
    s = textwrap.dedent(snippet).strip("\n") + "\n"
    # def at col 0
    s = re.sub(r'(?m)^\s*(def\s+)', r'\1', s)
    lines = s.splitlines()
    if not lines:
        raise ValueError("empty function snippet")
    # If only the def line is present, add pass
    if len(lines) == 1 or all(not ln.strip() for ln in lines[1:]):
        s = lines[0] + "\n    pass\n"
    else:
        # calculate the minimum leading whitespace in the body lines
        body = lines[1:]
        min_ws = None
        for ln in body:
            if not ln.strip(): continue
            leading = len(re.match(r'^([ \t]*)', ln).group(1).expandtabs(4))
            min_ws = leading if min_ws is None else min(min_ws, leading)
        if min_ws == 0:
            # add 4 spaces to all non-empty body lines
            for i in range(1, len(lines)):
                if lines[i].strip():
                    lines[i] = "    " + lines[i]
            s = "\n".join(lines) + "\n"
    # make sure ast can parse it
    try:
        ast.parse(s)
    except Exception as e:
        raise ValueError(f"function snippet is not valid Python after normalization: {e}")
    return s

def op_ensure_predicate(file: str, name: str, code: str) -> bool:
    """
    Ensure that the predicates module contains the top-level def <name>(...):
    - If the top-level definition already exists, do nothing;
    - Otherwise, append the normalized `code` to the end of the file.
    Return whether a change was made.
    """
    p = CRD_ROOT / file
    txt = p.read_text(encoding="utf-8")
    if re.search(rf'(?m)^def\s+{re.escape(name)}\s*\(', txt):
        return False
    # delete any mistakenly indented version of the function
    txt = re.sub(rf'(?ms)^[ \t]+def\s+{re.escape(name)}\s*\(.*?\n(?:[ \t].*?\n)*', '', txt)
    norm = _normalize_top_level_function(code)
    if not txt.endswith("\n\n"):
        txt = txt.rstrip() + "\n\n"
    txt += norm
    p.write_text(txt, encoding="utf-8")
    return True

def apply_ops(ops: list[dict]) -> bool:
    """
    Apply a list of operations as specified by LLM. Return whether any changes were made.
    Supported op types:
        - add_enum_member{file, enum_class, name, value}
        - add_to_group{file, insert_near_anchor, add}
        - upsert_formula_mapping{file, key, value}
        - ensure_predicate{file, name, code}
    """
    changed = False
    for op in ops or []:
        t = op.get("type")
        if t == "add_enum_member":
            changed |= op_add_enum_member(op["file"], op["enum_class"], op["name"], op["value"])
        elif t == "add_to_group":
            changed |= op_add_to_group(op["file"], op["insert_near_anchor"], op["add"])
        elif t == "upsert_formula_mapping":
            changed |= op_upsert_formula_mapping(op["file"], op["key"], op["value"])
        elif t == "ensure_predicate":
            changed |= op_ensure_predicate(op["file"], op["name"], op["code"])
        else:
            raise RuntimeError(f"Unsupported op type: {t}")
    # make sure newline at EOF for all four files
    for rel in FOUR_FILES:
        p = CRD_ROOT / rel
        if p.exists():
            _ensure_newline_eof(rel)
    return changed
def extract_yaml_ops_and_patch_loose(text: str) -> tuple[str, str, list]:
    """
    Loosely parse the first YAML block containing antlr_patch/python_patch/ops:
    - return (yaml_block_text, python_patch_str, ops_list)
    - even if python_patch is not a strict unified diff, return the raw string for later fixing/downgrade to ops.
    """
    import re
    yaml = ry.YAML(typ="safe")

    blocks = re.findall(r"```yaml\s*(.*?)\s*```", text, re.S | re.I)
    chosen_raw = None
    chosen_obj = None
    for blk in blocks:
        try:
            data = yaml.load(blk)
        except Exception:
            continue
        if isinstance(data, dict) and any(k in data for k in ("antlr_patch", "python_patch", "ops")):
            chosen_raw = blk
            chosen_obj = data
            break
    if chosen_raw is None or chosen_obj is None:
        # degradation: tolerate no fenced block (rare)
        m = re.search(r"^\s*antlr_patch\s*:\s*", text, re.M)
        if m:
            # from this line to the next ``` or end of text
            end = re.search(r"^```", text[m.start():], re.M)
            chunk = text[m.start():(m.start() + (end.start() if end else len(text)))]
            try:
                chosen_obj = yaml.load(chunk)
                chosen_raw = chunk
            except Exception:
                pass

    if not isinstance(chosen_obj, dict):
        raise RuntimeError("the YAML with antlr_patch/python_patch/ops not found or invalid")

    py_patch = chosen_obj.get("python_patch") or ""
    ops = chosen_obj.get("ops") or []
    if not isinstance(ops, list):
        ops = []
    return chosen_raw, str(py_patch), ops


def repair_missing_new_headers(patch: str) -> str:
    """
    If a '--- path' line is found without a following '+++ path', insert a '+++ path' line.
    Do minimal fix, do not add a/ b/ prefixes (handled later by add_ab_prefixes). 
    just prevent the LLM output that. sometimes
    """
    lines = patch.replace("\r\n", "\n").split("\n")
    out = []
    i, n = 0, len(lines)
    while i < n:
        ln = lines[i]
        out.append(ln)
        if ln.startswith("--- "):
            next_ln = lines[i + 1] if (i + 1) < n else ""
            if not next_ln.startswith("+++ "):
                path = ln[4:].strip()
                # if path is empty, still add (later normalize_patch will clean it)
                out.append(f"+++ {path}")
        i += 1
    s = "\n".join(out)
    if not s.endswith("\n"):
        s += "\n"
    return s

    
def current_branch() -> str:
    return run(["git", "rev-parse", "--abbrev-ref", "HEAD"], cwd=CRD_ROOT).stdout.strip()

def run_smoke(scenario_xml: str | None = None) -> Tuple[bool, str]:
    """
    Run a quick smoke test using CRD's verification script logic.
    - Prefer the scenario_xml argument;
    - Otherwise use the CRD_SCENARIO_XML environment variable;
    - If both are missing, use the example path in the repository.
    Return: (success, tail of stdout+stderr logs)
    """
    # can change the default back to absolute path; here it's safer to use a relative path in the repository
    default_xml = str(Path(os.environ.get("CRD_ROOT", ".")).resolve()
                      / "example_files/opendrive/opendrive-1.xml")
    scenario_xml = scenario_xml or os.environ.get("CRD_SCENARIO_XML", default_xml)

    # Run the verification script logic directly in a subprocess to avoid polluting the current interpreter environment.
    code = f"""
import os, logging, sys
logging.basicConfig(level=logging.INFO)
from crdesigner.common.file_reader import CRDesignerFileReader
from crdesigner.verification_repairing.map_verification_repairing import verify_and_repair_map
from crdesigner.verification_repairing.config import MapVerParams
from crdesigner.verification_repairing.verification.hol.formula_manager import FormulaManager

file = r"{scenario_xml}"
print("[SMOKE] reading:", file)
scenario, _ = CRDesignerFileReader(file).open()
fm = FormulaManager()
cfg = MapVerParams()
cfg.verification.formula_manager = fm

net, result = verify_and_repair_map(
    scenario.lanelet_network,
    scenario_id=scenario.scenario_id,
    config=cfg
)
print("[SMOKE] verification finished. Result summary:", result)
"""

    try:
        p = subprocess.run(
            [sys.executable, "-c", code],
            cwd=Path(os.environ.get("CRD_ROOT", ".")).resolve(),
            text=True,
            capture_output=True,
            check=False,
        )
        ok = (p.returncode == 0)

        tail = ((p.stdout or "") + "\n" + (p.stderr or ""))[-8000:]
        return ok, tail
    except Exception as e:
        return False, f"[SMOKE] Exception: {e}"
    
def _check_python_syntax(paths: list[Path]) -> None:
    import py_compile
    for p in paths:
        try:
            py_compile.compile(str(p), doraise=True)
        except Exception as e:
            raise RuntimeError(f"Python syntax error: {p}\n{e}")
        
def apply_ops_with_watchdog(ops: list[dict], per_op_timeout_s: int = 20) -> bool:
    """
    Execute ops one by one; set a timeout for each. If the watchdog triggers, skip that op and continue.
    Print clear begin/done/error/timeout logs (flush in real time).
    """
    import signal, traceback, sys, time

    class _Timeout(Exception):
        pass

    def _handle_timeout(signum, frame):
        raise _Timeout()

    # Only effective on *nix; will raise an exception on Windows, so here needs a safeguard.
    try:
        signal.signal(signal.SIGALRM, _handle_timeout)
        use_alarm = True
    except Exception:
        use_alarm = False

    total = len(ops or [])
    changed_any = False

    for i, op in enumerate(ops or [], 1):
        op_type = op.get("type")
        op_file = op.get("file")
        print(f"[ops {i}/{total}] BEGIN {op_type} → {op_file}", flush=True)

        if use_alarm:
            signal.alarm(per_op_timeout_s)
        t0 = time.time()
        try:
            # Reuse existing apply_ops, feeding only a single op to ensure idempotency.
            changed_any |= apply_ops([op])
            dt = time.time() - t0
            print(f"[ops {i}/{total}] DONE in {dt:.2f}s", flush=True)
        except _Timeout:
            print(f"[ops {i}/{total}] TIMEOUT after {per_op_timeout_s}s → skipped", flush=True)
        except Exception as e:
            print(f"[ops {i}/{total}] ERROR: {e}", flush=True)
            traceback.print_exc()
        finally:
            if use_alarm:
                signal.alarm(0)

    return changed_any

        
@APP.command()
def add(
    rule: List[str] = typer.Argument(..., help="Natural language rules, support for multiple paragraphs"),
    dry: bool = False,
    xml: str = typer.Option(None, help="Path to the scenario XML for verification, overrides CRD_SCENARIO_XML"),
    no_rag: bool = typer.Option(not RAG_ENABLED, help="Disable read-only code RAG context"),
    rag_dir: List[str] = typer.Option(None, help="Additional read-only directories to scan, relative to CRD_ROOT, can be passed multiple times"),
    model: str = typer.Option(None, help="Override OPENAI_MODEL, e.g. gpt-4o-mini"),
    timeout: float = typer.Option(None, help="Override request timeout (seconds)"),
    diff_only: bool = typer.Option(True, help="Only return YAML+diff, not full file (save tokens)"),
):
    """
    More robust landing process:
    - Only trust the diff of formula_collection.py (strict git apply, no fuzz allowed);
    - The other three files all use ops semantics to land;
    - If the diff cannot be applied strictly, give up the diff and switch to ops;
    - After executing ops, do a "predicate top-level wrapping" to avoid def being inserted into the function body;
    - Finally, unify syntax checking and smoke.
    """
    import re
    import subprocess
    import datetime
    import hashlib
    from pathlib import Path


    TRUST_DIFF_ONLY_FOR = {
        "crdesigner/verification_repairing/verification/hol/formula_collection.py",
    }

    def _strip_ab_prefix(path: str) -> str:
        # 兼容 a/xxx 或 b/xxx
        return path[2:] if path.startswith("a/") or path.startswith("b/") else path

    def _normalize_diff_headers(patch: str) -> str:
        """
        Normalize the ---/+++/@@ header lines to be left-aligned; unify line endings; remove CR.
        """
        if not patch:
            return ""
        lines = patch.replace("\r\n", "\n").replace("\r", "\n").split("\n")
        out = []
        for ln in lines:
            raw = ln.lstrip()
            if raw.startswith(("--- ", "+++ ", "@@ ")):
                out.append(raw)
            else:
                out.append(ln)
        return "\n".join(out).strip() + "\n"

    def _split_patch_by_file(patch: str):
        """
        Split a unified diff by file, return a list of (old_path, new_path, chunk).
        """
        patch = _normalize_diff_headers(patch)
        lines = patch.splitlines(True)
        i, n = 0, len(lines)
        out = []
        while i < n:
            if lines[i].startswith("--- "):
                old_path = lines[i].strip().split(" ", 1)[1]
                if i + 1 >= n or not lines[i + 1].startswith("+++ "):
                    j = i + 1
                    while j < n and not lines[j].startswith("--- "):
                        j += 1
                    i = j
                    continue
                new_path = lines[i + 1].strip().split(" ", 1)[1]
                j = i + 2
                while j < n and not lines[j].startswith("--- "):
                    j += 1
                out.append((_strip_ab_prefix(old_path), _strip_ab_prefix(new_path), "".join(lines[i:j])))
                i = j
            else:
                i += 1
        return out

    def _filter_patch_files_keep_only(patch: str, keep_paths: set) -> str:
        """
        Keep only the diff chunks for the specified files.
        """
        parts = _split_patch_by_file(patch)
        kept = []
        for _old, newp, chunk in parts:
            if newp in keep_paths:
                kept.append(chunk)
        return "".join(kept)

    def _git_apply_check_strict(patch_text: str) -> tuple[bool, str]:
        """
        Strictly check if the patch can be applied (git apply --check -p1).
        """
        p = subprocess.run(
            ["git", "apply", "--check", "-p1", "--whitespace=nowarn"],
            cwd=CRD_ROOT,
            input=patch_text.encode("utf-8"),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        return (p.returncode == 0, p.stderr.decode("utf-8"))

    def _git_apply_strict(patch_text: str):
        """
        apply the patch strictly (no fuzz).
        """
        p = subprocess.run(
            ["git", "apply", "--index", "-p1", "--whitespace=nowarn", "--verbose"],
            cwd=CRD_ROOT,
            input=patch_text.encode("utf-8"),
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if p.returncode != 0:
            raise RuntimeError(f"git apply failed:\nSTDOUT:\n{p.stdout.decode()}\nSTDERR:\n{p.stderr.decode()}")

    def _robust_insert_predicate_top_level(file_path: Path, func_src: str, anchor_before: str = "def has_stop_line("):
        """
        Ensure that the def starts at column 0 and the function body is indented with 4 spaces.
        If a top-level def with the same name already exists, remove it first.

        """
        text = file_path.read_text(encoding="utf-8")
        func_src = func_src.replace("\r\n", "\n").replace("\r", "\n").strip("\n") + "\n\n"
        # def must be at col 0
        func_src = re.sub(r"^\s*def\s+", "def ", func_src, count=1, flags=re.M)
        m = re.match(r"def\s+([A-Za-z_]\w*)\s*\(", func_src)
        if not m:
            raise RuntimeError("ensure_predicate: Unable to resolve function name")
        fname = m.group(1)
        # Remove the old top-level def with the same name
        pattern = re.compile(rf"^def\s+{re.escape(fname)}\s*\(.*?(?=^def\s|\Z)", re.S | re.M)
        text = re.sub(pattern, "", text)
        # Find the anchor point: insert before has_stop_line; if not, insert at the end of the file
        idx = text.find(anchor_before)
        if idx == -1:
            text = text.rstrip() + "\n\n" + func_src
        else:
            head, tail = text[:idx], text[idx:]
            head = head.rstrip("\n") + "\n\n"
            text = head + func_src + tail
        file_path.write_text(text, encoding="utf-8")



    # Override global config (only for this process)
    if model:
        globals()['OPENAI_MODEL'] = model
    if timeout:
        globals()['_OPENAI_REQ_TIMEOUT'] = float(timeout)

    if not OPENAI_API_KEY:
        typer.echo("Please set the OPENAI_API_KEY environment variable first."); raise typer.Exit(1)

    base_branch = current_branch()
    slug_src = "||".join(rule) + str(datetime.datetime.now())
    slug = hashlib.sha1(slug_src.encode()).hexdigest()[:10]
    tmp_branch = f"llm-rules/{slug}"

    # basic checks
    run(["git", "rev-parse", "--is-inside-work-tree"], cwd=CRD_ROOT)
    git_clean_tree_or_die()

    # get context
    code_ctx = collect_file_slices(FOUR_FILES)
    if no_rag or not RAG_ENABLED:
        ro_ctx = ""
    else:
        dirs = RAG_DIRS.copy()
        if rag_dir:
            dirs.extend(rag_dir)
        ro_ctx = collect_read_only_context(dirs=dirs, globs=RAG_GLOBS, max_chars=RAG_MAX_CHARS)

    prompt = build_prompt("\n\n".join(rule), code_ctx, ro_ctx, diff_only=diff_only)
    typer.echo(f">>> Context sizes — code: {len(code_ctx)} chars, RAG: {len(ro_ctx)} chars")

    # preflight + call LLM
    typer.echo(">>> OpenAI preflight ...")
    preflight_openai()
    typer.echo(">>> Calling LLM to generate patch ...")
    full_response = call_llm_with_retry(prompt, retries=1, diff_only=diff_only)
    save_artifacts(prompt, full_response, yml="", patch="", code_ctx=code_ctx, rag_ctx=ro_ctx)

    # parse YAML/patch/ops (strict → loose)
    ops = []
    try:
        yml, patch = extract_yaml_and_patch(full_response)  # require valid unified diff
        try:
            ops = extract_ops_from_response(full_response)
        except Exception:
            ops = []
    except Exception:
        yml, patch, ops = extract_yaml_ops_and_patch_loose(full_response)
        if patch and ("--- " in patch) and ("+++ " not in patch):
            patch = repair_missing_new_headers(patch)

    save_artifacts(prompt, full_response, yml or "", patch or "", code_ctx=code_ctx, rag_ctx=ro_ctx)


    norm_patch = ""
    trusted_patch = ""
    apply_strategy = "ops"  # default to ops only, more safety

    if patch and patch.strip():
        # Normalize + keep only formula_collection.py blocks
        try:
            pp = normalize_patch(patch)
            pp = add_ab_prefixes(pp)
            pp = fix_unified_diff(pp)
            ensure_patch_only_four_files(pp)
            # filter to keep only formula_collection.py
            trusted_patch = _filter_patch_files_keep_only(pp, TRUST_DIFF_ONLY_FOR)
        except Exception as e:
            typer.echo(f">>> Patch normalization failed, abandoning diff:{e}")
            trusted_patch = ""

    # try strict git apply
    if trusted_patch.strip():
        ok, err = _git_apply_check_strict(trusted_patch)
        if ok:
            apply_strategy = "diff+ops"  # formula_collection uses diff, others use ops
            norm_patch = trusted_patch
        else:
            typer.echo(">>> Patch application failed, reason:")
            typer.echo(err)
            apply_strategy = "ops"
    else:
        apply_strategy = "ops"

    # Show response and the strategy to be applied
    artifacts_dir = Path(CRD_ROOT) / ".llm_artifacts"
    latest_artifact = max(artifacts_dir.glob("*"), key=lambda p: p.stat().st_mtime) if artifacts_dir.exists() else None

    typer.echo("\n" + "="*80)
    typer.echo(">>> LLM has generated patches")
    typer.echo("="*80)
    if latest_artifact:
        typer.echo(f"\n📁 Generated files path: {latest_artifact}")
        typer.echo(f"   - prompt.txt / response.txt / patch.diff / code_context.txt")
        if ro_ctx:
            typer.echo(f"   - read_only_api.txt: RAG context")

    typer.echo("\n" + "-"*80)
    typer.echo(">>> LLM full response (first 2000 characters):")
    typer.echo("-"*80)
    print(full_response[:2000])
    if len(full_response) > 2000:
        typer.echo(f"\n... (left {len(full_response) - 2000} characters, full content see response.txt)")

    typer.echo("\n" + "-"*80)
    if apply_strategy.startswith("diff"):
        typer.echo(">>> will apply 'strict diff for formula_collection.py + ops for other files' strategy, normalized diff is as follows:")
        typer.echo("-"*80)
        print(norm_patch)
    else:
        typer.echo(">>> will apply ops strategy (semantic operations are as follows):")
        typer.echo("-"*80)
        import pprint
        pprint.pprint(ops, width=120)
    typer.echo("-"*80)

    # Dry-run: only show without applying
    if dry:
        save_artifacts(prompt, full_response, yml or "", (norm_patch if apply_strategy.startswith("diff") else ""), code_ctx=code_ctx, rag_ctx=ro_ctx)
        typer.echo(">>> [DRY-RUN] show the following content without modifying the repository.")
        raise typer.Exit()

    # Interactive confirmation
    typer.echo("\n⚠️  Do you want to apply this change to the Git repository?")
    typer.echo(f"   A new branch will be created: {tmp_branch}")
    while True:
        resp = input("Please enter (yes/y/Enter to apply, no/n to cancel): ").strip().lower()
        if resp in ("yes", "y", ""):
            typer.echo("\n✅ User confirmed, start applying changes...")
            break
        elif resp in ("no", "n"):
            typer.echo("\n❌ User canceled, not applying changes.")
            if latest_artifact:
                typer.echo(f"💾 Generated files have been saved to: {latest_artifact}")
            raise typer.Exit(0)
        else:
            typer.echo("⚠️  Invalid input, please enter yes/y/Enter or no/n")

    # Create branch and actually apply changes
    run(["git", "checkout", "-b", tmp_branch], cwd=CRD_ROOT)
    try:
        # 1) First apply strict diff for formula_collection (if this strategy is chosen)
        if apply_strategy.startswith("diff") and norm_patch.strip():
            typer.echo(">>> Applying strict diff for formula_collection.py ...")
            _git_apply_strict(norm_patch)

        # 2) Then apply ops (the other three files must use ops; the upsert for formula_collection should also be idempotent)
        if ops:
            typer.echo(">>> Applying ops semantics (other files & idempotent updates) ...")
            changed = apply_ops_with_watchdog(ops, per_op_timeout_s=20)
            if not changed and not apply_strategy.startswith("diff"):
                raise RuntimeError("ops did not cause any changes (and no diff to apply).")
        else:
            # For robustness, if there are no ops, we cannot rely solely on diff (to prevent error localization)
            if not apply_strategy.startswith("diff"):
                raise RuntimeError("LLM did not provide ops; aborting for robustness.")

        # 3) Normalizing formula strings
        typer.echo(">>> Normalizing formula strings in formula_collection.py ...")
        formula_collection_path = CRD_ROOT / FOUR_FILES[2]
        if formula_collection_path.exists():
            try:
                normalized = normalize_formula_and_subformula_strings(formula_collection_path)
                if normalized:
                    typer.echo("    ✓ Formula strings have been normalized")
                    run(["git", "add", str(formula_collection_path)], cwd=CRD_ROOT)
                else:
                    typer.echo("    - Formula strings do not need normalization")
            except Exception as e:
                typer.echo(f"    ⚠️  Normalization failed: {e} (continuing)")

        # 4) Predicate top-level insertion fallback (read ensure_predicate code from ops and force insert at top level)
        try:
            pred_ops = [o for o in ops if o.get("type") == "ensure_predicate" and o.get("file", "").endswith("lanelet_predicates.py")]
            for po in pred_ops:
                code_snippet = po.get("code", "")
                if code_snippet.strip():
                    _robust_insert_predicate_top_level(CRD_ROOT / FOUR_FILES[3], code_snippet)
                    run(["git", "add", str(CRD_ROOT / FOUR_FILES[3])], cwd=CRD_ROOT)
        except Exception as e:
            typer.echo(f"    ⚠️  Predicate top-level insertion fallback failed (will rely on subsequent syntax checks): {e}")

        # 5) Automatic remediation (your original indentation/scope fixes)
        typer.echo(">>> Fixing LaneletFormulaID indentation and predicate scope ...")
        post_apply_fixups()

        # 6) Syntax check and commit
        _check_python_syntax([CRD_ROOT / f for f in FOUR_FILES])
        run(["git", "commit", "-am", f"Add rules via LLM: {rule}"], cwd=CRD_ROOT)

        # 7) Smoke
        typer.echo(">>> Running smoke test ...")
        ok, logtail = run_smoke(xml)
        save_artifacts(prompt, full_response, yml or "", (norm_patch if apply_strategy.startswith("diff") else ""), smoke_log=logtail, code_ctx=code_ctx, rag_ctx=ro_ctx)
        typer.echo(logtail)
        if not ok:
            typer.echo("Build/validation failed, rolling back patch and cleaning up branch.")
            run(["git", "reset", "--hard", "HEAD~1"], cwd=CRD_ROOT)
            run(["git", "checkout", base_branch], cwd=CRD_ROOT)
            run(["git", "branch", "-D", tmp_branch], cwd=CRD_ROOT)
            raise typer.Exit(2)
    except Exception:
        # Any exception: return to the original branch and delete the temporary branch
        run(["git", "checkout", base_branch], cwd=CRD_ROOT, check=False)
        run(["git", "branch", "-D", tmp_branch], cwd=CRD_ROOT, check=False)
        raise

    typer.echo(f">>> RAG context size: {len(ro_ctx)} chars; code ctx size: {len(code_ctx)} chars")
    typer.echo("Done ✅")



if __name__ == "__main__":
    APP()
