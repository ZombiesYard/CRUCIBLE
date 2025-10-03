
# CRUCIBLE — CommonRoad Unified Code & Invariant Builder with LLM Engines — README (Quickstart for New Users)

This repository accompanies the paper “LLM-Assisted Tool for Joint Generation of Formulas and Functions in Rule-Based Verification of Map Transformations.” 

**Goal:** this document helps people who has never touched this repository run the LLM-based 3-D rule generator(CRUCIBLE） and the included smoke test, even if their folder layout differs from yours.

> TL;DR: You must first **clone and install the official CommonRoad Scenario Designer (CRD)** as per their [GitHub](https://github.com/CommonRoad/commonroad-scenario-designer) instructions. Without CRD installed correctly, the smoke test cannot run — you will only see generated files (prompts, diffs) under `.llm_artifacts/`.

---

## 1) What this tool does

This project adds an **LLM-driven 3-D rule generator** to [CommonRoad Scenario Designer](https://github.com/CommonRoad/commonroad-scenario-designer):

- It builds a strict prompt with the current code context.
- It calls OpenAI’s API and parses a **YAML block** containing both a **unified diff** and an **ops plan**.
- It **applies** changes either via:
  - a strict, trusted diff for `formula_collection.py` (when possible), and/or
  - **ops semantics** for the other three target files (append enum, add to group, ensure predicate).
- It **normalizes** formula strings and runs a **smoke test** on a CRD XML map.
- All artifacts (prompt/response/patch/logs) are saved under `./.llm_artifacts/<timestamp>/` for inspection.

The four writable target files (under CRD) are:
```
crdesigner/verification_repairing/verification/formula_ids.py
crdesigner/verification_repairing/verification/groups_handler.py
crdesigner/verification_repairing/verification/hol/formula_collection.py
crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py
```

---

## 2) Prerequisites

1. **CommonRoad Scenario Designer (CRD)**

   - Clone and install CRD from its official [GitHub](https://github.com/CommonRoad/commonroad-scenario-designer) repository. **Follow their instructions exactly** (Python version, dependency manager, etc.).
   - If CRD is not installed or not importable, the smoke test cannot run; you will still be able to generate artifacts (prompt/diff/ops).

2. **3D map note + example data**

   - The **official CRD** does **not** ship 3D map support for now.
   - This project provides **four handcrafted OpenDRIVE-format maps** *and* their **CRD-exported** 3D XML files (produced by our modified CRD with 3-D map support).  
   - All verifications in our examples run on these **CRD XML files** located at:
     ```
     example_files/opendrive/
     ```

3. **This repository**

   - Clone this repository and **place all its top-level folders into the CRD root directory** (so that paths like `crdesigner/...` resolve correctly inside the CRD checkout).
   - If you prefer keeping this repo separate, set the environment variable `CRD_ROOT` to the **absolute path of your CRD root** before running.

4. **System & Python**

   - Python **3.10+** (matching what CRD expects).
   - `git` available in your PATH.
   - (Optional) `patch` command available (Linux typically have it).

5. **Python dependencies**

   - Install CRD’s dependencies exactly as per the CRD repository (they commonly use Poetry or pip).
   - This tool additionally uses a small set of packages which are usually brought in by CRD or easy to install:
     ```bash
     pip install typer ruamel.yaml openai
     ```

6. **OpenAI credentials**

   - Set your API key in the environment:
     - Bash (Linux): `export OPENAI_API_KEY=sk-...`
   - Optional: set a model name via `OPENAI_MODEL` (defaults to `gpt-4o`).

---

## 3) Folder layout & environment variables

You can run from different locations. The tool uses these conventions:

- **`CRD_ROOT`**  
  Path to your _CommonRoad Scenario Designer_ checkout root.  
  If not set, **current directory (“.”)** is assumed.

- **`CRD_SCENARIO_XML`** (optional)  
  Path to a default scenario XML used by the smoke test if `--xml` is not provided.

### Examples

- **Running from the CRD root** (recommended for first-time users):
  ```bash
  cd /path/to/commonroad-scenario-designer  # CRD checkout root
  # All commands below assume we are in CRD root
  ```

- **Running from elsewhere**:
  ```bash
  export CRD_ROOT=/path/to/commonroad-scenario-designer
  cd /path/to/this-llm-rulegen-repo   # optional
  # Commands work because CRD_ROOT tells the tool where CRD lives
  ```

> Ensure the directory `example_files/opendrive/` (from this repo) is present under your **CRD root** so that the sample XML paths in this document resolve.

---

## 4) How the CLI is organized

We expose a Typer CLI command **`add`** in `tests/CRD-LLM-RuleGen.py`. It takes your natural-language rule(s), calls the LLM, and lands the changes (diff/ops), then runs a smoke test.

**Command syntax (simplified):**
```
python -u tests/CRD-LLM-RuleGen.py add [OPTIONS] "rule text ..." ["more rule text ..."]
```

**Key options:**
- `--diff-only / --no-diff-only` (default: `--diff-only True`)  
  Ask the LLM to return only YAML + diff, not full files (saves tokens).
- `--model TEXT`  
  Override model name (default comes from `OPENAI_MODEL`, typically `gpt-4o`).
- `--timeout FLOAT`  
  OpenAI request timeout (seconds).
- `--xml PATH`  
  Path to a **CRD XML** file used by the smoke test. If omitted, the tool will try `CRD_SCENARIO_XML` or an example path.
- `--no-rag` / `--rag-dir DIR`  
  Controls “read-only API” context scanning. RAG is disabled by default (safe to leave off).

**Positional arguments:**
- One or more paragraphs of **natural-language rule(s)**. They will be combined with context to produce the patch and ops.

---

## 5) Example: end‑to‑end run

### Example A (your path – as requested)

```bash
PYTHONUNBUFFERED=1 python -u tests/CRD-LLM-RuleGen.py add \
  --diff-only True \
  --model gpt-4o \
  --timeout 300 \
  --xml "/home/y/Desktop/commonroad-scenario-designer/example_files/opendrive/Vertical_Clearance_4m.xml" \
  "the min vertical clearance should more than 8m  between each other"
```

### Example B (general path – adapt to your machine)

```bash
# If not already in CRD root, export it:
export CRD_ROOT="/ABS/PATH/TO/commonroad-scenario-designer"

PYTHONUNBUFFERED=1 python -u tests/CRD-LLM-RuleGen.py add \
  --diff-only True \
  --model gpt-4o \
  --timeout 300 \
  --xml "$CRD_ROOT/example_files/opendrive/Vertical_Clearance_4m.xml" \
  "the min vertical clearance should more than 8m between each other"
```

---

## 6) What you should see (actual run output)

Below is a **real** output snippet from a successful run (paths redacted/shortened only in this paragraph).

> Command:
> ```bash
> PYTHONUNBUFFERED=1 python -u tests/CRD-LLM-RuleGen.py add \
>   --diff-only True \
>   --model gpt-4o \
>   --timeout 300 \
>   --xml "/home/y/Desktop/commonroad-scenario-designer/example_files/opendrive/Vertical_Clearance_4m.xml" \
>   "the min vertical clearance should more than 8m  between each other"
> ```
>
> Output (excerpt):
>
> ```text
> >>> Context sizes — code: 41635 chars, RAG: 0 chars
> >>> OpenAI preflight ...
> >>> Calling LLM to generate patch ...
> >>> Patch normalization failed, abandoning diff:Malformed hunk header: @@ -<old>,<n> +<new>,<m> @@
>
> ================================================================================
> >>> LLM has generated patches
> ================================================================================
>
> 📁 Generated files path: /home/y/Desktop/commonroad-scenario-designer/.llm_artifacts/20251003-100215
>    - prompt.txt / response.txt / patch.diff / code_context.txt
>
> --------------------------------------------------------------------------------
> >>> LLM full response (first 2000 characters):
> --------------------------------------------------------------------------------
> ```yaml
> antlr_patch: "NO_CHANGE"
> python_patch: |
>     --- crdesigner/verification_repairing/verification/formula_ids.py
>     +++ crdesigner/verification_repairing/verification/formula_ids.py
>     @@ -<old>,<n> +<new>,<m> @@
>      <BEFORE x6>
>     +    MIN_VERTICAL_CLEARANCE = "min_vertical_clearance"
>      <AFTER x6>
> ...
> ops:
>   - type: add_enum_member
>     file: crdesigner/verificatio
> ...
> --------------------------------------------------------------------------------
> >>> will apply ops strategy (semantic operations are as follows):
> --------------------------------------------------------------------------------
> [{'enum_class': 'LaneletFormulaID', 'file': 'crdesigner/verification_repairing/verification/formula_ids.py', ...}]
> --------------------------------------------------------------------------------
>
> ⚠️  Do you want to apply this change to the Git repository?
>    A new branch will be created: llm-rules/d129ff4486
> Please enter (yes/y/Enter to apply, no/n to cancel):
> ...
> ✅ User confirmed, start applying changes...
> >>> Applying ops semantics (other files & idempotent updates) ...
> [ops 1/4] BEGIN add_enum_member → crdesigner/verification_repairing/verification/formula_ids.py
> [ops 1/4] DONE in 0.00s
> [ops 2/4] BEGIN add_to_group → crdesigner/verification_repairing/verification/groups_handler.py
> [ops 2/4] DONE in 0.00s
> [ops 3/4] BEGIN upsert_formula_mapping → crdesigner/verification_repairing/verification/hol/formula_collection.py
> [ops 3/4] DONE in 0.00s
> [ops 4/4] BEGIN ensure_predicate → crdesigner/verification_repairing/verification/hol/functions/predicates/lanelet_predicates.py
> [ops 4/4] DONE in 0.00s
> >>> Normalizing formula strings in formula_collection.py ...
> [OK] Normalized: formula_collection.py  (backup: formula_collection.py.bak)
>     ✓ Formula strings have been normalized
> >>> Fixing LaneletFormulaID indentation and predicate scope ...
> >>> Running smoke test ...
> D.INCOMING_INTERSECTION: ... InvalidState(formula=<LaneletFormulaID.MIN_VERTICAL_CLEARANCE: 'min_vertical_clearance'>, element_ids=[19, 19, ...])]))])
>
> INFO:root:Validating map ZAM_MUC-1.
> ... (library warnings / info) ...
> INFO:root:Validating map ZAM_MUC-1 finished.
>
> >>> RAG context size: 0 chars; code ctx size: 41635 chars
> Done ✅
> ```

### Why are there “two blocks” of output?

It’s a single test run, but there are **two different output streams** merged in the final printout:

- The long `InvalidState(...)` list comes from our `run_smoke()`:
  ```python
  print("[SMOKE] verification finished. Result summary:", result)
  ```
  That is **stdout**.

- The `INFO:root:Validating map ZAM_MUC-1.` … `finished.` lines are **library logs from CRD/CommonRoad**, emitted via Python’s `logging`. By default, `logging` often writes to **stderr**.

Our tool concatenates `stdout` first, then `stderr` when displaying the tail of logs, so you see them as two “segments”. Both belong to the **same** run.

> In the sample above, you can also see `InvalidState(formula=<LaneletFormulaID.MIN_VERTICAL_CLEARANCE: 'min_vertical_clearance'>, ...)`, which confirms the new rule shows up in the verification results on the provided map `Vertical_Clearance_4m.xml`.

---

## 7) Tips & Troubleshooting

- **CRD not installed / import errors**  
  Ensure you followed the CRD repository instructions. Without CRD importable, only prompt/diff files will be generated; the smoke test will be skipped or fail.

- **“Patch normalization failed, abandoning diff …”**  
  The LLM sometimes outputs a template-like diff (`@@ -<old>,<n> +<new>,<m> @@`). Our pipeline then **falls back to the safer “ops” strategy**, which still lands the change deterministically.

- **Where are my artifacts?**  
  Look under:
  ```
  ./.llm_artifacts/<YYYYMMDD-HHMMSS>/
  ```
  - `prompt.txt` — the exact prompt sent to the model  
  - `response.txt` — raw model output  
  - `patch.diff` — the normalized diff (if applicable)  
  - `code_context.txt` — code context sent to the model  
  - `read_only_api.txt` — (if RAG was enabled)

- **Changing the map under test**  
  Use `--xml PATH/TO/MAP.xml`. In our examples we ship CRD XMLs under `example_files/opendrive/`.

- **Paths differ on your machine**  
  Set `CRD_ROOT=/absolute/path/to/commonroad-scenario-designer` and reference maps using `$CRD_ROOT/example_files/opendrive/...`.

- **OpenAI preflight errors**  
  Check `OPENAI_API_KEY`, any custom base URL/proxy, and your network connectivity.

---

## 8) Internals (optional)

- Only **four files** are ever modified (see the list at the top).  
- We **trust diff** only for `formula_collection.py` and use **ops** for the other three files.  
- We **normalize** formula strings into single-line, double-quoted values and emit lint warnings for common pitfalls.
- A minimal smoke test is launched in a **subprocess** to keep your environment clean.

---

## 9) Example quick recipe (copy‑paste)

```bash
# 1) Clone CRD -> install per CRD docs
# 2) Place this repository's folders into the CRD root (or set CRD_ROOT)
cd /path/to/commonroad-scenario-designer

# 3) Ensure OpenAI key
export OPENAI_API_KEY="sk-..."
export PYTHONUNBUFFERED=1

# 4) Run the LLM rule generator with our provided 3D CRD XML
python -u tests/CRD-LLM-RuleGen.py add \
  --diff-only True \
  --model gpt-4o \
  --timeout 300 \
  --xml "$PWD/example_files/opendrive/Vertical_Clearance_4m.xml" \
  "the min vertical clearance should more than 8m between each other"
```

If you see `InvalidState(formula=<LaneletFormulaID.MIN_VERTICAL_CLEARANCE: 'min_vertical_clearance'>, ...)`, the rule hooked correctly into the verification.

---

## 10) Acknowledgements

- CommonRoad Scenario Designer (CRD) — original authors and maintainers.
- OpenDRIVE example maps and CRD 3D XMLs included here were handcrafted for demonstration and testing.

Good luck, and enjoy!