# Lean 4 Theorem Proving Scripts

Automated tools for common Lean 4 workflows. These scripts implement the workflows described in SKILL.md with deterministic reliability.

**All scripts validated on real Lean 4 formalization project (1000+ commits).** See `TESTING.md` for complete test results.

## Scripts Overview

| Script | Purpose | When to Use | Status |
|--------|---------|-------------|--------|
| `search_mathlib.sh` | Find lemmas in mathlib | Before proving something that might exist | ✅ Production |
| `check_axioms_inline.sh` | Verify axiom usage (all declarations) | Before committing, during PR review | ✅ Production |
| `check_axioms.sh` | Verify axiom usage (public API only) | Library files with flat structure | ⚠️ Limited |
| `sorry_analyzer.py` | Extract and report sorries | Planning work, tracking progress | ✅ Production |

## search_mathlib.sh

**Purpose:** Find existing lemmas, theorems, and definitions in mathlib to avoid reproving standard results.

**Usage:**
```bash
./search_mathlib.sh <query> [search-type]
```

**Search Types:**
- `name` (default) - Search declaration names
- `type` - Search type signatures
- `content` - Full content search (slower but comprehensive)

**Examples:**
```bash
# Find continuous functions and compactness lemmas
./search_mathlib.sh "continuous.*compact" name

# Search for integrability lemmas
./search_mathlib.sh "integrable" content

# Find measurable space instances
./search_mathlib.sh "MeasurableSpace" type
```

**Configuration:**
Set `MATHLIB_PATH` environment variable to override default `.lake/packages/mathlib`

**Output:**
- Matching files with line numbers
- Declaration snippets
- Import suggestions

**Workflow:**
1. Run search before proving anything
2. Check results for existing lemmas
3. Import and use `#check` to verify
4. Save hours by not reproving standard results

---

## check_axioms_inline.sh ✅ **Recommended**

**Purpose:** Verify that theorems use only standard mathlib axioms, identifying any custom axioms that need elimination plans. Works for ALL declarations including namespaces, sections, and private declarations.

**Usage:**
```bash
./check_axioms_inline.sh <file> [--verbose]
```

**How it works:**
1. Detects namespace from file
2. Temporarily appends `#print axioms` commands
3. Runs Lean and captures output
4. Restores file automatically (safe even if interrupted)
5. Filters out standard axioms

**Standard Axioms (Acceptable):**
- `propext` - Propositional extensionality
- `quot.sound` / `Quot.sound` - Quotient soundness
- `Classical.choice` - Axiom of choice

**Examples:**
```bash
# Check single file
./check_axioms_inline.sh MyFile.lean

# Verbose mode (shows all axioms, including standard ones)
./check_axioms_inline.sh MyFile.lean --verbose
```

**Output:**
```
✓ All declarations use only standard axioms

# Or if non-standard axioms found:
⚠ my_theorem uses non-standard axiom: my_custom_axiom
```

**Workflow:**
1. Run before committing new theorems
2. Add elimination plans for any custom axioms
3. Use during PR review to verify axiom hygiene

**Note:** Requires project to build successfully (`lake build`).

---

## check_axioms.sh ⚠️ **Limited - Public API Only**

**⚠️ LIMITATION:** This script only works for declarations that are part of the module's public API. Declarations in namespaces, sections, or marked `private` cannot be checked via external import.

**Recommendation:** Use `check_axioms_inline.sh` instead for regular development files.

**Usage:**
```bash
./check_axioms.sh <file-or-directory> [--verbose]
```

**When to use:**
- Library files with flat (non-namespaced) structure
- Checking public API of published libraries

## sorry_analyzer.py

**Purpose:** Extract all `sorry` statements with context and documentation to track incomplete proofs.

**Usage:**
```bash
./sorry_analyzer.py <file-or-directory> [--format=text|json|markdown]
```

**Output Formats:**
- `text` (default) - Human-readable terminal output
- `markdown` - Formatted report for documentation
- `json` - Machine-readable for tooling integration

**Examples:**
```bash
# Analyze single file
./sorry_analyzer.py src/DeFinetti/ViaKoopman.lean

# Generate markdown report for entire project
./sorry_analyzer.py src/ --format=markdown > SORRIES.md

# JSON output for CI/CD
./sorry_analyzer.py . --format=json > sorries.json
```

**Extracted Information:**
- Location (file and line number)
- Containing declaration (theorem/lemma/def)
- Documentation (TODO/NOTE comments)
- Context (surrounding code)

**Workflow:**
1. Run after structuring proof (Phase 1)
2. Track which sorries to tackle next
3. Monitor progress on sorry elimination
4. Generate reports for project status
5. Use in CI to track completion metrics

**Exit Code:**
- `0` - No sorries found (all proofs complete!)
- `1` - Sorries found (work remaining)

## Installation

All scripts are executable and self-contained:

```bash
# Make executable (if needed)
chmod +x scripts/*.sh scripts/*.py

# Run from skill directory or add to PATH
export PATH="$PATH:/path/to/lean4-theorem-proving/scripts"
```

## Requirements

- **Bash 4.0+** (for shell scripts)
- **Python 3.6+** (for sorry_analyzer.py)
- **Lean 4 project** with `lake` (for check_axioms.sh)
- **mathlib** in `.lake/packages/mathlib` (for search_mathlib.sh)

## Integration with Workflows

These scripts implement the systematic approaches from SKILL.md:

**Phase 1: Structure Before Solving**
→ Use `sorry_analyzer.py` to track structured sorries

**Phase 2: Helper Lemmas First**
→ Use `search_mathlib.sh` to find existing helpers

**Phase 3: Incremental Filling**
→ Use `sorry_analyzer.py` to pick next sorry

**Phase 4: Managing Type Class Issues**
→ Use `search_mathlib.sh` to find instance patterns

**Before Commit:**
→ Use `check_axioms.sh` to verify axiom hygiene

## Contributing

Found a bug or have an enhancement idea?
- Report issues: https://github.com/cameronfreer/lean4-theorem-proving-skill/issues
- Submit improvements via PR
- Share your own automation scripts

## License

MIT License - same as parent skill
