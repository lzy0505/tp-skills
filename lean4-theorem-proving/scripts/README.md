# Lean 4 Theorem Proving Scripts

Automated tools for common Lean 4 workflows. These scripts implement the workflows described in SKILL.md with deterministic reliability.

## Scripts Overview

| Script | Purpose | When to Use |
|--------|---------|-------------|
| `search_mathlib.sh` | Find lemmas in mathlib | Before proving something that might exist |
| `check_axioms.sh` | Verify axiom usage | Before committing, during PR review |
| `sorry_analyzer.py` | Extract and report sorries | Planning work, tracking progress |

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

## check_axioms.sh

**Purpose:** Verify that theorems use only standard mathlib axioms, identifying any custom axioms that need elimination plans.

**Usage:**
```bash
./check_axioms.sh <file-or-directory> [--verbose]
```

**⚠️ LIMITATION:** This script only works for declarations that are part of the module's public API. Declarations in namespaces, sections, or marked `private` cannot be checked via external import.

**For checking all declarations (including internal ones):**
```lean
-- Add at the end of your Lean file:
#print axioms my_theorem
#print axioms my_lemma
```

**Standard Axioms (Acceptable):**
- `propext` - Propositional extensionality
- `quot.sound` / `Quot.sound` - Quotient soundness
- `Classical.choice` - Axiom of choice

**Examples:**
```bash
# Check single file
./check_axioms.sh src/DeFinetti/ViaL2.lean

# Check entire directory
./check_axioms.sh src/DeFinetti/

# Check with verbose output (shows all axioms)
./check_axioms.sh . --verbose
```

**Output:**
- ✓ Green: Declarations using only standard axioms
- ⚠ Red: Non-standard axioms (need elimination plans)

**Workflow:**
1. Run before committing new theorems
2. Add elimination plans for any custom axioms
3. Use during PR review to verify axiom hygiene
4. Track progress on axiom elimination

**Note:** Requires project to build (`lake build`) for imports to resolve.

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
