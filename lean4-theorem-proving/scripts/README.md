# Lean 4 Theorem Proving Scripts

Automated tools for common Lean 4 workflows. These scripts implement the workflows described in SKILL.md with deterministic reliability.

**All scripts validated on real Lean 4 formalization project (1000+ commits).** See `TESTING.md` for complete test results.

## Scripts Overview

| Script | Purpose | When to Use | Status |
|--------|---------|-------------|--------|
| `search_mathlib.sh` | Find lemmas in mathlib | Before proving something that might exist | ✅ Production |
| `smart_search.sh` | Multi-source search (APIs + local) | Advanced searches, natural language queries | ✅ Production |
| `find_instances.sh` | Find type class instances | Need instance patterns or examples | ✅ Production |
| `check_axioms_inline.sh` | Verify axiom usage (all declarations) | Before committing, during PR review | ✅ Production |
| `check_axioms.sh` | Verify axiom usage (public API only) | Library files with flat structure | ⚠️ Limited |
| `sorry_analyzer.py` | Extract and report sorries | Planning work, tracking progress | ✅ Production |
| `proof_complexity.sh` | Analyze proof metrics | Refactoring, identifying complex proofs | ✅ Production |
| `dependency_graph.sh` | Visualize theorem dependencies | Understanding proof structure | ✅ Production |

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

**Purpose:** Verify that theorems use only standard mathlib axioms, identifying any custom axioms that need elimination plans. Works for ALL declarations including namespaces, sections, and private declarations. **Now supports batch mode for multiple files!**

**Usage:**
```bash
./check_axioms_inline.sh <file-or-pattern> [--verbose]
```

**How it works:**
1. Detects namespace from file(s)
2. Temporarily appends `#print axioms` commands
3. Runs Lean and captures output
4. Restores file automatically (safe even if interrupted)
5. Filters out standard axioms
6. Generates summary across all files

**Standard Axioms (Acceptable):**
- `propext` - Propositional extensionality
- `quot.sound` / `Quot.sound` - Quotient soundness
- `Classical.choice` - Axiom of choice

**Examples:**
```bash
# Check single file
./check_axioms_inline.sh MyFile.lean

# Check multiple files (batch mode)
./check_axioms_inline.sh File1.lean File2.lean

# Check all files in directory with glob pattern
./check_axioms_inline.sh "src/**/*.lean"

# Verbose mode (shows all axioms, including standard ones)
./check_axioms_inline.sh MyFile.lean --verbose
```

**Batch Mode Features:**
- Process multiple files in one command
- Summary statistics (total files, declarations, custom axioms)
- Continues on errors, reports all issues at end
- Exit code 1 if any custom axioms or errors found

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
./sorry_analyzer.py <file-or-directory> [--format=text|json|markdown] [--interactive]
```

**Modes:**
- Default: Generate reports in various formats
- `--interactive`: Interactive TUI to browse and navigate sorries

**Output Formats:**
- `text` (default) - Human-readable terminal output
- `markdown` - Formatted report for documentation
- `json` - Machine-readable for tooling integration

**Examples:**
```bash
# Analyze single file
./sorry_analyzer.py src/DeFinetti/ViaKoopman.lean

# Interactive mode - browse and open sorries
./sorry_analyzer.py . --interactive

# Generate markdown report for entire project
./sorry_analyzer.py src/ --format=markdown > SORRIES.md

# JSON output for CI/CD
./sorry_analyzer.py . --format=json > sorries.json
```

**Interactive Mode Features:**
- Browse sorries grouped by file
- View detailed context for each sorry
- Open files directly in $EDITOR at sorry location
- Navigate between files and sorries

**Extracted Information:**
- Location (file and line number)
- Containing declaration (theorem/lemma/def)
- Documentation (TODO/NOTE comments)
- Context (surrounding code)

**Workflow:**
1. Run after structuring proof (Phase 1)
2. Use `--interactive` to pick next sorry to tackle
3. Monitor progress on sorry elimination
4. Generate reports for project status
5. Use in CI to track completion metrics

**Exit Code:**
- `0` - No sorries found (all proofs complete!)
- `1` - Sorries found (work remaining)

---

## smart_search.sh

**Purpose:** Multi-source theorem search combining local mathlib search with online APIs (LeanSearch, Loogle).

**Usage:**
```bash
./smart_search.sh <query> [--source=leansearch|loogle|mathlib|all]
```

**Sources:**
- `mathlib` (default) - Local ripgrep/grep search, no rate limits
- `leansearch` - Natural language semantic search via leansearch.net (~3 req/30s)
- `loogle` - Type-based search via loogle.lean-lang.org (~3 req/30s)
- `all` - Try all sources (respects rate limits)

**Examples:**
```bash
# Natural language search using LeanSearch API
./smart_search.sh "continuous functions on compact spaces" --source=leansearch

# Type pattern search using Loogle API
./smart_search.sh "(?a -> ?b) -> List ?a -> List ?b" --source=loogle

# Fast local search (no rate limits)
./smart_search.sh "continuous.*compact" --source=mathlib

# Try all sources
./smart_search.sh "Cauchy Schwarz" --source=all
```

**Query Patterns:**
- Natural language: "If there exist injective maps..."
- Type patterns: `(?a -> ?b) -> List ?a -> List ?b`
- Identifiers: "List.sum", "continuous"
- Mixed: "natural numbers. from: n < m, to: n + 1 < m + 1"

**Dependencies:**
- `curl` (for API sources)
- `jq` (optional, for formatted API output)

---

## find_instances.sh

**Purpose:** Find type class instances in mathlib to understand instance patterns and examples.

**Usage:**
```bash
./find_instances.sh <type-class-name> [--verbose]
```

**Searches For:**
- Instance declarations (`instance : TypeClass`)
- Deriving instances (`deriving TypeClass`)
- Implicit instance arguments (in `--verbose` mode)

**Examples:**
```bash
# Find MeasurableSpace instances
./find_instances.sh MeasurableSpace

# Find probability measure instances with verbose output
./find_instances.sh IsProbabilityMeasure --verbose

# Find Fintype instances
./find_instances.sh Fintype
```

**Use Cases:**
- Understanding how to instantiate type classes
- Finding patterns for writing your own instances
- Discovering available instances for a type

---

## proof_complexity.sh

**Purpose:** Analyze proof length and complexity metrics to identify complex proofs for refactoring.

**Usage:**
```bash
./proof_complexity.sh <file-or-directory> [--sort-by=lines|tokens|sorries]
```

**Metrics:**
- Lines per proof
- Estimated token count
- Tactics count
- Presence of sorries

**Examples:**
```bash
# Analyze single file
./proof_complexity.sh MyFile.lean

# Find most complex proofs by line count
./proof_complexity.sh src/ --sort-by=lines

# Find proofs with most sorries
./proof_complexity.sh . --sort-by=sorries
```

**Output:**
- Top 20 most complex proofs
- Summary statistics (averages)
- Size distribution (small/medium/large/huge)
- Sorry count warnings

**Proof Size Categories:**
- Small: ≤10 lines
- Medium: 11-50 lines
- Large: 51-100 lines
- Huge: >100 lines

---

## dependency_graph.sh

**Purpose:** Visualize theorem dependencies within a file to understand proof structure.

**Usage:**
```bash
./dependency_graph.sh <file> [--format=dot|text]
```

**Output Formats:**
- `dot` - GraphViz DOT format for visualization
- `text` (default) - Dependency tree with counts

**Examples:**
```bash
# Text dependency tree
./dependency_graph.sh MyFile.lean

# Generate PNG visualization with graphviz
./dependency_graph.sh MyFile.lean --format=dot | dot -Tpng > deps.png

# View in browser with dot
./dependency_graph.sh MyFile.lean --format=dot | dot -Tsvg > deps.svg
```

**Features:**
- Identifies leaf theorems (no internal dependencies)
- Shows dependency counts per theorem
- Highlights highly coupled theorems
- Helps identify refactoring opportunities

---

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
