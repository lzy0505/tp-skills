# lean4-theorem-proving

Systematic workflows for Lean 4 proof development.

## Overview

This skill teaches Claude how to develop formal proofs in Lean 4 using battle-tested workflows from real formalization projects. It provides systematic approaches, automation tools, and domain-specific patterns for measure theory, probability, and algebra.

## What You Get

### 4-Phase Proof Development Workflow

1. **Structure Before Solving** - Outline proof strategy before writing tactics
2. **Helper Lemmas First** - Build infrastructure bottom-up
3. **Incremental Filling** - One `sorry` at a time, compile, commit, repeat
4. **Type Class Management** - Explicit instance handling for sub-structures

### 16 Automation Scripts

**Search (4 scripts):**
- `search_mathlib.sh` - Find lemmas in mathlib by name, type, or content
- `smart_search.sh` - Multi-source search (mathlib + APIs)
- `find_instances.sh` - Locate type class instances
- `find_usages.sh` - Track theorem usage across project

**Analysis (4 scripts):**
- `proof_complexity.sh` - Analyze proof metrics (lines, tactics, tokens)
- `dependency_graph.sh` - Visualize theorem dependencies
- `build_profile.sh` - Profile build performance and bottlenecks
- `suggest_tactics.sh` - Get tactic suggestions for goals

**Verification (4 scripts):**
- `sorry_analyzer.py` - Extract and track sorries with context
- `check_axioms.sh` - Verify axiom usage (external import method)
- `check_axioms_inline.sh` - Verify axiom usage (inline method)
- `simp_lemma_tester.sh` - Test `@[simp]` lemmas for issues

**Quality & Refactoring (4 scripts):**
- `pre_commit_hook.sh` - Comprehensive quality gates
- `unused_declarations.sh` - Find dead code
- `minimize_imports.py` - Remove unused imports
- `proof_templates.sh` - Generate proof skeletons

➡️ **[Scripts Documentation](scripts/README.md)** | **[Testing Report](scripts/TESTING.md)**

### Comprehensive Guides

**Core Workflow:**
- [SKILL.md](skills/lean4-theorem-proving/SKILL.md) - Main skill document (loaded automatically)

**References (loaded as needed):**
- [lean-phrasebook.md](skills/lean4-theorem-proving/references/lean-phrasebook.md) - Mathematical English to Lean translations
- [mathlib-guide.md](skills/lean4-theorem-proving/references/mathlib-guide.md) - Search strategies, imports, naming conventions
- [mathlib-style.md](skills/lean4-theorem-proving/references/mathlib-style.md) - Mathlib style conventions and formatting
- [tactics-reference.md](skills/lean4-theorem-proving/references/tactics-reference.md) - Comprehensive tactics catalog
- [calc-patterns.md](skills/lean4-theorem-proving/references/calc-patterns.md) - Calc chain patterns and simp optimization
- [domain-patterns.md](skills/lean4-theorem-proving/references/domain-patterns.md) - Math domain-specific patterns
- [measure-theory.md](skills/lean4-theorem-proving/references/measure-theory.md) - Sub-σ-algebras and conditional expectation
- [compilation-errors.md](skills/lean4-theorem-proving/references/compilation-errors.md) - Error debugging and solutions
- [proof-golfing.md](skills/lean4-theorem-proving/references/proof-golfing.md) - Simplifying proofs after compilation
- [lean-lsp-server.md](skills/lean4-theorem-proving/references/lean-lsp-server.md) - Lean LSP server tools (Claude Code users)
- [subagent-workflows.md](skills/lean4-theorem-proving/references/subagent-workflows.md) - Subagent delegation patterns (Claude Code users)

## Installation

See [INSTALLATION.md](../INSTALLATION.md) for installation instructions.

### How This Plugin Works

**Hooks (Automatic Setup):**

This plugin includes a lightweight `SessionStart` hook that runs once when Claude Code starts:

```bash
hooks/bootstrap.sh
```

**What it does (all read-only and innocuous):**
1. Finds Python interpreter (`python3` or `python`)
2. Locates the plugin's scripts directory
3. Copies 8 tool scripts to `.claude/tools/lean4/` in your workspace
4. Sets environment variables for the session
5. Reports status (visible in debug logs)

**Why this is safe:**
- ✅ Read-only operations (only copies files, doesn't modify code)
- ✅ Runs in sandboxed environment
- ✅ Only copies known tool scripts (no arbitrary code execution)
- ✅ Fails gracefully if Python is not installed
- ✅ No network access, no file modification, no git operations

**What gets staged to `.claude/tools/lean4/`:**
- `sorry_analyzer.py` - Analyzes incomplete proofs
- `search_mathlib.sh` - Searches mathlib by name/content
- `smart_search.sh` - Multi-source search (local + APIs)
- `check_axioms.sh` - Verifies axiom usage
- `find_golfable.py` - Finds proof optimization opportunities
- `analyze_let_usage.py` - Analyzes let binding usage
- `count_tokens.py` - Counts proof tokens
- `suggest_tactics.sh` - Suggests tactics for goals

This staging approach avoids Claude Code's parameter substitution security filter, allowing slash commands to reference scripts reliably.

## Usage

### Automatic Activation

Claude automatically uses this skill when you:
- Work on `.lean` files
- Mention Lean 4, theorem proving, or formal verification
- Prove theorems or manage sorries/axioms
- Ask about mathlib or type class issues

No manual invocation needed!

### Key Principles

- ✅ **Always compile before commit** (`lake build` is your test suite)
- ✅ **Document every sorry** with strategy and dependencies
- ✅ **Search mathlib first** before reproving standard results
- ✅ **Eliminate axioms systematically** with documented plans
- ✅ **One change at a time** - fill one sorry, compile, commit

### Slash Commands

**What are slash commands?**

Slash commands are interactive workflows you can invoke by typing `/` followed by the command name. They combine multiple scripts and provide guided, step-by-step assistance.

**Available commands** (type `/lean4-theorem-proving:` and it will autocomplete):

**Search & Discovery:**
```
/lean4-theorem-proving:search-mathlib continuity compactness
```
Find relevant lemmas in mathlib before proving. Searches by name, type pattern, or natural language description. Tries multiple search strategies automatically.

**Project Analysis:**
```
/lean4-theorem-proving:analyze-sorries
```
Scan project for incomplete proofs, categorize by difficulty (easy/medium/hard), and plan systematic filling work. Highlights undocumented sorries.

**Interactive Proof Development:**
```
/lean4-theorem-proving:fill-sorry MyTheorems.lean:142
```
Get tactic suggestions, lemma search results, and multi-candidate testing for a specific sorry. Generates 2-3 proof approaches and tests them.

**Quality Verification:**
```
/lean4-theorem-proving:check-axioms MyTheorems.lean
```
Verify proofs use only standard axioms (propext, quot.sound, Classical.choice). Reports any custom axioms that need elimination.

```
/lean4-theorem-proving:build-lean
```
Run `lake build` with formatted error analysis and actionable debugging hints. Categorizes errors by type.

**Proof Optimization:**
```
/lean4-theorem-proving:golf-proofs MyFile.lean
```
Interactively simplify proofs after compilation (30-40% reduction typical). Includes false-positive filtering to avoid making code worse.

```
/lean4-theorem-proving:clean-warnings
```
Systematically clean up linter warnings by category (unused variables, simp args, etc.). Fixes safest categories first with verification.

**How to use:**
1. Type `/lean4-theorem-proving:` in Claude Code
2. Select a command from autocomplete
3. Add any required arguments (file paths, search queries)
4. Follow the interactive prompts

### Common Patterns

**Integrability proofs:**
```lean
have h_integrable : Integrable X μ := by
  refine ⟨h_measurable, ?_⟩
  calc ∫⁻ a, ‖X a‖₊ ∂μ
    ≤ ∫⁻ a, M ∂μ := by apply lintegral_mono; intro; apply h_bound
    _ = M * μ univ := lintegral_const M
    _ < ∞ := by simp [h_prob, ENNReal.mul_lt_top]
```

**Conditional expectation equalities:**
```lean
theorem condExp_unique (hX : Measurable X) (hY : Measurable Y)
    (h_eq : ∀ s, MeasurableSet[m] s → ∫ x in s, X x ∂μ = ∫ x in s, Y x ∂μ) :
    condExp μ m X =ᵐ[μ] Y := by
  apply ae_eq_condExp_of_forall_setIntegral_eq hX hY
  exact h_eq
```

**Type class instance management:**
```lean
-- Explicit instance when Lean can't infer
haveI : MeasurableSpace Ω := inferInstance
haveI : IsProbabilityMeasure μ := h_prob

-- Now use dependent results
apply measure_eq_on_generateFrom
```

## When to Use

**Perfect for:**
- Formalizing mathematical theorems (analysis, algebra, topology)
- Working with measure theory and probability
- Contributing to mathlib
- Managing complex proof development
- Converting axioms to proven lemmas
- Dealing with type class inference issues

**Especially helpful when:**
- Starting a new Lean formalization project
- Learning Lean 4 from Lean 3 or other proof assistants
- Stuck with type class synthesis errors
- Managing multiple interrelated proofs
- Working on real analysis, probability, or abstract algebra

## Contents

```
lean4-theorem-proving/
├── README.md                      # This file
├── commands/                      # Slash commands
│   ├── search-mathlib.md          # Search mathlib lemmas
│   ├── analyze-sorries.md         # Analyze incomplete proofs
│   ├── fill-sorry.md              # Fill sorries interactively
│   ├── check-axioms.md            # Verify axiom hygiene
│   ├── build-lean.md              # Build with error analysis
│   ├── golf-proofs.md             # Optimize proofs
│   └── clean-warnings.md          # Clean linter warnings
├── scripts/                       # 16 automation tools
│   ├── README.md                  # Scripts documentation
│   ├── TESTING.md                 # Comprehensive validation report
│   ├── search_mathlib.sh          # Find mathlib lemmas
│   ├── smart_search.sh            # Multi-source search
│   ├── find_instances.sh          # Type class instances
│   ├── find_usages.sh             # Usage tracking
│   ├── sorry_analyzer.py          # Sorry extraction
│   ├── check_axioms.sh            # Axiom verification (external)
│   ├── check_axioms_inline.sh     # Axiom verification (inline)
│   ├── proof_complexity.sh        # Proof metrics
│   ├── dependency_graph.sh        # Dependency visualization
│   ├── build_profile.sh           # Build profiling
│   ├── suggest_tactics.sh         # Tactic suggestions
│   ├── proof_templates.sh         # Proof scaffolding
│   ├── unused_declarations.sh     # Dead code detection
│   ├── simp_lemma_tester.sh       # Simp hygiene
│   ├── pre_commit_hook.sh         # Quality gates
│   └── minimize_imports.py        # Import minimization
└── skills/lean4-theorem-proving/  # Skill content
    ├── SKILL.md                   # Core workflow (loaded by Claude)
    └── references/                # Detailed guides
        ├── lean-phrasebook.md     # Math English to Lean
        ├── mathlib-guide.md       # mathlib integration
        ├── mathlib-style.md       # Mathlib style conventions
        ├── tactics-reference.md   # Tactics catalog
        ├── calc-patterns.md       # Calc chain patterns
        ├── domain-patterns.md     # Math patterns
        ├── measure-theory.md      # Sub-σ-algebras, conditional expectation
        ├── compilation-errors.md  # Error solutions
        ├── proof-golfing.md       # Proof simplification
        ├── lean-lsp-server.md     # LSP tools (Claude Code)
        └── subagent-workflows.md  # Subagent patterns (Claude Code)
```

## Examples from Real Projects

This skill was developed from real-world Lean 4 formalization work:

**Project:** de Finetti theorem formalization (1000+ commits, 22 files)

**Patterns extracted:**
- π-system uniqueness for measure equality
- Conditional expectation via integral identity
- Type class instance management for sub-σ-algebras
- Systematic axiom elimination (75 axioms → 6 sorries → 0)

**Scripts validated on:**
- Exchangeability formalization
- All 16 scripts tested on real codebase
- See [scripts/TESTING.md](scripts/TESTING.md) for validation report

## Requirements

- **Claude Code 2.0.13+** (for marketplace installation), OR
- **Claude.ai Pro/Max/Team/Enterprise** (for web/API), OR
- **Just Claude** (for CLAUDE.md method)
- (Optional) Lean 4 installed for working on Lean projects

## FAQ

### How does this work with the lean4-memories skill?

lean4-memories is optional and adds persistent learning across sessions. This skill (lean4-theorem-proving) works standalone and provides all core functionality.

**Use together:** lean4-theorem-proving provides general workflows, lean4-memories adds project-specific context.

See [lean4-memories/README.md](../lean4-memories/README.md) for details.

### Do I need all 16 scripts?

No! Scripts are organized by use case:
- **Daily use:** search_mathlib.sh, sorry_analyzer.py, suggest_tactics.sh
- **Quality gates:** pre_commit_hook.sh, check_axioms_inline.sh
- **Specific tasks:** All others (use as needed)

### Can I use just the SKILL.md without scripts?

Yes! The SKILL.md provides the core workflow. Scripts are optional automation tools.

### How is this different from Claude's general Lean knowledge?

Claude has general Lean knowledge from training. This skill provides:
- **Specific workflows** (structure before solve, one sorry at a time)
- **Project patterns** (type class management, mathlib integration)
- **Quality standards** (compile before commit, document sorries)
- **Automation tools** (16 scripts for common tasks)

It's like having a Lean 4 expert mentor coaching Claude.

## Contributing

Contributions welcome! See [main README](../README.md#contributing) for guidelines.

**Ways to contribute:**
- Share additional proof patterns
- Add domain-specific tactics
- Submit examples from successful projects
- Report issues or unclear guidance

## License

MIT License - see [../LICENSE](../LICENSE)

## Related Resources

**Official Lean 4:**
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

**Claude Skills:**
- [Claude Skills Documentation](https://www.anthropic.com/news/skills)
- [Main Repository](../README.md)

---

Part of [lean4-skills](../README.md) - Lean 4 Skills for Claude
