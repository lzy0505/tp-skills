---
name: lean4-theorem-proving
description: This skill should be used when developing Lean 4 proofs, managing sorries/axioms, facing "failed to synthesize instance" or type class errors, or searching mathlib - provides systematic build-first workflow, type class management patterns (haveI/letI), and domain-specific tactics for measure theory, probability, and algebra
---

# Lean 4 Theorem Proving

## Overview

Lean 4 is an interactive theorem prover. Unlike traditional code, correctness is verified by the type checker—there are no "unit tests."

**What "success" means in Lean 4:**
- ✅ File compiles (`lake build` succeeds)
- ✅ **Zero sorries** (or only documented active work-in-progress)
- ✅ **Zero custom axioms** (or only with explicit user approval and elimination plan)
- ✅ Only standard mathlib axioms (`Classical.choice`, `propext`, `quot.sound`)

**A theorem is NOT proved if it contains sorries or custom axioms.** Those are scaffolding, not results.

**Core principle:** Build incrementally, structure before solving, and trust the type checker.

## When to Use This Skill

Use these workflows for ANY Lean 4 development across all mathematical domains:
- Pure mathematics (algebra, topology, analysis, number theory, combinatorics)
- Applied mathematics (probability, optimization, numerical methods)
- Computer science (algorithms, data structures, program verification)
- Contributing to or extending mathlib

**Especially important when you see:**
- **Compilation errors:** "failed to synthesize instance", "maximum recursion depth", "type mismatch", "unknown identifier"
- **Type class issues:** MeasurableSpace, IsProbabilityMeasure, or other instance synthesis failures
- **Sorry accumulation:** Multiple sorries with unclear elimination strategy
- **Axiom proliferation:** Custom axioms without documented proof plans
- **Search challenges:** Need to find mathlib lemmas but don't know where to look
- **Working with:** measure theory, conditional expectation, σ-algebras, integrability

## Powerful Tools at Your Disposal

**🚀 Lean LSP Server (GAME CHANGER - if available):** **30x faster feedback** vs build-only
- **Instant proof state** - See goals in < 1 second (not 30+ seconds building)
- **Parallel tactic testing** - Test 4 tactics at once with `lean_multi_attempt`
- **Integrated search** - `lean_local_search` unlimited, `lean_loogle` type patterns
- **No more guessing** - Verify before editing, not after slow builds
- **Setup:** See [INSTALLATION.md](../INSTALLATION.md#lean-lsp-server) (5 minute one-time config)
- **Full guide:** `references/lean-lsp-server.md` with battle-tested workflows

**⚡ Subagent Delegation (Efficient - Claude Code users):** 6x token reduction
- Dispatch Explore agents to run automation scripts
- Example: `"Dispatch Explore agent to run scripts/smart_search.sh..."`
- See `references/subagent-workflows.md` for patterns and examples

**🔧 Automation Scripts (16 tools - all users):** Located in `scripts/`
- **Search:** search_mathlib.sh, smart_search.sh, find_instances.sh, find_usages.sh
- **Analysis:** proof_complexity.sh, dependency_graph.sh, build_profile.sh, unused_declarations.sh
- **Learning:** suggest_tactics.sh, proof_templates.sh
- **Verification:** check_axioms_inline.sh, sorry_analyzer.py, simp_lemma_tester.sh, pre_commit_hook.sh
- **Refactoring:** minimize_imports.py
- See `scripts/README.md` for complete documentation

**Priority:** Use LSP server when available → Delegate to subagents → Run scripts directly

## The Build-First Principle

```
ALWAYS ensure the file compiles before committing
```

**Lean has no runtime tests.** The type checker IS your test suite.

**CRITICAL: "Compiles" ≠ "Complete"**

A file can compile with sorries/axioms, but that doesn't mean the work is done:

```lean
-- ✅ Compiles, ❌ NOT complete
theorem my_result : Important_Property := by
  sorry

-- ✅ Compiles, ❌ NOT complete
axiom helper_lemma : Key_Fact

-- ✅ Compiles, ❌ NOT complete (trivial placeholder)
theorem placeholder : True := trivial
```

**What "complete" actually means:**
- ✅ File compiles with `lake build`
- ✅ NO sorries (except documented work-in-progress)
- ✅ NO custom axioms (except with explicit user approval and elimination plan)
- ✅ NO trivial placeholders (`by True := trivial`, etc.)
- ✅ Only standard mathlib axioms (`Classical.choice`, `propext`, `quot.sound`)

**Build commands:**
```bash
lake build              # Full project
lake env lean MyFile.lean  # Single file
lake clean && lake build   # Clean rebuild
```

**Before any commit:**
1. Run `lake build` on the full project
2. Verify no new errors introduced
3. Document any remaining `sorry`s with clear strategy (or eliminate them)

## The 4-Phase Workflow

### Phase 1: Structure Before Solving

**DON'T:** Start writing tactics immediately
**DO:** Understand the goal structure first

```lean
-- ✅ Good: Structure with clear subgoals
lemma main_theorem (h : Hypothesis) : Conclusion := by
  -- Strategy: Show Q by constructing witness from h
  -- Need: (1) Extract x from h, (2) Show x satisfies Q
  have h_extract : Extract := sorry  -- TODO: Use helper_lemma_1
  have h_property : Property := sorry  -- TODO: Apply known_result
  sorry  -- TODO: Combine above
```

**Key insight:** Outline proof strategy before writing tactics. Break into named helpers, use `have` for subgoals, document sorries.

### Phase 2: Helper Lemmas First

Build infrastructure bottom-up. Extract reusable components:

```lean
private lemma helper_step (x : X) : Property x := sorry

theorem main : Result := by
  have h1 := helper_step x
  have h2 := helper_step y
  -- Combine h1 and h2
```

### Phase 3: Incremental Filling

**One sorry at a time:** Choose ONE sorry → Fill completely → Compile → Commit → Repeat

**Never:** Fill 5 sorries simultaneously, commit without compiling, or skip documentation.

**🚀 Track sorries with LSP server (if available):**
```lean
-- See proof state at sorry location
mcp__lean-lsp__lean_goal("MyFile.lean", line_number, column_number)
```

**⚡ Use interactive navigator (Claude Code users):**
```bash
scripts/sorry_analyzer.py . --interactive
# Browse sorries, open in $EDITOR, navigate by file
```

**🔧 Generate sorry reports:**
```bash
# Dispatch Explore agent to run:
scripts/sorry_analyzer.py src/ --format=markdown > SORRIES.md
```

### Phase 4: Managing Type Class Issues

**Sub-structures need explicit instances** (common with sub-σ-algebras, submeasures):

```lean
-- ❌ Common error: Lean can't synthesize instance
have h_le : m ≤ m0 := ...
-- Later: "Failed to synthesize MeasurableSpace Ω"
--        "typeclass instance problem is stuck"

-- ✅ Fix: Provide instance explicitly
haveI : MeasurableSpace Ω := m0  -- Explicit instance
-- OR use Fact:
haveI : Fact (m ≤ m0) := ⟨h_le⟩
```

**CRITICAL - Binder order matters:** When working with sub-structures (like `m : MeasurableSpace Ω` with ambient `[MeasurableSpace Ω]`), the parameter `m` must come AFTER all instance parameters to avoid instance resolution choosing the wrong structure.

**When synthesis fails:** Add `haveI : Instance := ...`, use `letI` for let-bound, or `@lemma (inst := your_instance)`.

## Finding and Using Mathlib Lemmas

**Philosophy:** Search before prove. Mathlib has 100,000+ theorems.

**🚀 BEST: Use LSP server tools (if available)**
```lean
-- Find theorems by semantic search
mcp__lean-lsp__lean_leansearch("continuous functions on compact spaces")

-- Find theorems by type pattern
mcp__lean-lsp__lean_loogle("(?a -> ?b) -> List ?a -> List ?b")

-- Search current workspace
mcp__lean-lsp__lean_local_search("continuous")
```

**⚡ EFFICIENT: Dispatch Explore agent (Claude Code users)**
```
"Dispatch Explore agent to run scripts/smart_search.sh 'continuous compact' --source=all and report top 3 results"
```

**🔧 MANUAL: Direct search (without MCP/Claude Code)**
```bash
scripts/smart_search.sh "continuous compact" --source=leansearch
scripts/search_mathlib.sh "continuous.*compact" name
```

**Workflow:**
1. Search using LSP tools (preferred) or scripts
2. Read candidate file
3. Import and verify: `#check Continuous.isCompact_preimage`

**For detailed search techniques, naming conventions, and import organization, see:** `references/mathlib-guide.md`

## Essential Tactics

**Simplification:**
```lean
simp only [lem1, lem2]  -- Explicit (preferred)
simpa using h           -- Simplify and close
```

**Case analysis:**
```lean
by_cases h : p          -- Split on decidable
rcases h with ⟨x, hx⟩   -- Destructure exists/and
```

**Rewriting:**
```lean
rw [lemma]              -- Left-to-right
rw [← lemma]            -- Right-to-left
```

**Apply:**
```lean
apply lemma             -- Apply, leave subgoals
exact expr              -- Close goal exactly
refine pattern ?_       -- Apply with holes
```

**Function equality:**
```lean
ext x / funext x        -- Prove functions equal pointwise
```

**For comprehensive tactics guide, simp deep dive, and automation, see:** `references/tactics-reference.md`

## Domain-Specific Patterns

**Analysis & Topology:**
- Integrability: bounded + measurable + finite = integrable
- Continuity from preimage
- Compactness via finite subcover
- Tactics: `continuity`, `fun_prop`

**Algebra:**
- Build instances compositionally: `instance : CommRing (Polynomial R) := inferInstance`
- Quotient constructions with `refine`
- Tactics: `ring`, `field_simp`, `group`

**Measure Theory & Probability:**
- Conditional expectation equality via uniqueness
- Type class instance management for sub-σ-algebras
- Almost everywhere properties: `ae_of_all`, `filter_upwards`
- Tactics: `measurability`, `positivity`

**For detailed patterns, real-world examples, and measure theory specifics, see:** `references/domain-patterns.md`

## Managing Incomplete Proofs

### Standard vs Custom Axioms

**Standard mathlib axioms (acceptable):** `Classical.choice`, `propext`, `quot.sound`

Check with: `#print axioms my_theorem`

**Custom axioms need elimination plan:**
```lean
-- ❌ Bad: No plan
axiom my_conjecture : P

-- ✅ Good: Documented strategy
axiom helper_theorem : P
-- TODO: Prove using technique X, need lemmas A, B from mathlib, ~2 days
```

### Sorry Documentation

**Every sorry needs:** What (goal), How (strategy), Dependencies (blockers)

```lean
have h : Complex_Goal := by
  sorry
  -- TODO: (1) Apply monotone convergence, (2) Show f_n ≤ f_{n+1},
  --       (3) Show bound. Need `tendsto_lintegral_of_monotone`, ~2h
```

### The "Not in Mathlib" Antipattern

**CRITICAL: Sorries/Axioms Are NOT "Complete" Work**

Even if a theorem compiles and "works" with sorries, **the work is not done**.

**❌ WRONG - Treating sorries/axioms as acceptable endpoints:**
```lean
lemma helper : Key_Property := by
  sorry
  -- TODO: This should be in mathlib but isn't

lemma infrastructure : Basic_Fact := by
  sorry
  -- Infrastructure - not blocking main proof

axiom utility_lemma : Common_Pattern
-- We can use this for now, will prove later

theorem main_result : Big_Theorem := by
  apply helper
  exact infrastructure ...
-- ✅ Compiles! ❌ But NOT complete - has 2 sorries + 1 axiom
```

**Why this is wrong:**
- Sorries are placeholders, not proofs
- "Should be in mathlib" is not a justification to leave sorries
- "Infrastructure" sorries are still sorries - they need proofs
- The goal is a **complete, verified proof**, not "proof modulo missing lemmas"
- **You cannot claim a theorem is proved if it depends on sorries/axioms**

**✅ CORRECT - Prove it yourself:**
```lean
-- If it's not in mathlib, search thoroughly first
-- scripts/smart_search.sh "key property" --source=all
-- lean_local_search("key property")

-- If truly missing: PROVE IT
lemma helper : Key_Property := by
  -- Actual proof steps
  intro x
  apply monotone_lemma
  exact bound_from_hypothesis

-- If complex: break into smaller lemmas
lemma helper_step1 : Subproperty := by ...
lemma helper_step2 : Another_Subproperty := by ...
lemma helper : Key_Property := by
  apply helper_step1
  exact helper_step2 ...
```

**When sorries are acceptable:**
1. **Active work in progress** - you're currently filling them (document order/plan)
2. **Documented axioms** - clear elimination strategy and timeline
3. **Explicitly scoped** - user agrees to leave as axioms (rare)

**Not acceptable:**
- "This should be in mathlib" (then search harder, or prove it)
- "Infrastructure lemma" (still needs proof)
- "Will be added later" (when? by whom? with what strategy?)

### Elimination Pattern

```lean
-- 1. Search mathlib thoroughly FIRST
-- scripts/smart_search.sh "property name" --source=all

-- 2. If truly missing, prove it
lemma key_lemma : Goal := by
  -- YOUR proof here, not sorry

-- 3. If you must use axiom temporarily, document elimination plan
axiom key_lemma : Goal
-- TODO: Eliminate by [concrete strategy], need [specific mathlib lemmas],
--       estimated [time], assigned to [person/you]. NOT "hope mathlib adds this."
```

## Common Compilation Errors

Quick reference for the most common errors:

| Error | Fix |
|-------|-----|
| "failed to synthesize instance" | Add `haveI : IsProbabilityMeasure μ := ⟨proof⟩` |
| "maximum recursion depth" | Provide manually: `letI := instance` or increase limit |
| "type mismatch" (has type ℕ but expected ℝ) | Use coercion: `(x : ℝ)` or `↑x` |
| "tactic 'exact' failed" | Use `apply` or restructure term |
| "unknown identifier 'ring'" | Add: `import Mathlib.Tactic.Ring` |

**For detailed error explanations, debugging, and solutions, see:** `references/compilation-errors.md`

## Leveraging Subagents for Automation

**For Claude Code users:** Delegate mechanical tasks to subagents. This keeps main conversation focused on proof strategy.

**Quick reference:**
- **Dispatch for:** Search, analysis, verification, exploration tasks
- **Keep local:** Proof development, design decisions, error debugging
- **Use Explore agents** for most script execution (fast, cheap)
- **6x token savings** vs running scripts directly

**Common patterns:**
```
"Dispatch Explore agent to run scripts/smart_search.sh 'continuous compact' and report top 3"
"Dispatch Explore agent to:
 1. Run sorry_analyzer.py and report count
 2. Run check_axioms_inline.sh and report issues"
```

**For complete workflows, patterns, and examples, see:** `references/subagent-workflows.md`

## Documentation Conventions

### Write Timeless Documentation

Documentation should describe what the code **is** and **does**, not what it **was** or how it evolved.

**Avoid development history references:**
```lean
-- ❌ BAD
/-- In earlier drafts, this used axioms, but now it doesn't. -/
/-- Originally defined differently, but we changed the approach. -/
/-- This replaces the old broken implementation. -/

-- ✅ GOOD
/-- Uses mathlib's standard measure theory infrastructure. -/
/-- Constructs via the Koopman representation. -/
```

**Rationale:** Development history belongs in git commits, not source comments. Historical references become confusing and add no value to understanding code.

### Avoid Highlighting "Axiom-Free" Code (After Proved)

Once a theorem has been proved (removing the `axiom` keyword), don't highlight that it no longer uses axioms:

```lean
-- ❌ BAD (after development complete)
/-- This construction is completely **axiom-free** and uses only standard mathlib. -/

-- ✅ GOOD
/-- This construction uses mathlib's standard measure theory infrastructure. -/
```

**Rationale:** Not adding custom `axiom` declarations is the expected default state. Highlighting it is unnecessary and may become outdated if code is refactored.

**Exception:** During development, documenting axiom placeholders is appropriate:
```lean
-- ✅ GOOD (during development)
/-- Key lemma for the martingale proof. For now, accepting as axiom. -/
axiom conditionallyIID_of_exchangeable : ...
```

**Note:** Discussion of *mathematical* axioms (Choice, etc.) is perfectly acceptable when mathematically relevant:
```lean
-- ✅ GOOD
/-- This construction avoids the Axiom of Choice by using a canonical limit process. -/
```

### Keep Public API Clean

Make internal helpers `private` or place them in dedicated internal sections:

```lean
/-! ### Internal helpers -/

private lemma indicator_bounded : ... := by ...
private lemma intermediate_step : ... := by ...

/-! ### Public API -/

theorem main_result : ... := by ...
```

### Educational Examples

Use `example` instead of `lemma/theorem` for educational code that shouldn't enter the namespace:

```lean
-- ❌ BAD: Unnecessary lemma in namespace
lemma unused_stub : True := trivial

-- ✅ GOOD: Educational example that doesn't pollute namespace
example : True := trivial
```

## Quality Checklist

**Before commit:**
- [ ] File compiles: `lake env lean <file>`
- [ ] Full project builds: `lake build`
- [ ] All new `sorry`s documented with strategy
  - 🚀 MCP: Use `mcp__lean-lsp__lean_diagnostic_messages`
  - ⚡ Script: Dispatch agent with `scripts/sorry_analyzer.py`
- [ ] No new axioms (or documented with elimination plan)
  - 🚀 Best: N/A (MCP doesn't have axiom checker)
  - ⚡ Efficient: Dispatch agent with `scripts/check_axioms_inline.sh "src/**/*.lean"`
  - 🔧 Manual: Run `scripts/check_axioms_inline.sh` directly
- [ ] Imports minimal and specific

**Efficient workflow (Claude Code users):**
```
"Dispatch Explore agent to:
1. Run scripts/sorry_analyzer.py src/ and report count
2. Run scripts/check_axioms_inline.sh 'src/**/*.lean' and report any issues
3. Summarize: Ready to commit?"
```

**Doing it right ✅:**
- File always compiles after each change
- Each commit advances one specific lemma **to completion** (no new sorries)
- Helper lemmas accumulate and get reused
- **Sorries decrease over time** (trend toward zero)
- **Axioms decrease over time** (or stay at zero)
- Proofs build on mathlib, not custom axioms
- Using LSP server or delegating to subagents for mechanical tasks
- **Claiming "done" only when sorries/axioms are eliminated**

**Red flags 🚩:**
- Multiple compilation errors accumulating
- **Sorries multiply faster than they're filled**
- **Claiming work is "complete" when sorries/axioms remain**
- **Treating sorries as "good enough" for infrastructure**
- Fighting with type checker for hours
- Adding custom axioms without concrete elimination plan
- Reproving things mathlib has
- Proofs are monolithic (>100 lines with no structure)
- Sorries justified with "should be in mathlib" or "not blocking"
- **Using `by True := trivial` or similar placeholders**

**ALL red flags mean: Return to systematic approach.**

**Remember:** A theorem that compiles with sorries is **not proved**. It's scaffolding, not a result.

## Reference Files

Detailed reference files for deep dives:

- **`references/lean-phrasebook.md`** - Mathematical English to Lean translations ("observe that...", "it suffices to show...", etc.)
- **`references/mathlib-guide.md`** - Finding lemmas, import organization, naming conventions, search strategies
- **`references/mathlib-style.md`** - Mathlib style conventions, copyright headers, naming, line length, formatting (with pointers to official docs)
- **`references/tactics-reference.md`** - Comprehensive tactics guide, simp deep dive, tactic selection decision trees
- **`references/calc-patterns.md`** - Calc chain patterns after simp, canonical forms, performance optimization for inequality chains
- **`references/domain-patterns.md`** - Analysis, topology, algebra patterns; includes implicit parameter conventions (Pattern 9)
- **`references/measure-theory.md`** - Sub-σ-algebras, conditional expectation, type class management, trimmed measures
- **`references/compilation-errors.md`** - Detailed error explanations, debugging workflows, type class synthesis issues
- **`references/proof-golfing.md`** - Simplifying proofs after compilation, consolidating rewrites, removing boilerplate
- **`references/lean-lsp-server.md`** - Lean LSP server tools, workflows, troubleshooting (for Claude Code users)
- **`references/subagent-workflows.md`** - Subagent delegation patterns, workflows, examples (for Claude Code users)

Load these references as needed when working on specific tasks.
