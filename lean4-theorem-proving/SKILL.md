---
name: lean4-theorem-proving
description: Use when writing Lean 4 proofs, managing sorries/axioms, facing "failed to synthesize instance" or type class errors, or searching mathlib - provides systematic build-first workflow, type class management patterns (haveI/letI), and domain-specific tactics for measure theory, probability, and algebra
---

# Lean 4 Theorem Proving

## Overview

Lean 4 is an interactive theorem prover. Unlike traditional code, correctness is verified by the type checker—there are no "unit tests." Success means eliminating all `sorry`s and building with clean proofs that use only standard axioms.

**Core principle:** Build incrementally, structure before solving, and trust the type checker.

## When to Use This Skill

Use for ANY Lean 4 development across all mathematical domains:
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

## The Build-First Principle

```
ALWAYS ensure the file compiles before committing
```

**Lean has no runtime tests.** The type checker IS your test suite.

### Build Commands

```bash
# Full project build
lake build

# Check specific file
lake env lean MyFile.lean

# Clean and rebuild
lake clean && lake build
```

**Before any commit:**
1. Run `lake build` on the full project
2. Verify no new errors introduced
3. Document any remaining `sorry`s with clear strategy

## Proof Development Workflow

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

**Structure first:** Break into named helpers, use `have` for subgoals, write skeleton with documented sorries, ensure compilation.

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

**When synthesis fails:** Add `haveI : Instance := ...`, use `letI` for let-bound, or `@lemma (inst := your_instance)`.

**Binder order matters:** When working with sub-structures (like `m : MeasurableSpace Ω` with ambient `[MeasurableSpace Ω]`), the parameter `m` must come AFTER all instance parameters to avoid instance resolution choosing the wrong structure.

## Mathlib Integration

### Finding Existing Lemmas

**DON'T:** Reprove what mathlib provides
**DO:** Search thoroughly first

#### In-Editor Search (For Human Users)

```bash
# VS Code with Lean extension:
# Ctrl+T (Cmd+T on Mac) - search by name
# Note: This is for human users in VS Code, not available to AI assistants

# Use exact? tactic in proofs
example : goal := by
  exact?  -- Suggests mathlib lemmas that directly prove the goal
```

#### Command-Line Search (For AI Assistants and Power Users)

```bash
# Find files containing specific patterns
find .lake/packages/mathlib -name "*.lean" -exec grep -l "pattern1\|pattern2" {} \; | head -10

# Search with line numbers (for Read tool)
grep -n "lemma.*keyword" path/to/file.lean | head -15
```

**Workflow:** Identify keywords → `find` + `grep -l` → `Read` tool → `grep -n` for line numbers → Import and apply

**Pro tips:** Use `\|` for OR patterns, `head -N` to limit, search `"theorem\|lemma\|def"`, include alternative spellings.

### Importing Correctly

```lean
-- Specific imports (preferred)
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic

-- Tactic imports when needed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
```

### Naming Conventions (mathlib style)

```lean
-- Implications: bar_of_foo means foo → bar
lemma continuous_of_isOpen_preimage : (∀ U, IsOpen (f ⁻¹' U)) → Continuous f

-- Equivalences: foo_iff_bar
lemma injective_iff_leftInverse : Injective f ↔ ∃ g, LeftInverse g f
```

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

### Elimination Pattern

```lean
-- 1. Start with axiom
axiom key_lemma : Goal  -- TODO: Replace with mathlib's result_X

-- 2. Find infrastructure
#check mathlib_result

-- 3. Replace with proof
theorem key_lemma : Goal := by exact mathlib_result ...
```

## Domain-Specific Patterns

### Analysis & Topology

```lean
-- Integrability: bounded + measurable + finite = integrable
lemma integrable_of_bounded_measurable [IsFiniteMeasure μ] {f : X → ℝ}
    (h_meas : Measurable f) (h_bound : ∃ C, ∀ x, ‖f x‖ ≤ C) : Integrable f μ := by
  obtain ⟨C, hC⟩ := h_bound
  exact Integrable.of_bound h_meas.aestronglyMeasurable C (ae_of_all _ hC)

-- Continuity from preimage
lemma continuous_of_preimage (h : ∀ U, IsOpen U → IsOpen (f ⁻¹' U)) :
    Continuous f := by rw [continuous_def]; exact h

-- Tactics: continuity, fun_prop
-- Patterns: Compactness via finite subcover, limits via Filter API, ε-δ proofs
```

### Algebra

```lean
-- Build instances compositionally
instance : CommRing (Polynomial R) := inferInstance

-- Structure lemmas
lemma quotient_ring_hom (I : Ideal R) : RingHom (R ⧸ I) := by
  refine { toFun := ..., map_one' := ..., map_mul' := ... }

-- Tactics: ring, field_simp, group
-- Patterns: Morphisms with refine, quotients via Quotient.sound, universal properties
```

### Number Theory & Combinatorics

```lean
-- Induction principles
lemma property_of_list (l : List α) : P l := by
  induction l with
  | nil => sorry  -- Base case
  | cons head tail ih => sorry  -- Use ih

-- Tactics: linarith, norm_num
-- Patterns: Divisibility via Nat.dvd_iff_mod_eq_zero, prime factorization, Fintype.card
```

### Probability & Measure Theory

```lean
-- Manage instances explicitly
[IsProbabilityMeasure μ] -- Declare at function level
haveI : IsFiniteMeasure μ := ⟨measure_univ_lt_top⟩  -- Add in proof

-- Tactics: positivity, measurability
-- Patterns: ae_of_all for ∀ → a.e., filtrations need Monotone, uniqueness via integral identity
```

### General Patterns

```lean
-- Equality via uniqueness
lemma foo_eq_bar (h : ∀ x, property x → f x = g x) : f = g := by
  ext x; apply h  -- Show x satisfies property
```

## Tactics and Automation

### Essential Tactics

```lean
-- Simplification
simp only [lem1, lem2]  -- Explicit (preferred)
simpa using expr         -- Simplify and close

-- Case analysis
by_cases h : p           -- Split on decidable
rcases h with ⟨x, hx⟩    -- Destructure exists/and

-- Rewriting
rw [lemma]               -- Rewrite left-to-right
rw [← lemma]             -- Rewrite right-to-left

-- Apply
apply lemma              -- Apply, leave subgoals
exact expr               -- Close goal exactly
refine pattern ?_        -- Apply with holes

-- Extension & congruence
ext x / funext x / congr
```

### The `simp` Tactic

**What it does:** Applies `@[simp]` lemmas recursively to normal form

**Usage:** `simp` | `simp only [lem1, lem2]` (preferred) | `simp?` (shows which lemmas)

**When to add `@[simp]`:**
```lean
-- ✅ Good: Makes simpler
@[simp] lemma f_zero : f 0 = 1
@[simp] lemma union_empty : s ∪ ∅ = s

-- ❌ Bad: Creates loops or makes complex
@[simp] lemma reverse : f (g x) = g (f x)  -- Loop with reverse direction!
```

**Decision tree:** Use `simp` for obvious normalization, `simp only` when you know lemmas, `rw` for 1-3 rewrites, `simp?` for exploration.

## Interactive Exploration

### Essential Commands

```lean
#check expr                    -- Show type
#check @theorem                -- Show with all implicit arguments
#print theorem                 -- Show definition/proof
#print axioms theorem          -- List axioms used
#eval expr                     -- Evaluate (computable only)

-- In tactic mode
trace "Current goal: {·}"

-- Debug instance synthesis
set_option trace.Meta.synthInstance true in
theorem my_theorem : Goal := by apply_instance

-- Find lemmas
example : goal := by
  exact?         -- Find exact proof in mathlib
  apply?         -- Find applicable lemmas
  rw?            -- Find rewrite lemmas
```

### Common Compilation Errors

| Error | Cause | Fix |
|-------|-------|-----|
| **"failed to synthesize instance"** | Missing type class | Add `haveI : IsProbabilityMeasure μ := ⟨proof⟩` |
| **"maximum recursion depth"** | Type class loop/complex search | Provide manually: `letI := instance` or increase: `set_option synthInstance.maxHeartbeats 40000` |
| **"type mismatch"** (has type ℕ but expected ℝ) | Wrong type | Use coercion: `(x : ℝ)` or `↑x` |
| **"tactic 'exact' failed"** | Goal/term type mismatch | Use `apply` for unification or restructure: `⟨h.2, h.1⟩` |
| **"unknown identifier 'ring'"** | Missing import | Add: `import Mathlib.Tactic.Ring` |
| **"equation compiler failed"** | Can't prove termination | Add `termination_by my_rec n => n` clause |

**Quick debug:** `#check problematic_term` → `#check @problematic_term` → `refine problematic_term ?_ ?_`

## Quality Signals

### Before Commit Checklist

- [ ] File compiles: `lake env lean <file>`
- [ ] Full project builds: `lake build`
- [ ] All new `sorry`s documented with strategy
- [ ] No new axioms (or documented with elimination plan)
- [ ] Imports minimal and specific
- [ ] Lemmas follow mathlib naming conventions
- [ ] Public API has docstrings
- [ ] Helper lemmas marked `private` if internal

### Doing It Right ✅

- File always compiles after each change
- Each commit advances one specific lemma
- Helper lemmas accumulate and get reused
- Axioms decrease over time
- Compilation errors rare and quickly fixed
- Proofs build on mathlib

### Red Flags 🚩 - STOP and Reconsider

- Multiple compilation errors accumulating
- Sorries multiply faster than they're filled
- Fighting with type checker for hours
- Adding custom axioms without plan
- Reproving things mathlib has
- Proofs are monolithic (>100 lines with no structure)

**ALL red flags mean: Return to systematic approach.**
