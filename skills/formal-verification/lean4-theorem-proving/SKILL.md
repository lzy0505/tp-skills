---
name: Lean 4 Theorem Proving
description: Systematic approach to developing formal proofs in Lean 4, managing sorries, using mathlib, and building verified mathematics
when_to_use: when working on Lean 4 formalization projects, proving theorems, or developing mathematical libraries
version: 1.0.0
languages: lean
---

# Lean 4 Theorem Proving

## Overview

Lean 4 is an interactive theorem prover. Unlike traditional code, correctness is verified by the type checker—there are no "unit tests." Success means eliminating all `sorry`s and building with clean proofs that use only standard axioms.

**Core principle:** Build incrementally, structure before solving, and trust the type checker.

## When to Use This Skill

Use for ANY Lean 4 development:
- Formalizing mathematical theorems
- Proving properties of algorithms
- Developing verified libraries
- Contributing to mathlib
- Building on top of mathlib

**Especially important when:**
- Working with complex mathematical structures (measure theory, probability, algebra)
- Managing multiple interrelated proofs
- Dealing with type class inference issues
- Converting axioms to proven lemmas

## The Build-First Principle

```
ALWAYS ensure the file compiles before committing
```

**Lean has no runtime tests.** The type checker IS your test suite.

### Build Commands

```bash
# Full project build (check all files)
lake build

# Check specific file
lake env lean Exchangeability/Probability/CondExp.lean

# Clean and rebuild
lake clean && lake build

# Update dependencies (after changing lakefile)
lake update
```

**Before any commit:**
1. Run `lake build` on the full project
2. Verify no new errors introduced
3. Document any remaining `sorry`s with clear comments

## Proof Development Workflow

### Phase 1: Structure Before Solving

**DON'T:** Start writing tactics immediately
**DO:** Understand the goal structure first

```lean
-- ❌ Bad: Jump straight to tactics
lemma my_theorem : P → Q := by
  intro h
  sorry

-- ✅ Good: Structure with clear subgoals
lemma my_theorem : P → Q := by
  intro h
  -- Strategy: Show Q by constructing witness from h
  -- Need: (1) Extract x from h
  --       (2) Show x satisfies Q
  sorry  -- TODO: Extract witness from h.exists
```

**Structure first:**
- Break complex proof into named helper lemmas
- Use `have` statements to structure argument
- Write proof skeleton with documented `sorry`s
- Ensure file compiles with structure in place

**Example of good structuring:**
```lean
lemma main_theorem (h : ComplexHypothesis) : ComplexConclusion := by
  -- Step 1: Reduce to simpler case
  have h_simple : SimplerCase := by
    sorry  -- TODO: Use helper_lemma_1

  -- Step 2: Apply known result
  have h_known : KnownResult := by
    sorry  -- TODO: Apply mathlib_lemma with h_simple

  -- Step 3: Conclude
  sorry  -- TODO: Combine h_simple and h_known
```

### Phase 2: Helper Lemmas First

Complex proofs need infrastructure. Build bottom-up.

**Pattern from successful Lean work:**
1. Identify the "hard part" of proof
2. State it as a separate lemma
3. Prove the lemma independently
4. Use lemma in main proof

```lean
-- Step 1: Identify hard part and state as lemma
private lemma measure_eq_of_fin_marginals_eq_aux
    (h : ∀ n, marginal μ n = marginal ν n) :
    μ (cylinder r C) = ν (cylinder r C) := by
  sorry

-- Step 2: Use in main theorem
theorem measure_eq_of_fin_marginals_eq
    (h : ∀ n, marginal μ n = marginal ν n) :
    μ = ν := by
  ext s hs
  -- Now we have the helper available
  apply measure_eq_of_fin_marginals_eq_aux h
```

**Why this works:**
- Smaller proofs are easier to debug
- Helper lemmas are reusable
- Compilation errors localized
- Can mark helpers as `private` to keep API clean

### Phase 3: Incremental Filling

**The golden rule:** One `sorry` at a time.

```
1. Pick ONE sorry to eliminate
2. Work on ONLY that sorry
3. Get file to compile with that sorry filled
4. Commit with clear message
5. Repeat
```

**Example commit progression:**
```
commit 1: "Add helper lemmas for finite_product_formula_id"
commit 2: "Fill measure_pi_univ_pi lemma"
commit 3: "Complete finite_product_formula_id using helpers"
```

**DON'T:** Try to fill 5 sorries simultaneously
**DO:** Fill one, compile, commit, next

### Phase 4: Managing Type Class Issues

Lean 4 uses aggressive type class inference. This causes issues with sub-structures.

**Common problem: Metavariable hell**
```lean
-- ❌ Problem: Lean can't infer which MeasurableSpace
μ[f | m]  -- Error: can't synthesize instance
```

**Solution patterns:**

**Pattern 1: Explicit instance management**
```lean
-- Declare instances explicitly before use
haveI : IsFiniteMeasure μ := inferInstance
haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
-- Now this works:
μ[f | m]
```

**Pattern 2: Wrapper with frozen instances**
```lean
-- Create wrapper that manages instances
noncomputable def condExpWith
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ m₀)
    (f : Ω → ℝ) : Ω → ℝ := by
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
  exact μ[f | m]
```

**Pattern 3: Use `classical` mode**
```lean
-- At file level for measure theory
noncomputable section
-- Proofs using classical logic
```

## Mathlib Integration

### Finding Existing Lemmas

**DON'T:** Reprove what mathlib provides
**DO:** Search thoroughly first

```bash
# Search mathlib docs
# Visit https://leanprover-community.github.io/mathlib4_docs/

# Search in VS Code with Lean extension
# Ctrl+T (Cmd+T on Mac) - search by name

# Use exact? tactic
example : goal := by
  exact?  -- Suggests mathlib lemmas
```

**Common mathlib modules for formal math:**
- `Mathlib.MeasureTheory.*` - Measure and integration theory
- `Mathlib.Probability.*` - Probability theory
- `Mathlib.Topology.*` - Topological spaces
- `Mathlib.Data.*` - Data structures
- `Mathlib.Algebra.*` - Algebraic structures

### Importing Correctly

```lean
-- Import specific modules
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Measure.MeasureSpace

-- Standard opens
open MeasureTheory Filter Set Function
open scoped MeasureTheory ProbabilityTheory Topology
```

**Import strategy:**
- Start with specific imports (faster compile)
- Add imports as needed
- Don't import `Mathlib` wholesale
- Use `open scoped` for notation

### Naming Conventions (mathlib style)

Follow mathlib conventions for consistency:

```lean
-- Implications: foo_of_bar means bar → foo
lemma integrable_of_bounded : Bounded f → Integrable f μ

-- Equivalences: foo_iff_bar
lemma exchangeable_iff_contractable : Exchangeable X ↔ Contractable X

-- Application: foo_bar means "apply bar to foo"
lemma measure_pi_univ : μ.pi univ = 1

-- Projection: foo_fst, foo_snd
lemma measure_fst : (μ.map Prod.fst) s = μ (s ×ˢ univ)
```

## Managing Axioms and Sorries

### The Axiom Hierarchy

**Acceptable (standard mathlib axioms):**
- `propext` - Propositional extensionality
- `quot.sound` - Quotient soundness
- `choice` - Axiom of choice

**Check with:**
```lean
#print axioms my_theorem
-- Should only show propext, quot.sound, choice
```

**Unacceptable:**
- Custom `axiom` declarations (except temporarily)
- Completed proofs with `sorry`

### Sorry Documentation Strategy

While developing, document every `sorry`:

```lean
lemma complex_theorem : Goal := by
  sorry
  -- TODO: Strategy:
  --   1. Use tower property to reduce to simpler σ-algebra
  --   2. Apply Lévy's upward theorem (needs mathlib import)
  --   3. Identify limit via uniqueness of conditional expectation
  -- Dependencies: Need to prove helper_lemma_1 first
  -- Estimated difficulty: High - requires lattice manipulation
```

**Good sorry documentation includes:**
1. **Strategy**: How to prove it
2. **Dependencies**: What else is needed
3. **Difficulty**: Estimated complexity
4. **Blockers**: What's preventing progress

### Axiom Elimination Pattern

When you have axioms that should be proven:

1. **Document the axiom's purpose**
```lean
/-- Lévy's upward theorem: conditional expectations converge along
    increasing filtrations.

    TODO: Replace with proven lemma using mathlib's
    `MeasureTheory.tendsto_ae_condExp`. -/
axiom condExp_tendsto_iSup : ...
```

2. **Create implementation notes** (separate file)
```markdown
# AXIOM_ELIMINATION_NOTES.md

## condExp_tendsto_iSup

**Current status:** Axiom
**Target:** Proven lemma using mathlib
**Strategy:** Wrap mathlib's `tendsto_ae_condExp` with `Filtration` packaging
**Estimated effort:** 1 hour
```

3. **Replace with proven version**
```lean
-- Delete axiom, add proof
theorem condExp_tendsto_iSup
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_mono : Monotone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ m0)
    (f : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto ... := by
  -- Build filtration structure
  let ℱ : Filtration ℕ m0 := { seq := 𝔽, mono := h_mono, le := h_le }
  -- Apply mathlib
  simpa using MeasureTheory.tendsto_ae_condExp (μ := μ) (ℱ := ℱ) f
```

## Common Patterns in Measure Theory

### Pattern 1: Integrability Proofs

```lean
-- Bounded + measurable + finite measure = integrable
lemma integrable_indicator_comp
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → α} (hX : Measurable X)
    {B : Set α} (hB : MeasurableSet B) :
    Integrable ((Set.indicator B (fun _ => (1 : ℝ))) ∘ X) μ := by
  have h_meas : Measurable _ := (measurable_const.indicator hB).comp hX
  have h_bound : ∀ᵐ ω ∂μ, ‖...‖ ≤ 1 := by
    apply ae_of_all
    intro ω
    by_cases hω : X ω ∈ B <;> simp [hω]
  exact Integrable.of_bound h_meas.aestronglyMeasurable 1 h_bound
```

### Pattern 2: Conditional Expectation Equalities

```lean
-- Use uniqueness via integral identity
lemma condexp_eq_of_integrals_eq
    (h : ∀ s, MeasurableSet[m] s → ∫ ω in s, f ω ∂μ = ∫ ω in s, g ω ∂μ) :
    μ[f | m] =ᵐ[μ] μ[g | m] := by
  apply ae_eq_condExp_of_forall_setIntegral_eq
  -- Fill in conditions
```

### Pattern 3: Sigma Algebra Manipulations

```lean
-- Prove sub-σ-algebra relationships
have hmZ_le : comap Z mβ ≤ mΩ := by
  intro s hs
  obtain ⟨E, hE, rfl⟩ := hs  -- s = Z⁻¹(E)
  exact hZ hE  -- Z⁻¹(E) measurable since Z measurable
```

## Tactics and Automation

### Essential Tactics

```lean
-- Simplification
simp [lemma1, lemma2]  -- Simplify with specific lemmas
simpa using expr        -- Simplify and close goal

-- Case analysis
by_cases h : p          -- Split on decidable proposition
rcases h with ⟨x, hx⟩   -- Destructure exists/and
obtain ⟨x, hx⟩ := h     -- Alternative destructuring syntax

-- Rewriting
rw [lemma]              -- Rewrite left-to-right
rw [← lemma]            -- Rewrite right-to-left

-- Apply and exact
apply lemma             -- Apply lemma, leave subgoals
exact expr              -- Close goal exactly
refine pattern ?_       -- Apply with holes

-- Have and suffices
have h : P := proof     -- Forward reasoning
suffices h : P by proof -- Backward reasoning
```

### Domain-Specific Tactics

```lean
-- Measure theory
measurability           -- Prove measurability goals
apply_instance          -- Find type class instance
infer_instance         -- Alternative instance search

-- Real numbers
linarith                -- Linear arithmetic
positivity              -- Prove positivity
norm_num                -- Normalize numerals

-- Structure
ext x                   -- Extensionality
funext x                -- Function extensionality
congr                   -- Congruence
```

### Adding Automation

```lean
-- Register lemmas for automation
attribute [measurability] measurable_prefixProj takePrefix_measurable
attribute [simp] cylinder_univ prefixCylinder_inter
```

## Commit Message Patterns

Based on successful Lean development:

**Structure commits:**
```
Add helper lemmas for finite_product_formula_id
Structure lintegral→integral conversion with helper lemmas
```

**Progress commits:**
```
Fill measure_pi_univ_pi lemma and document bind_apply_univ_pi
Complete π-λ extension application using ext_of_generate_finite
```

**Breakthrough commits:**
```
🎉 BREAKTHROUGH: Eliminate ENNReal.ofReal product sorry!
MAJOR BREAKTHROUGH: Eliminate Measure.pi_pi sorry!
```

**Fix commits:**
```
Fix all compilation errors - file now compiles with only sorries
Fix linter warning and complete hprob2 proof (modulo AEMeasurable)
```

**Documentation commits:**
```
Enhanced documentation for sorries 2371, 2386, and 2396
Add implementation notes for Lévy convergence theorems
```

**Template:**
```
[Action]: [What] ([Detail])

- Action: Add/Fill/Fix/Complete/Structure/Eliminate
- What: Specific theorem/lemma/module
- Detail: Optional context or strategy
```

## Red Flags - Stop and Reconsider

**If you catch yourself:**
- Adding `sorry` without documentation
- Committing code that doesn't compile
- Copying proof patterns without understanding
- Fighting type class inference (add explicit instances instead)
- Reproving something mathlib likely has (search first)
- Making 5 changes before running `lake build`
- Trying to fill 3 sorries simultaneously
- Using `axiom` without documented elimination plan

**ALL of these mean: STOP. Return to systematic approach.**

## Debugging Type Errors

### Common Type Error Patterns

**Error: "Failed to synthesize instance"**
- **Cause:** Missing type class instance
- **Fix:** Add `haveI : Instance := inferInstance` or explicit proof

**Error: "Type mismatch"**
- **Cause:** Implicit coercion failed or wrong type
- **Fix:** Use explicit coercion or check types with `#check`

**Error: "Tactic 'exact' failed"**
- **Cause:** Proof term doesn't exactly match goal
- **Fix:** Use `apply` instead or add simplification

**Debugging commands:**
```lean
#check expr         -- Show type of expression
#print theorem      -- Show proof term
#print axioms thm   -- List axioms used
set_option trace.Meta.synthInstance true  -- Debug instance search
```

## Project-Specific Patterns

When working on specific mathematical domains:

**Measure Theory:**
- Check file header for necessary opens
- Use `noncomputable section` liberally
- Manage `IsFiniteMeasure` and `SigmaFinite` instances explicitly
- Use `ae_of_all` to convert everywhere statements to a.e.

**Probability Theory:**
- Import `Mathlib.Probability.*` modules
- Use `IsProbabilityMeasure` when applicable
- Filtrations need `Monotone`, `Antitone` proofs
- Conditional independence via `ProbabilityTheory.CondIndep`

**Algebra:**
- Structure instances carefully (ring, field, module)
- Use `ring` tactic for algebraic manipulation
- Check for existing algebraic lemmas in mathlib

## Quality Checklist Before Commit

- [ ] File compiles: `lake env lean <file>`
- [ ] Full project builds: `lake build`
- [ ] All new `sorry`s documented with strategy
- [ ] No new axioms (or axioms documented with elimination plan)
- [ ] Imports are minimal and specific
- [ ] Lemmas follow mathlib naming conventions
- [ ] Public API has docstrings
- [ ] Helper lemmas marked `private` if internal
- [ ] Commit message describes what and why

## Integration with Other Skills

This skill works with:
- `skills/debugging/systematic-debugging` - Debug compilation errors
- `skills/research/tracing-knowledge-lineages` - Understand design decisions
- `skills/problem-solving/*` - Break down complex theorems

## Learning Resources

**Official:**
- Theorem Proving in Lean 4: https://leanprover.github.io/theorem_proving_in_lean4/
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Lean Zulip chat: https://leanprover.zulipchat.com/

**Search strategies:**
```bash
# Find similar proofs in mathlib
grep -r "theorem.*contractable" ~/.elan/toolchains/

# Search mathlib docs online
# Use search box at https://leanprover-community.github.io/mathlib4_docs/

# Ask Zulip
# Search existing threads before posting
```

## Success Metrics

**You're doing it right when:**
- File always compiles after each change
- Each commit advances one specific lemma/theorem
- Helper lemmas accumulate and get reused
- Axioms decrease over time
- Compilation errors are rare and quickly fixed
- Proofs build on mathlib rather than reinventing
- Project builds cleanly with `lake build`

**You're doing it wrong when:**
- Multiple compilation errors accumulate
- Sorries multiply faster than they're filled
- Custom axioms are added without elimination plan
- Fighting with type checker for extended periods
- Proofs are monolithic without structure
- Not running `lake build` before committing
