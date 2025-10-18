---
name: lean4-theorem-proving
description: Systematic approach to developing formal proofs in Lean 4, managing sorries, using mathlib, and building verified mathematics
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

When working as an AI assistant, use `Bash` tool with `find` and `grep` to search mathlib:

**Search mathlib by keyword:**
```bash
# Find files containing specific lemmas (use Read tool after finding)
find .lake/packages/mathlib -name "*.lean" -exec grep -l "keyword1\|keyword2" {} \; | head -10

# Example: Search for pi and iSup lemmas
find .lake/packages/mathlib -name "*.lean" -exec grep -l "pi.*iSup\|iSup.*pi" {} \; | head -5
# Returns:
#   .lake/packages/mathlib/Mathlib/Topology/MetricSpace/HausdorffDimension.lean
#   .lake/packages/mathlib/Mathlib/Topology/MetricSpace/Isometry.lean
#   .lake/packages/mathlib/Mathlib/Topology/MetricSpace/UniformConvergence.lean
```

**Search for specific theorem patterns:**
```bash
# Find conditional expectation + tendsto lemmas
find .lake/packages/mathlib -name "*.lean" -exec grep -l "condExp.*tend\|condExp.*iSup\|Levy\|Lévy" {} \; | head -10
# Returns:
#   .lake/packages/mathlib/Mathlib/Probability/BorelCantelli.lean
#   .lake/packages/mathlib/Mathlib/Probability/Independence/ZeroOne.lean
#   .lake/packages/mathlib/Mathlib/Probability/Martingale/BorelCantelli.lean

# Then use Read tool to examine promising files
```

**Search local project files:**
```bash
# Find uses of specific pattern in local files
grep -n "iSup\|condExp.*tend" Exchangeability/Probability/Martingale.lean | head -15
# Returns line numbers and matching text:
#   180:private lemma iSup_of_antitone_eq {𝔽 : ℕ → MeasurableSpace Ω} (h_antitone : Antitone 𝔽) (k : ℕ)
#   184:    refine iSup₂_le fun n hn => ?_
#   188:    exact @le_iSup₂ (MeasurableSpace Ω) ℕ (fun n => n ≤ k) _ (fun n _ => 𝔽 n) 0 h0k

# Search for definitions of key concepts
grep -n "def.*tailSigma\|def.*shiftInvariant" Exchangeability/DeFinetti/*.lean
```

**Recursive search with context:**
```bash
# Find and show context around matches (±3 lines)
grep -r -A 3 -B 3 "theorem.*ergodic" .lake/packages/mathlib/Mathlib/Dynamics/

# Search for lemma names starting with specific prefix
grep -r "^lemma integral_" .lake/packages/mathlib/Mathlib/MeasureTheory/Integral/
```

**Workflow for finding relevant mathlib lemmas:**
1. **Identify keywords** from your goal (e.g., "condExp", "martingale", "convergence")
2. **Use `find` + `grep -l`** to locate candidate files
3. **Use `Read` tool** to examine the most promising files
4. **Use `grep -n`** to find exact line numbers of relevant lemmas
5. **Import and apply** the lemmas in your proof

**Example workflow:**
```bash
# Step 1: Find files about measure preservation
⏺ Bash(find .lake/packages/mathlib -name "*.lean" -exec grep -l "MeasurePreserving\|measure_preserving" {} \; | head -10)

# Step 2: Read the most relevant file
⏺ Read(.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean)

# Step 3: Find specific lemmas with line numbers
⏺ Bash(grep -n "lemma.*MeasurePreserving.*comp" .lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean)

# Step 4: Read the specific lemma
⏺ Read(.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean, offset=450, limit=20)
```

**Pro tips for search:**
- Use `\|` for OR patterns in grep: `"pattern1\|pattern2"`
- Use `head -N` to limit results to first N matches
- Use `grep -n` to get line numbers (useful for Read tool)
- Use `grep -l` to list files only (faster for broad searches)
- Search for theorem statements, not proofs: `"theorem\|lemma\|def"`
- Include alternative spellings: `"Levy\|Lévy"`, `"sigma\|σ"`

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

### The `simp` Tactic - Deep Dive

**Most powerful and most dangerous tactic in Lean.** Understand before using extensively.

**What `simp` does:**
- Applies a database of `@[simp]` lemmas to rewrite the goal into "normal form"
- Works recursively (applies lemmas until no more match)
- Can solve goals automatically when normal form is trivial

**Basic usage:**
```lean
simp                           -- Use all simp lemmas
simp only [lemma1, lemma2]     -- Use only these lemmas (recommended)
simp [h]                       -- Add hypothesis h to simp set
simp at h                      -- Simplify hypothesis h
simp?                          -- Show which lemmas simp would use (very useful!)
simpa using expr               -- Simplify then apply expr
```

**When to add `@[simp]` attribute:**
```lean
-- ✅ Good simp lemmas (make things simpler):
@[simp] lemma f_zero : f 0 = 1 := ...           -- Evaluation lemma
@[simp] lemma map_id : map id = id := ...        -- Identity lemma
@[simp] lemma union_empty : s ∪ ∅ = s := ...     -- Simplification to normal form

-- ❌ Bad simp lemmas (don't simplify or create loops):
@[simp] lemma reverse_property : f (g x) = g (f x)  -- Not directional
@[simp] lemma expand : x = x + y - y                -- Makes things more complex
```

**Simp normal forms** - Know these patterns:
- Empty set: `s ∩ ∅ → ∅`, `s ∪ ∅ → s`
- Identity: `map id → id`, `f ∘ id → f`
- Logical: `P ∧ True → P`, `P ∨ False → P`
- Numeric: `x + 0 → x`, `x * 1 → x`

**Common pitfalls:**

**1. Simp loops** (infinite recursion):
```lean
-- Bad: These create a loop if both are @[simp]
@[simp] lemma forward : f x = g x
@[simp] lemma backward : g x = f x

-- Fix: Remove @[simp] from one
lemma forward : f x = g x := ...
@[simp] lemma backward : g x = f x := ...
```

**2. Simp makes things worse:**
```lean
-- If simp makes goal more complex, use simp only:
simp only [specific_lemma]

-- Or don't use simp at all:
rw [specific_lemma]
```

**3. Slow simp calls:**
```lean
-- In tight loops or big proofs:
set_option maxHeartbeats 200000  -- Increase timeout

-- Or avoid simp, use rw:
rw [lemma1, lemma2, lemma3]  -- Faster and more explicit
```

**Advanced simp usage:**
```lean
-- Simp with context
simp (config := {contextual := true})  -- Use local hypotheses

-- Show what simp does (debugging)
simp?  -- Prints "Try this: simp only [lemma1, lemma2, ...]"

-- Conditional simp
simp only [lemma] at h  -- Simplify just hypothesis h
```

**When to use `simp` vs alternatives:**
- **Use `simp`:** When goal is obviously true after normalization
- **Use `simp only`:** When you know exactly which lemmas apply (recommended for readability)
- **Use `rw`:** When applying 1-3 specific rewrites
- **Use `simp?`:** When exploring what lemmas would help (then copy the output)

**Measure theory example:**
```lean
-- Instead of:
simp  -- Might apply 50+ lemmas, slow and opaque

-- Prefer:
simp only [cylinder_univ, prefixCylinder_inter, Set.mem_univ]
-- Explicit, fast, reviewable
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

-- Use sparingly - only for lemmas that genuinely simplify
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

## Interactive Exploration and Debugging

### Essential Commands for Understanding Code

**Check types and definitions:**
```lean
#check expr                    -- Show type of expression
#check @theorem                -- Show full type with implicit arguments

#print theorem                 -- Show definition/proof term
#print axioms theorem          -- List all axioms used (should be minimal!)

#eval expr                     -- Evaluate (only for computable terms)
#reduce expr                   -- Reduce to normal form

#where                         -- Show current namespace and section context
```

**Example workflow:**
```lean
-- What's the type of this lemma?
#check measure_iUnion_finset
-- Result: ∀ {α : Type u_1} {m : MeasurableSpace α} (μ : Measure α) ...

-- Show full signature with implicits
#check @measure_iUnion_finset
-- Shows ALL type parameters and instance arguments

-- See the actual proof/definition
#print measure_iUnion_finset

-- Check if it uses any axioms
#print axioms measure_iUnion_finset
-- Should show: propext, quot.sound, Classical.choice (standard mathlib axioms)
```

**Inspect current context:**
```lean
-- In tactic mode:
example (n : ℕ) (h : n > 0) : n ≠ 0 := by
  trace "Current goal: {·}"  -- Print formatted goal
  #check h                    -- Show type of hypothesis
  sorry
```

**Debug instance synthesis:**
```lean
set_option trace.Meta.synthInstance true in
theorem my_theorem : Goal := by
  -- Shows all instance search steps
  apply_instance
```

**Pretty printing options:**
```lean
set_option pp.notation false   -- Show raw terms (no notation)
set_option pp.universes true   -- Show universe levels
set_option pp.implicit true    -- Show all implicit arguments
set_option pp.proofs true      -- Show proof terms (usually large)
```

**Find lemmas by pattern (in proofs):**
```lean
example : goal := by
  exact?         -- Find exact proof in mathlib
  apply?         -- Find applicable lemmas
  rw?            -- Find rewrite lemmas
```

### Common Compilation Errors - Expanded Guide

**Error: "failed to synthesize instance"**
```
type mismatch
  ...
has type
  Measure Ω : Type
but is expected to have type
  IsProbabilityMeasure μ : Prop
```
- **Cause:** Missing type class instance (Lean can't find `IsProbabilityMeasure μ`)
- **Fix:** Add instance explicitly:
  ```lean
  haveI : IsProbabilityMeasure μ := ⟨measure_univ_eq_one⟩
  -- or
  letI : IsProbabilityMeasure μ := inferInstance
  ```
- **Debug:** `set_option trace.Meta.synthInstance true` to see search process

**Error: "maximum recursion depth exceeded"**
```
(deterministic) timeout at 'typeclass', maximum number of heartbeats (20000) reached
```
- **Cause:** Type class loop or very complex instance search
- **Common in:** Nested measure spaces, product σ-algebras
- **Fix 1:** Provide instance manually: `letI := your_instance`
- **Fix 2:** Break inference chain: Use `@lemma (inst := ...)` to pass explicitly
- **Fix 3:** Increase limit: `set_option synthInstance.maxHeartbeats 40000`

**Error: "type mismatch"**
```
application type mismatch
  f x
argument
  x
has type
  ℕ : Type
but is expected to have type
  ℝ : Type
```
- **Cause:** Implicit coercion didn't trigger or wrong type
- **Fix:** Use explicit coercion: `f (x : ℝ)` or `f ↑x`
- **Debug:** `#check x` to see what Lean thinks the type is

**Error: "tactic 'exact' failed, type mismatch"**
```
tactic 'exact' failed, type mismatch
  term has type: P ∧ Q
  goal: Q ∧ P
```
- **Cause:** Proof term has different (but equivalent) type than goal
- **Fix:** Use `apply` to allow unification, or restructure: `⟨h.2, h.1⟩`
- **Alternative:** Add conversion lemma: `rw [and_comm]`

**Error: "unknown identifier"**
```
unknown identifier 'measurability'
```
- **Cause:** Tactic or name not in scope
- **Fix:** Check imports: `import Mathlib.Tactic.Measurability`
- **Common:** Missing `open Tactic` or `import Mathlib.Tactic`

**Error: "equation compiler failed to prove equation lemmas"**
```
failed to prove recursive application is decreasing
```
- **Cause:** Structural recursion not obvious to Lean
- **Fix:** Use `termination_by` clause:
  ```lean
  def my_rec (n : ℕ) : T :=
    ... my_rec (n - 1) ...
  termination_by my_rec n => n
  ```
- **Alternative:** Use well-founded recursion or explicit induction

**Error: "unexpected bound variable"**
```
unexpected bound variable #0
```
- **Cause:** Lambda capture issue or ill-formed term
- **Fix:** Often indicates wrong de Bruijn index - restructure the term
- **Common when:** Building proof terms manually with `Expr` API

**Error: "failed to elaborate term, type mismatch"**
```
failed to elaborate term, unexpected type
```
- **Cause:** Elaboration order issue - Lean can't infer types
- **Fix 1:** Add explicit type annotations: `(x : Type)`
- **Fix 2:** Use `@` to provide all arguments: `@lemma Type _ _ x`
- **Fix 3:** Help with `by exact` or provide more context

**Error: "invalid occurrence of recursive function"**
```
invalid occurrence of recursive function 'foo'
```
- **Cause:** Recursion not in structurally decreasing position
- **Fix:** Restructure to make structural recursion obvious, or prove termination
- **Common in:** Mutual recursion, nested recursion

**Quick debugging workflow:**
```lean
-- Step 1: Check what you have
#check problematic_term

-- Step 2: Check what's expected
-- (Look at error message goal type)

-- Step 3: Show implicit arguments
#check @problematic_term

-- Step 4: Try to build manually
example : goal := by
  refine problematic_term ?_ ?_  -- See what holes remain

-- Step 5: Enable tracing if still stuck
set_option trace.Elab.term true
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
See the "Finding Existing Lemmas" section above for detailed command-line search techniques.

Additional resources:
- Search mathlib docs online: https://leanprover-community.github.io/mathlib4_docs/
- Ask Zulip (search existing threads first): https://leanprover.zulipchat.com/
- Use `exact?` and `apply?` tactics for automatic suggestions

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
