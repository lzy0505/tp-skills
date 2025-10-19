---
name: lean4-theorem-proving
description: Systematic approach to developing formal proofs in Lean 4, managing sorries, using mathlib, and building verified mathematics
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

**Especially important when:**
- Managing multiple interrelated proofs
- Dealing with type class inference issues
- Converting axioms to proven lemmas
- Working with complex mathematical structures

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
  -- Need: (1) Extract x from h
  --       (2) Show x satisfies Q
  have h_extract : Extract := sorry  -- TODO: Use helper_lemma_1
  have h_property : Property := sorry  -- TODO: Apply known_result
  sorry  -- TODO: Combine above
```

**Structure first:**
- Break complex proof into named helper lemmas
- Use `have` statements to structure argument
- Write proof skeleton with documented `sorry`s
- Ensure file compiles with structure in place

### Phase 2: Helper Lemmas First

Build infrastructure bottom-up. Extract reusable components:

```lean
-- Extract helpers that appear multiple times
private lemma helper_step (x : X) : Property x := sorry

-- Then use in main proof
theorem main : Result := by
  have h1 := helper_step x
  have h2 := helper_step y
  -- Combine h1 and h2
```

### Phase 3: Incremental Filling

**One sorry at a time:**
1. Choose ONE sorry to fill
2. Fill it completely (no new sorries in the proof)
3. Compile and verify
4. Commit with descriptive message
5. Repeat

### Phase 4: Managing Type Class Issues

**Sub-structures need explicit instances:**

```lean
-- ❌ Common error: Lean can't synthesize instance
have h_le : m ≤ m0 := ...
-- Later: "Failed to synthesize MeasurableSpace Ω"

-- ✅ Fix: Provide instance explicitly
have h_le : m ≤ m0 := ...
haveI : MeasurableSpace Ω := m0  -- Explicit instance
-- OR use Fact:
haveI : Fact (m ≤ m0) := ⟨h_le⟩
```

**When type class synthesis fails:**
- Add `haveI : Instance := ...` before the problematic line
- Use `letI` for `let`-bound instances
- Use `@lemma (inst := your_instance)` to pass explicitly

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

Use `Bash` tool with `find` and `grep` to search mathlib:

```bash
# Find files containing specific patterns
find .lake/packages/mathlib -name "*.lean" -exec grep -l "pattern1\|pattern2" {} \; | head -10

# Search with line numbers (for Read tool)
grep -n "lemma.*keyword" path/to/file.lean | head -15

# Then use Read tool to examine files
```

**Workflow:**
1. Identify keywords from goal
2. Use `find` + `grep -l` to locate candidate files
3. Use `Read` tool to examine promising files
4. Use `grep -n` for exact line numbers
5. Import and apply the lemmas

**Pro tips:**
- Use `\|` for OR patterns: `"pattern1\|pattern2"`
- Use `head -N` to limit results
- Use `grep -n` for line numbers
- Search theorem statements: `"theorem\|lemma\|def"`
- Include alternative spellings: `"Levy\|Lévy"`

### Importing Correctly

```lean
-- Specific imports (preferred)
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Group.Defs

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

-- Projections: foo_bar means access field bar of foo
lemma group_mul : (G : Group) → G.mul ...
```

## Managing Axioms and Sorries

### The Axiom Hierarchy

**Standard mathlib axioms (acceptable):**
- `Classical.choice`
- `propext`
- `quot.sound`

Check with: `#print axioms my_theorem`

**Custom axioms (must have elimination plan):**

```lean
-- ❌ Bad: Axiom with no plan
axiom my_conjecture : P

-- ✅ Good: Documented axiom with elimination strategy
axiom helper_theorem : P
-- TODO: Strategy: Prove using technique X
--       Dependencies: Need lemmas A, B from mathlib
--       Estimated effort: 2 days
```

### Sorry Documentation Strategy

**Every sorry needs:**
1. **What** needs to be proved
2. **How** to prove it (strategy)
3. **Dependencies** (what's blocking)

```lean
-- ✅ Good documentation
have h : Complex_Goal := by
  sorry
  -- TODO: Strategy:
  --   (1) Apply monotone convergence theorem
  --   (2) Show f_n ≤ f_{n+1} using h_mono
  --   (3) Show bound using h_bound
  -- Dependencies: Need `tendsto_lintegral_of_monotone` from mathlib
  -- Estimated effort: 2 hours
```

### Axiom Elimination Pattern

```lean
-- 1. Start with axiom (document plan)
axiom key_lemma : Goal
-- TODO: Replace with proof using mathlib's result_X

-- 2. Find mathlib infrastructure
#check mathlib_result  -- Found relevant lemma

-- 3. Replace with proven version
theorem key_lemma : Goal := by
  exact mathlib_result ...
```

## Common Proof Patterns

### Pattern 1: Integrability (Analysis/Probability)

```lean
-- Bounded + measurable + finite = integrable
lemma integrable_of_bounded_measurable
    [IsFiniteMeasure μ] {f : X → ℝ}
    (h_meas : Measurable f)
    (h_bound : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := h_bound
  exact Integrable.of_bound h_meas.aestronglyMeasurable C (ae_of_all _ hC)
```

### Pattern 2: Algebraic Structure (Algebra)

```lean
-- Build instances compositionally
instance : CommRing (Polynomial R) := inferInstance

-- Use structure lemmas
lemma quotient_ring_hom (I : Ideal R) :
    RingHom (R ⧸ I) := by
  refine { toFun := ..., map_one' := ..., map_mul' := ... }
  -- Fill in each field
```

### Pattern 3: Topological Properties (Topology)

```lean
-- Continuity from preimage criterion
lemma continuous_of_preimage
    (h : ∀ U, IsOpen U → IsOpen (f ⁻¹' U)) :
    Continuous f := by
  rw [continuous_def]
  exact h

-- Compactness via finite subcover
lemma compact_of_finite_subcover
    (h : ∀ 𝓤, ... → ∃ 𝓣 ⊆ 𝓤, Finite 𝓣 ∧ ...) :
    IsCompact K := ...
```

### Pattern 4: Equality via Uniqueness (General)

```lean
-- Prove equality by showing both satisfy uniqueness criterion
lemma foo_eq_bar
    (h : ∀ x, property x → f x = g x) :
    f = g := by
  ext x
  apply h
  -- Show x satisfies property
```

### Pattern 5: Inductive Constructions (General)

```lean
-- Use mathlib's induction principles
lemma property_of_list (l : List α) : P l := by
  induction l with
  | nil => sorry  -- Base case
  | cons head tail ih => sorry  -- Inductive step using ih
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
```

### The `simp` Tactic - Deep Dive

**What `simp` does:** Applies `@[simp]` lemmas recursively to rewrite goal into normal form

**Basic usage:**
```lean
simp                           -- Use all simp lemmas
simp only [lem1, lem2]         -- Use only these (recommended for clarity)
simp?                          -- Show which lemmas applied (very useful!)
```

**When to add `@[simp]`:**
```lean
-- ✅ Good: Makes things simpler
@[simp] lemma f_zero : f 0 = 1
@[simp] lemma map_id : map id = id
@[simp] lemma union_empty : s ∪ ∅ = s

-- ❌ Bad: Not directional or makes complex
@[simp] lemma reverse : f (g x) = g (f x)  -- Creates loops
@[simp] lemma expand : x = x + y - y       -- Makes worse
```

**Common pitfalls:**
- **Simp loops:** Don't make both `f x = g x` and `g x = f x` simp lemmas
- **Slow simp:** In big proofs, use `rw [lem1, lem2]` instead
- **Opaque simp:** Use `simp only` or `simp?` for reviewability

**Decision tree:**
- **Use `simp`:** When goal obviously true after normalization
- **Use `simp only [...]`:** When you know which lemmas apply (preferred)
- **Use `rw`:** When applying 1-3 specific rewrites
- **Use `simp?`:** When exploring (then copy the output)

### Domain-Specific Tactics

```lean
-- Analysis/Topology
continuity              -- Prove continuity goals
fun_prop                -- Prove function properties

-- Algebra
ring                    -- Solve ring equations
field_simp              -- Simplify field expressions
group                   -- Group theory simplification

-- Real numbers
linarith                -- Linear arithmetic
positivity              -- Prove positivity
norm_num                -- Normalize numerals

-- General
ext x                   -- Extensionality
funext x                -- Function extensionality
congr                   -- Congruence
```

## Interactive Exploration and Debugging

### Essential Commands

```lean
#check expr                    -- Show type
#check @theorem                -- Show with all implicit arguments
#print theorem                 -- Show definition/proof
#print axioms theorem          -- List axioms used (should be minimal!)
#eval expr                     -- Evaluate (computable only)
#where                         -- Show namespace/context
```

**Workflow example:**
```lean
-- What's the type?
#check measure_iUnion_finset
-- Show all parameters
#check @measure_iUnion_finset
-- See definition
#print measure_iUnion_finset
-- Check axioms
#print axioms measure_iUnion_finset
```

**In tactic mode:**
```lean
example (n : ℕ) (h : n > 0) : n ≠ 0 := by
  trace "Current goal: {·}"
  sorry
```

**Debug instance synthesis:**
```lean
set_option trace.Meta.synthInstance true in
theorem my_theorem : Goal := by
  apply_instance  -- Shows all instance search steps
```

**Find lemmas:**
```lean
example : goal := by
  exact?         -- Find exact proof in mathlib
  apply?         -- Find applicable lemmas
  rw?            -- Find rewrite lemmas
```

### Common Compilation Errors

**"failed to synthesize instance"**
```
type mismatch: IsProbabilityMeasure μ not found
```
- **Fix:** Add `haveI : IsProbabilityMeasure μ := ⟨proof⟩`
- **Debug:** `set_option trace.Meta.synthInstance true`

**"maximum recursion depth exceeded"**
```
timeout at 'typeclass'
```
- **Cause:** Type class loop or complex search
- **Fix:** Provide instance manually with `letI := instance`
- **Or:** Increase limit: `set_option synthInstance.maxHeartbeats 40000`

**"type mismatch"**
```
has type ℕ but expected ℝ
```
- **Fix:** Use explicit coercion: `(x : ℝ)` or `↑x`
- **Debug:** `#check x` to see actual type

**"tactic 'exact' failed"**
```
term has type P ∧ Q but goal is Q ∧ P
```
- **Fix:** Use `apply` for unification, or `⟨h.2, h.1⟩`

**"unknown identifier"**
```
unknown identifier 'ring'
```
- **Fix:** Add import: `import Mathlib.Tactic.Ring`

**"equation compiler failed"**
```
failed to prove recursive application is decreasing
```
- **Fix:** Add `termination_by` clause:
  ```lean
  def my_rec (n : ℕ) : T :=
    ... my_rec (n - 1) ...
  termination_by my_rec n => n
  ```

**Quick debugging workflow:**
```lean
-- 1. Check what you have
#check problematic_term
-- 2. Show implicit arguments
#check @problematic_term
-- 3. Try to build manually
example : goal := by
  refine problematic_term ?_ ?_  -- See what holes remain
```

## Domain-Specific Patterns

**Analysis & Topology:**
- Use `noncomputable section` for non-constructive proofs
- Compactness arguments via finite subcover
- Continuity from ε-δ or preimage criterion
- Limits via Filter API

**Algebra:**
- Structure instances compositionally
- Use `ring`, `field_simp`, `group` tactics
- Build morphisms with `refine { toFun := ..., ... }`
- Quotients via `Quotient.sound` and universal properties

**Number Theory & Combinatorics:**
- Induction on natural numbers
- Divisibility via `Nat.dvd_iff_mod_eq_zero`
- Prime factorization lemmas in mathlib
- Combinatorial counting with `Fintype.card`

**Probability & Measure Theory:**
- Manage `IsFiniteMeasure`, `IsProbabilityMeasure` instances explicitly
- Use `ae_of_all` to convert ∀ to almost everywhere
- Filtrations need `Monotone`/`Antitone` proofs
- Conditional expectation uniqueness via integral identity

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

## Red Flags - Stop and Reconsider

**You're going off track if:**
- Multiple compilation errors accumulating
- Sorries multiply faster than they're filled
- Fighting with type checker for hours
- Adding custom axioms without plan
- Proofs are monolithic (>100 lines with no structure)

**ALL of these mean: STOP. Return to systematic approach.**

## Success Metrics

**You're doing it right when:**
- File always compiles after each change
- Each commit advances one specific lemma
- Helper lemmas accumulate and get reused
- Axioms decrease over time
- Compilation errors are rare and quickly fixed
- Proofs build on mathlib
- Project builds cleanly with `lake build`

**You're doing it wrong when:**
- Not running `lake build` before committing
- Reproving things mathlib has
- Using `axiom` without elimination plan
