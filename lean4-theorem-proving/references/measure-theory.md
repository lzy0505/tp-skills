# Measure Theory Reference

Deep patterns and pitfalls for measure theory and probability in Lean 4.

**When to use this reference:**
- Working with sub-σ-algebras and conditional expectation
- Hitting type class synthesis errors with measures
- Managing measurable space structures and trimmed measures
- Debugging "failed to synthesize instance" errors in measure theory

## Type Class Instance Management for Sub-σ-Algebras

### Critical: Binder Order Matters

When working with a sub-σ-algebra `m ≤ m₀`, the parameter order in function signatures is crucial:

```lean
-- ❌ WRONG: m before instance parameters causes instance resolution issues
lemma my_lemma
    {Ω : Type*} [MeasurableSpace Ω]  -- Instance
    (m : MeasurableSpace Ω)            -- Plain parameter BEFORE instance params
    {μ : Measure Ω} [IsProbabilityMeasure μ]  -- More instances
    (hm : m ≤ ‹MeasurableSpace Ω›) :
    Result := by
  -- Lean chooses m instead of ambient instance!
  sorry

-- ✅ CORRECT: ALL instance parameters first, THEN plain parameters
lemma my_lemma
    {Ω : Type*} [inst : MeasurableSpace Ω]  -- Named instance
    {μ : Measure Ω} [IsProbabilityMeasure μ]  -- All instances first
    (m : MeasurableSpace Ω)  -- Plain parameter AFTER all instances
    (hm : m ≤ inst) :        -- Reference named instance
    Result := by
  -- Now instance resolution works correctly
  sorry
```

**Why this matters:**
- When `m` appears before instance parameters, `‹MeasurableSpace Ω›` resolves to `m` instead of the ambient instance
- This causes type class synthesis to choose the wrong structure
- Results in errors like "has type @MeasurableSet Ω m B but expected @MeasurableSet Ω inst B"

### Pitfall: Anonymous Instance Notation `‹_›` with Sub-σ-Algebras

When working with sub-σ-algebras, **never use `‹_›` for the ambient space**—it resolves incorrectly:

```lean
-- ❌ WRONG: Anonymous instance resolves to m instead of ambient space!
lemma bad_example [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)  -- ‹_› becomes m, so hm : m ≤ m
    : Result := by
  sorry  -- Type class errors: "failed to synthesize instance"

-- ✅ CORRECT: Make ambient space explicit
lemma good_example {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- Now hm : m ≤ m₀ is meaningful
    : Result := by
  -- Provide instances explicitly before calling mathlib
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
  sorry
```

**The bug:** `hm : m ≤ ‹_›` gave you `hm : m ≤ m` because Lean picked the most recent `MeasurableSpace Ω` in scope (which was `m` itself).

**The fix:** Explicit `m₀` parameter gives meaningful `hm : m ≤ m₀` and avoids instance resolution failures.

## The condExpWith Pattern for Conditional Expectation

### The Problem It Solves

When working with conditional expectation on sub-σ-algebras, you often have:
- An ambient measurable space structure on Ω
- A sub-σ-algebra `m` that's smaller: `m ≤ (ambient structure)`
- A measure `μ` on the ambient space
- Need to compute `μ[f|m]` (conditional expectation with respect to `m`)

**Challenge:** Lean needs to know about both measurable space structures simultaneously, and type class inference can get confused.

### The Anti-Pattern (What NOT to do)

```lean
lemma my_condexp_lemma
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)  -- ❌ WRONG!
    {f : Ω → ℝ} ... :
    μ[f|m] = ... := by
  ...
```

**Problem:** The anonymous instance notation `‹_›` gets resolved incorrectly. Lean resolves it to `m` itself, giving you `hm : m ≤ m`, which is useless! This causes type class synthesis failures like:
```
error: typeclass instance problem is stuck
  IsFiniteMeasure ?m.104
```

### The condExpWith Pattern (Correct Approach)

The canonical solution from real codebases:

```lean
def condExpWith {Ω : Type*} {m₀ : MeasurableSpace Ω}  -- ✅ Explicit ambient space
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- ✅ Explicit sub-algebra relation
    (f : Ω → ℝ) : Ω → ℝ := by
  -- Inside the function body, provide instances explicitly:
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm

  exact condExp m μ f  -- Now type class resolution works!
```

### Key Principles

1. **Make the ambient measurable space explicit:**
   ```lean
   {m₀ : MeasurableSpace Ω}  -- Name it explicitly
   ```

2. **Use explicit inequality:**
   ```lean
   (hm : m ≤ m₀)  -- Not hm : m ≤ ‹_›
   ```

3. **Provide trimmed measure instances with `haveI`:**
   ```lean
   haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
   haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
   ```

### Why It Works

- **Explicit `m₀`:** Lean now knows there are TWO distinct measurable spaces in play
- **`hm : m ≤ m₀`:** The relationship is unambiguous
- **`haveI`:** Adds instances to the local type class context before calling mathlib lemmas
- **Trimmed measure:** Many conditional expectation lemmas need instances on `μ.trim hm`, not just `μ`

### Real Example: condExp_mul_pullout

**Before (broken):**
```lean
lemma condExp_mul_pullout
    {m : MeasurableSpace Ω} (hm : m ≤ ‹_›)  -- ❌
    ... := by
  exact condExp_stronglyMeasurable_mul_of_bound hm ...
  -- Error: IsFiniteMeasure ?m.104
```

**After (fixed):**
```lean
lemma condExp_mul_pullout {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- ✅
    ... := by
  haveI : IsFiniteMeasure μ := inferInstance
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm

  exact condExp_stronglyMeasurable_mul_of_bound hm ...
  -- ✅ Works!
```

## Explicit Instance Declarations

When Lean can't synthesize required instances automatically, provide them explicitly:

```lean
haveI : IsFiniteMeasure μ := inferInstance
haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
-- Now conditional expectation works:
μ[f | m]
```

## Measurability Lifting Between Structures

When you have a set measurable in the sub-algebra, lift to ambient space:

```lean
-- When you have s measurable in m, lift to ambient m₀
have hs_m : MeasurableSet[m] s := ...
have hs_m₀ : MeasurableSet[m₀] s := hm _ hs_m  -- hm : m ≤ m₀
```

## Quick Reference

**When working with sub-σ-algebras in Lean 4:**
- ✅ DO: Make ambient space explicit `{m₀ : MeasurableSpace Ω}`
- ✅ DO: Use `haveI` for trimmed measure instances
- ✅ DO: Put all instance parameters before plain parameters
- ❌ DON'T: Use `‹_›` for the ambient measurable space
- ❌ DON'T: Put plain measurable space parameters before instance parameters
- 📚 PATTERN: Use the condExpWith pattern as template for conditional expectation work

## Common Error Messages

**"typeclass instance problem is stuck"**
→ Provide instances explicitly with `haveI` before calling mathlib

**"has type @MeasurableSet Ω m B but expected @MeasurableSet Ω m₀ B"**
→ Check binder order: all instance parameters must come before plain parameters

**"failed to synthesize instance IsFiniteMeasure ?m.104"**
→ Make ambient space explicit and provide trimmed measure instances

## TL;DR

When working with sub-σ-algebras and conditional expectation:
1. **Make ambient space explicit:** `{m₀ : MeasurableSpace Ω}`
2. **Never use `‹_›`** for ambient space (it resolves incorrectly)
3. **Use `haveI`** to provide trimmed measure instances
4. **Correct binder order:** All instances first, then plain parameters
5. **Follow condExpWith pattern** for conditional expectation work

This prevents type class inference failures and is essential for any serious work with conditional expectation in Lean 4.
