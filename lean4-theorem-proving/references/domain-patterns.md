# Domain-Specific Patterns for Lean 4

This reference provides detailed patterns, tactics, and common approaches for different mathematical domains in Lean 4 formalization.

## Measure Theory & Probability

### Core Patterns

#### Pattern 1: Proving Integrability

**The golden rule:** `bounded + measurable + finite measure = integrable`

```lean
lemma integrable_of_bounded_measurable
    [IsFiniteMeasure μ] {f : X → ℝ}
    (h_meas : Measurable f)
    (h_bound : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := h_bound
  exact Integrable.of_bound h_meas.aestronglyMeasurable C (ae_of_all _ hC)
```

**Variations:**

```lean
-- When bound is ae (almost everywhere)
lemma integrable_of_ae_bounded
    [IsFiniteMeasure μ] {f : X → ℝ}
    (h_meas : AEMeasurable f μ)
    (h_bound : ∃ C, ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := h_bound
  exact Integrable.of_bound h_meas C hC

-- When using indicator functions
lemma integrable_indicator
    {A : Set X} (hA : MeasurableSet A) {f : X → ℝ}
    (hf : Integrable f μ) :
    Integrable (A.indicator f) μ :=
  hf.indicator hA
```

#### Pattern 2: Conditional Expectation Equality

**Use the uniqueness theorem:**

```lean
-- To show μ[f | m] = g, prove:
-- 1. g is m-measurable
-- 2. g is integrable
-- 3. For all m-measurable sets B: ∫ x in B, g x ∂μ = ∫ x in B, f x ∂μ

lemma condExp_eq_of_integral_eq
    {f g : Ω → ℝ} (hf : Integrable f μ)
    (hg_meas : Measurable[m] g)
    (hg_int : Integrable g μ)
    (h_eq : ∀ s, MeasurableSet[m] s → ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ) :
    μ[f | m] =ᵐ[μ] g := by
  symm
  exact ae_eq_condExp_of_forall_setIntegral_eq (μ := μ) (m := m) hm
    hf hg_meas hg_int h_eq
```

**Common applications:**

```lean
-- Conditional expectation of indicator
lemma condExp_indicator_eq (hA : MeasurableSet[m₀] A) :
    μ[A.indicator (fun _ => (1 : ℝ)) | m] =ᵐ[μ] condProb μ m A := by
  -- Prove via uniqueness: both are m-measurable, integrable,
  -- and have same integral on all m-measurable sets
  sorry
```

#### Pattern 3: Sub-σ-Algebras and Type Class Management

**Critical issues when working with sub-σ-algebras:**
- Binder order matters: instance parameters must come before plain parameters
- Never use `‹_›` for the ambient space (resolves incorrectly)
- Provide trimmed measure instances explicitly with `haveI`
- Follow the condExpWith pattern for conditional expectation

**Quick example:**
```lean
-- ✅ Correct pattern
lemma my_condexp_lemma {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)  -- Explicit ambient space
    : Result := by
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
  -- Now call mathlib lemmas
```

**For complete coverage of sub-σ-algebra patterns, conditional expectation, and debugging type class synthesis errors, see:** `references/measure-theory.md`

#### Pattern 4: Almost Everywhere Properties

**From universal to ae:**

```lean
-- Use ae_of_all
have h : ∀ x, P x := ...
have h_ae : ∀ᵐ x ∂μ, P x := ae_of_all _ h
```

**Combining ae properties:**

```lean
-- Use filter_upwards
have h1 : ∀ᵐ x ∂μ, P x := ...
have h2 : ∀ᵐ x ∂μ, Q x := ...
filter_upwards [h1, h2] with x hP hQ
-- Now have: ∀ᵐ x ∂μ, P x ∧ Q x
```

**ae equality reasoning:**

```lean
-- Transitivity
have h1 : f =ᵐ[μ] g := ...
have h2 : g =ᵐ[μ] h := ...
have : f =ᵐ[μ] h := h1.trans h2

-- Substitution
have h : f =ᵐ[μ] g := ...
have hf : Integrable f μ := ...
have hg : Integrable g μ := hf.congr h
```

#### Pattern 5: Filtrations and Increasing σ-Algebras

```lean
-- Define filtration
def Filtration (f : ℕ → MeasurableSpace Ω) : Prop :=
  Monotone f ∧ ∀ n, f n ≤ m₀

-- Use in adapted processes
def Adapted (X : ℕ → Ω → ℝ) (f : ℕ → MeasurableSpace Ω) : Prop :=
  ∀ n, Measurable[f n] (X n)

-- Martingale property with conditional expectation
def IsMartingale (X : ℕ → Ω → ℝ) (f : ℕ → MeasurableSpace Ω) : Prop :=
  Adapted X f ∧
  (∀ n, Integrable (X n) μ) ∧
  ∀ m n, m ≤ n → μ[X n | f m] =ᵐ[μ] X m
```

#### Pattern 6: Product Measures and Independence

```lean
-- Product measure on ℕ → α
variable (ν : Measure α) [IsProbabilityMeasure ν]

-- Infinite product exists via Ionescu-Tulcea
noncomputable def productMeasure : Measure (ℕ → α) :=
  Measure.pi (fun _ => ν)

-- Independence via product structure
lemma independent_of_product :
    ∀ n m, n ≠ m →
    IndepFun (fun ω => ω n) (fun ω => ω m) (productMeasure ν) := by
  sorry
```

#### Pattern 7: Managing Section Variables with `omit`

When organizing files with `section` and `variable`, you may need to exclude certain section variables from specific lemmas:

```lean
section IntegrationHelpers

variable [MeasurableSpace Ω] {μ : Measure Ω}

-- Most lemmas use the section variables
lemma uses_measure [IsFiniteMeasure μ] : ... := by
  -- Uses μ and MeasurableSpace Ω from section
  sorry

-- This lemma doesn't need MeasurableSpace Ω at all
omit [MeasurableSpace Ω] in
/-- **Cauchy-Schwarz inequality for L² real-valued functions.**

    For integrable functions f, g in L²(μ): |∫ f·g| ≤ (∫ f²)^(1/2) · (∫ g²)^(1/2) -/
lemma abs_integral_mul_le_L2 [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (∫ x, f x ^ 2 ∂μ) ^ (1 / 2 : ℝ) * (∫ x, g x ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  sorry

end IntegrationHelpers
```

**Critical ordering:**
- `omit [...] in` must appear **before** the docstring
- Placing it after the docstring will cause a compilation error

**When to use:**
- Lemma doesn't actually use a section variable but Lean includes it anyway
- Section variable causes unwanted type class instance requirements
- Want to make lemma signature cleaner and more general

**Common pattern in probability theory:**
```lean
section ProbabilityResults
variable [MeasurableSpace Ω] [MeasurableSpace Ω'] {μ : Measure Ω}

-- Some lemmas need both spaces
lemma needs_both_spaces : ... := sorry

-- Some lemmas only need one
omit [MeasurableSpace Ω'] in
lemma needs_only_Omega : ... := sorry

end ProbabilityResults
```

### Common Tactics for Measure Theory

```lean
-- Prove measurability automatically
measurability

-- Prove positivity of measures/integrals
positivity

-- Prove ae statements from universal
ae_of_all

-- Work with integrability
-- Step 1: Show measurability
have h_meas : Measurable f := by measurability
-- Step 2: Show boundedness
have h_bound : ∃ C, ∀ x, ‖f x‖ ≤ C := ⟨1, fun x => ...⟩
-- Step 3: Combine
exact integrable_of_bounded_measurable h_meas h_bound
```

### Pattern 8: Automating Measurability Proofs

The `measurability` tactic can replace manual proofs involving `measurable_pi_lambda`, `measurable_pi_apply`, and similar boilerplate patterns. This is especially useful for product spaces and complex compositions.

**Manual vs Automated:**

```lean
-- ❌ Manual: verbose and repetitive
lemma measurable_projection {n : ℕ} :
    Measurable (fun (x : ℕ → α) => fun (i : Fin n) => x i.val) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  exact measurable_pi_apply i.val

-- ✅ Automated: clean and maintainable
lemma measurable_projection {n : ℕ} :
    Measurable (fun (x : ℕ → α) => fun (i : Fin n) => x i.val) := by
  measurability
```

**Using `fun_prop` with `measurability` discharger:**

For goals involving function properties where measurability appears as a subgoal:

```lean
-- When proving Measurable for complex function compositions
have h_meas : Measurable (fun ω => fun i : Fin k => X (m + 1 + i.val) ω) := by
  fun_prop (disch := measurability)
```

**Making lemmas discoverable with `@[measurability]` attribute:**

Add the attribute to make your measurability lemmas available to the `measurability` tactic:

```lean
@[measurability]
lemma measurable_shiftSeq {d : ℕ} :
    Measurable (shiftSeq (β:=β) d) := by
  measurability

@[measurability]
lemma measurable_firstRMap (X : ℕ → Ω → α) (r : ℕ) (hX : ∀ i, Measurable (X i)) :
    Measurable (firstRMap X r) := by
  measurability
```

Now when you call `measurability` elsewhere, it can automatically use these lemmas.

**Combining with `@[fun_prop]` for compositional proofs:**

For custom measurability lemmas, use both attributes to enable both `measurability` and `fun_prop` tactics:

```lean
-- Best practice: make lemma discoverable by both tactics
@[measurability, fun_prop]
lemma measurable_shiftℤ : Measurable (shiftℤ (α := α)) := by
  measurability

-- Now both tactics can find it automatically
example : Measurable (fun ω => shiftℤ (α := α) ω) := by
  measurability  -- Works!

example : Measurable (fun ω => shiftℤ (α := α) (ω 0)) := by
  fun_prop (disch := measurability)  -- Also works!
```

**When to add `@[fun_prop]`:**
- Custom function measurability lemmas (like `measurable_shiftℤ`)
- Enables `fun_prop (disch := measurability)` to use them in compositional proofs
- Allows cleaner automation for complex function compositions

**Common patterns that `measurability` handles:**

```lean
-- Product space projections
measurable_pi_lambda _ (fun i => measurable_pi_apply (f i))  -- ✗ Manual
measurability                                                 -- ✓ Auto

-- Coordinate permutations
refine measurable_pi_lambda _ (fun i => measurable_pi_apply (σ i))  -- ✗ Manual
measurability                                                        -- ✓ Auto

-- Function restrictions/extensions
refine measurable_pi_lambda _ (fun i => measurable_pi_apply (Fin.castLE hmn i))  -- ✗ Manual
measurability                                                                     -- ✓ Auto

-- Composed maps with measurable components
have h_proj_meas : Measurable (fun g => fun i => g (Fin.castLE hkℓ i)) := by
  measurability  -- Much cleaner than manual proof
```

**Real-world automation results:**

From the exchangeability project, automation with `measurability` and `@[measurability]` attributes:
- Simplified 33 proofs across 9 files
- Eliminated ~90 lines of boilerplate
- Made proofs more maintainable and easier to understand

**When automation works well:**

✅ **Direct measurability goals:** Simple product types and compositions
```lean
lemma measurable_proj : Measurable (fun x : ℕ → α => fun i : Fin n => x i) := by
  measurability  -- Works great
```

✅ **Function property goals with measurability subgoals:**
```lean
have h : Measurable (fun ω => fun i => X (k i) ω) := by
  fun_prop (disch := measurability)  -- Handles composition + measurability
```

✅ **After adding attributes:** Making custom lemmas discoverable boosts power
```lean
@[measurability]
lemma measurable_myCustomMap : Measurable myCustomMap := by ...
-- Now measurability can use this automatically
```

**When automation doesn't work (pitfalls to avoid):**

⚠️ **Complex set operations can timeout:**
```lean
-- ❌ Can hang or timeout
lemma complicated_set : MeasurableSet ((f ⁻¹' A) ∩ (g ⁻¹' B) ∪ (h ⁻¹' C)) := by
  measurability  -- May timeout on complex set algebra

-- ✅ Use direct proof instead
lemma complicated_set : MeasurableSet ((f ⁻¹' A) ∩ (g ⁻¹' B) ∪ (h ⁻¹' C)) := by
  apply MeasurableSet.union
  · apply MeasurableSet.inter <;> exact Measurable.measurableSet_preimage ‹_› ‹_›
  · exact Measurable.measurableSet_preimage ‹_› ‹_›
```

⚠️ **Custom definitions unknown to `fun_prop`:**
```lean
-- If you have: def path (X : ℕ → Ω → α) : Ω → (ℕ → α) := fun ω n => X n ω

-- ❌ fun_prop doesn't know about path
lemma measurable_path_composed : Measurable (path X) := by
  fun_prop  -- Fails: doesn't recognize 'path'

-- ✅ Use measurability directly or add intermediate steps
lemma measurable_path_composed : Measurable (path X) := by
  measurability  -- Works if path unfolds to measurable_pi_lambda pattern
  -- OR unfold manually:
  -- unfold path; measurability
```

**General troubleshooting:**

If tactics fail, try:
1. Add `@[measurability]` to a key helper lemma
2. Break into smaller intermediate steps
3. Use `fun_prop (disch := measurability)` for function compositions
4. Unfold custom definitions first, then automate
5. For complex set operations, write direct structured proofs

**Automation Philosophy - Balancing Power with Readability:**

Automation tactics are powerful but should serve clarity, not obscure it:

✅ **Good automation:** Eliminates tedious boilerplate while keeping proof structure clear
```lean
-- Pi-type measurability: automation is perfect here
lemma measurable_proj : Measurable (fun x : ℕ → α => fun i : Fin n => x i) := by
  measurability  -- Clear intent, no important reasoning hidden

-- Arithmetic side conditions: automation prevents distraction
lemma main_result (n : ℕ) (h : n > 0) : n + 1 < 2 * n := by
  omega  -- Trivial arithmetic, would distract from real proof
```

⚠️ **Overly aggressive automation:** Hides important mathematical reasoning
```lean
-- ❌ BAD: Key proof step hidden by automation
lemma important_theorem : complicated_property := by
  mega_tactic_that_does_everything
  -- What's the actual argument? Unclear!

-- ✅ GOOD: Important reasoning explicit, automation for steps
lemma important_theorem : complicated_property := by
  -- Key insight: reduce to simpler property via this lemma
  suffices simpler_property by exact key_lemma this
  -- Now use automation for routine verification
  constructor
  · measurability
  · omega
```

**Guidelines:**
- Use automation for: boilerplate (measurability), trivial arithmetic (omega/linarith), type class inference
- Keep explicit: key mathematical insights, proof architecture, non-obvious lemma applications
- Document with comments when automation does something non-trivial
- If a tactic call raises "how does this work?", consider making it more explicit

### Real-World Example: Finite Marginals Uniqueness

From exchangeability project - shows typical measure theory proof structure:

```lean
-- Goal: Two measures equal if all finite marginals equal
theorem measure_eq_of_fin_marginals_eq
    {μ ν : Measure (ℕ → α)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ n, Measure.map (fun ω => ω ∘ Fin.val) μ =
              Measure.map (fun ω => ω ∘ Fin.val) ν) :
    μ = ν := by
  -- Strategy:
  -- 1. Show equality on π-system of cylinder sets
  -- 2. Use uniqueness of extension to σ-algebra
  ext s hs
  -- Key: Reduce to finite-dimensional projections
  sorry
```

## Analysis & Topology

### Core Patterns

#### Pattern 1: Continuity Proofs

```lean
-- From preimage of open sets
lemma continuous_of_isOpen_preimage
    {f : X → Y} (h : ∀ U, IsOpen U → IsOpen (f ⁻¹' U)) :
    Continuous f := by
  rw [continuous_def]
  exact h

-- Using continuity tactic (automatic)
lemma continuous_comp_add :
    Continuous (fun (p : ℝ × ℝ) => p.1 + p.2) := by
  continuity
```

#### Pattern 2: Compactness Arguments

```lean
-- Finite subcover criterion
lemma compact_of_finite_subcover
    {K : Set X} (h : ∀ (ι : Type*) (U : ι → Set X),
      (∀ i, IsOpen (U i)) → K ⊆ ⋃ i, U i →
      ∃ (s : Finset ι), K ⊆ ⋃ i ∈ s, U i) :
    IsCompact K := by
  sorry

-- Using compactness
example {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ x ∈ K, ∀ y ∈ K, f x ≤ f y := by
  exact IsCompact.exists_isMinOn hK hne (continuous_id.comp continuous_f)
```

#### Pattern 3: Limits via Filters

```lean
-- ε-δ criterion via filters
lemma tendsto_of_forall_eventually
    (h : ∀ ε > 0, ∀ᶠ n in atTop, ‖x n - L‖ < ε) :
    Tendsto x atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  exact h
```

### Common Tactics

```lean
continuity  -- Prove continuity automatically
fun_prop    -- General function property prover (Lean 4.13+)
```

## Algebra

### Core Patterns

#### Pattern 1: Building Algebraic Instances

```lean
-- Compositional instance construction
instance : CommRing (Polynomial R) := inferInstance

-- Manual instance for custom types
instance : Ring MyType := {
  add := my_add,
  add_assoc := my_add_assoc,
  zero := my_zero,
  zero_add := my_zero_add,
  add_zero := my_add_zero,
  neg := my_neg,
  add_left_neg := my_add_left_neg,
  mul := my_mul,
  mul_assoc := my_mul_assoc,
  one := my_one,
  one_mul := my_one_mul,
  mul_one := my_mul_one,
  left_distrib := my_left_distrib,
  right_distrib := my_right_distrib
}
```

#### Pattern 2: Quotient Constructions

```lean
-- Ring homomorphism from quotient
lemma quotient_ring_hom (I : Ideal R) :
    RingHom R (R ⧸ I) := by
  refine { toFun := Ideal.Quotient.mk I,
           map_one' := rfl,
           map_mul' := fun x y => rfl,
           map_zero' := rfl,
           map_add' := fun x y => rfl }
```

#### Pattern 3: Universal Properties

```lean
-- Use universal property to define morphism
lemma exists_unique_hom (h : ...) :
    ∃! φ : A →+* B, ... := by
  use my_homomorphism
  constructor
  · -- Prove it satisfies property
  · -- Prove uniqueness
    intro ψ hψ
    ext x
    sorry
```

### Common Tactics

```lean
ring       -- Solve ring equations
field_simp -- Simplify field expressions
group      -- Solve group equations
```

## Number Theory & Combinatorics

### Core Patterns

#### Pattern 1: Induction on Lists/Nats

```lean
lemma property_of_list (l : List α) : P l := by
  induction l with
  | nil =>
    -- Base case: l = []
    sorry
  | cons head tail ih =>
    -- Inductive case: l = head :: tail, have ih : P tail
    sorry
```

#### Pattern 2: Divisibility

```lean
-- Using dvd
lemma dvd_example (n : ℕ) : 2 ∣ n * (n + 1) := by
  cases' Nat.even_or_odd n with h h
  · -- n even
    obtain ⟨k, rfl⟩ := h
    use k * (2 * k + 1)
    ring
  · -- n odd
    obtain ⟨k, rfl⟩ := h
    use (2 * k + 1) * (k + 1)
    ring
```

### Common Tactics

```lean
linarith   -- Linear arithmetic
norm_num   -- Normalize numerical expressions
omega      -- Integer linear arithmetic (Lean 4.13+)
```

## Cross-Domain Tactics

### Essential for All Domains

```lean
-- Simplification
simp only [lemma1, lemma2]  -- Explicit lemmas (preferred)
simpa using h               -- Simplify and close with h

-- Case analysis
by_cases h : p              -- Split on decidable proposition
rcases h with ⟨x, y, hx⟩    -- Destructure exists/and/or

-- Rewriting
rw [lemma]                  -- Left-to-right
rw [← lemma]                -- Right-to-left

-- Function extensionality
ext x                       -- Prove functions equal pointwise
funext x                    -- Alternative syntax

-- Apply lemmas
apply lemma                 -- Apply, leaving subgoals
exact expr                  -- Close goal exactly
refine template ?_ ?_       -- Apply with placeholders
```

## Pattern: Equality via Uniqueness

Works across all domains:

```lean
-- To show f = g, prove:
-- 1. Both f and g satisfy some uniqueness criterion
-- 2. Use the uniqueness theorem

lemma my_eq : f = g := by
  have hf : satisfies_property f := ...
  have hg : satisfies_property g := ...
  exact unique_satisfier hf hg
```

**Examples:**
- Measures: Equal if agree on π-system
- Conditional expectations: Equal if have same integrals on all measurable sets
- Functions: Equal if continuous and agree on dense subset
- Group homomorphisms: Equal if agree on generators
