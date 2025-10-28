# Domain-Specific Patterns for Lean 4

## TLDR

**Purpose:** Quick reference for common proof patterns and tactics across mathematical domains.

**When to use:** When working in a specific domain (measure theory, analysis, algebra, etc.) and need proven patterns for common tasks.

**Coverage:** Measure theory (12 patterns), analysis (3 patterns), algebra (3 patterns), number theory (2 patterns), plus cross-domain tactics.

**For deep measure theory patterns (sub-σ-algebras, conditional expectation, type class errors):** See `references/measure-theory.md`

## Quick Reference by Domain

### Measure Theory & Probability (12 Patterns)

| Pattern | Task | Key Tactic/Approach |
|---------|------|---------------------|
| 1. Proving Integrability | Show function integrable | `bounded + measurable + finite measure` |
| 2. Conditional Expectation | Prove μ[f\|m] = g | Uniqueness theorem (3 conditions) |
| 3. Sub-σ-Algebras | Type class management | See measure-theory.md |
| 4. Almost Everywhere | Convert universal to ae | `ae_of_all`, `filter_upwards` |
| 5. Filtrations | Martingales, adapted processes | Monotone σ-algebras |
| 6. Product Measures | Independence via products | Ionescu-Tulcea |
| 7. Section Variables | Exclude from lemmas | `omit [...] in` |
| 8. Measurability | Automate boilerplate | `measurability`, `@[measurability]` |
| 9. Implicit Parameters | Follow mathlib conventions | Inferrable → implicit |
| 10. Structure Matching | const_mul with sums | Match goal parenthesization |
| 11. Type Matching | Integrable.of_bound | Use canonical forms `(m:ℝ)⁻¹` |
| 12. Pointwise Inequalities | intro vs filter_upwards | `intro ω` for simple cases |

**Common tactics:** `measurability`, `positivity`, `ae_of_all`, `filter_upwards`

### Analysis & Topology (3 Patterns)

| Pattern | Task | Key Tactic/Approach |
|---------|------|---------------------|
| 1. Continuity | Prove continuous | `continuity`, `continuous_def` |
| 2. Compactness | Finite subcover, min/max | `IsCompact.exists_isMinOn` |
| 3. Limits | ε-δ via filters | `Metric.tendsto_atTop` |

**Common tactics:** `continuity`, `fun_prop`

### Algebra (3 Patterns)

| Pattern | Task | Key Tactic/Approach |
|---------|------|---------------------|
| 1. Algebraic Instances | Build Ring/CommRing | `inferInstance` or manual |
| 2. Quotients | Define quotient homs | Universal property |
| 3. Universal Properties | Unique morphisms | Existence + uniqueness |

**Common tactics:** `ring`, `field_simp`, `group`

### Number Theory (2 Patterns)

| Pattern | Task | Key Tactic/Approach |
|---------|------|---------------------|
| 1. Induction | Lists/Nats | `induction` with cases |
| 2. Divisibility | Prove n ∣ m | `cases' even_or_odd`, `use` |

**Common tactics:** `linarith`, `norm_num`, `omega`

### Cross-Domain

**Essential tactics:** `simp only`, `by_cases`, `rcases`, `rw`, `ext`, `apply`, `exact`, `refine`

**Equality via uniqueness:** Works across all domains (measures, functions, homs)

---

## Measure Theory & Probability

### Pattern 1: Proving Integrability

**Golden rule:** `bounded + measurable + finite measure = integrable`

```lean
lemma integrable_of_bounded_measurable
    [IsFiniteMeasure μ] {f : X → ℝ}
    (h_meas : Measurable f)
    (h_bound : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := h_bound
  exact Integrable.of_bound h_meas.aestronglyMeasurable C (ae_of_all _ hC)
```

**Key variations:**
- AE bound: Use `AEMeasurable` and `∀ᵐ x ∂μ, ‖f x‖ ≤ C`
- Indicator: `hf.indicator hA` when `hf : Integrable f μ`

### Pattern 2: Conditional Expectation Equality

**Uniqueness theorem:** To show μ[f | m] = g, prove all three:
1. g is m-measurable
2. g is integrable
3. ∀ B (m-measurable set): ∫ x in B, g x ∂μ = ∫ x in B, f x ∂μ

```lean
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

### Pattern 3: Sub-σ-Algebras and Type Class Management

**Critical issues:**
- Binder order: instance parameters before plain parameters
- Never use `‹_›` for ambient space (resolves incorrectly)
- Provide trimmed measure instances with `haveI`

```lean
-- ✅ Correct pattern
lemma my_condexp_lemma {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) : Result := by
  haveI : IsFiniteMeasure (μ.trim hm) := isFiniteMeasure_trim μ hm
  haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
  -- Now call mathlib lemmas
```

**For complete coverage:** See `references/measure-theory.md` for sub-σ-algebra patterns, condExpWith, debugging type class errors, and binder order requirements.

### Pattern 4: Almost Everywhere Properties

**From universal to ae:**
```lean
have h : ∀ x, P x := ...
have h_ae : ∀ᵐ x ∂μ, P x := ae_of_all _ h
```

**Combining ae properties:**
```lean
filter_upwards [h1, h2] with x hP hQ
-- Now have: ∀ᵐ x ∂μ, P x ∧ Q x
```

**ae equality reasoning:**
```lean
-- Transitivity
h1.trans h2  -- f =ᵐ[μ] g → g =ᵐ[μ] h → f =ᵐ[μ] h

-- Substitution
hf.congr h  -- Integrable f μ → f =ᵐ[μ] g → Integrable g μ
```

### Pattern 5: Filtrations and Martingales

```lean
def Filtration (f : ℕ → MeasurableSpace Ω) : Prop :=
  Monotone f ∧ ∀ n, f n ≤ m₀

def Adapted (X : ℕ → Ω → ℝ) (f : ℕ → MeasurableSpace Ω) : Prop :=
  ∀ n, Measurable[f n] (X n)

def IsMartingale (X : ℕ → Ω → ℝ) (f : ℕ → MeasurableSpace Ω) : Prop :=
  Adapted X f ∧ (∀ n, Integrable (X n) μ) ∧
  ∀ m n, m ≤ n → μ[X n | f m] =ᵐ[μ] X m
```

### Pattern 6: Product Measures and Independence

```lean
-- Infinite product via Ionescu-Tulcea
noncomputable def productMeasure (ν : Measure α) : Measure (ℕ → α) :=
  Measure.pi (fun _ => ν)

lemma independent_of_product :
    ∀ n m, n ≠ m →
    IndepFun (fun ω => ω n) (fun ω => ω m) (productMeasure ν) := by
  sorry
```

### Pattern 7: Managing Section Variables with `omit`

Exclude section variables from specific lemmas:

```lean
section IntegrationHelpers
variable [MeasurableSpace Ω] {μ : Measure Ω}

-- This lemma doesn't need MeasurableSpace Ω
omit [MeasurableSpace Ω] in
lemma abs_integral_mul_le_L2 [IsFiniteMeasure μ] {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ ... := by sorry

end IntegrationHelpers
```

**Critical:** `omit [...] in` must appear **before** docstring, not after.

**When to use:** Lemma doesn't use section variable, or variable causes unwanted instance requirements.

### Pattern 8: Automating Measurability Proofs

**Manual vs automated:**

```lean
-- ❌ Manual: verbose
lemma measurable_projection {n : ℕ} :
    Measurable (fun (x : ℕ → α) => fun (i : Fin n) => x i.val) := by
  refine measurable_pi_lambda _ (fun i => ?_)
  exact measurable_pi_apply i.val

-- ✅ Automated: clean
lemma measurable_projection {n : ℕ} :
    Measurable (fun (x : ℕ → α) => fun (i : Fin n) => x i.val) := by
  measurability
```

**Make lemmas discoverable:**

```lean
@[measurability]
lemma measurable_shiftSeq {d : ℕ} : Measurable (shiftSeq (β:=β) d) := by
  measurability
```

**For function compositions:**

```lean
-- Use fun_prop with measurability discharger
have h : Measurable (fun ω => fun i => X (k i) ω) := by
  fun_prop (disch := measurability)
```

**Combine attributes for maximum automation:**

```lean
@[measurability, fun_prop]
lemma measurable_myFunc : Measurable myFunc := by measurability
```

**When automation works well:**
- ✅ Product types and compositions
- ✅ Pi-type projections
- ✅ Coordinate permutations
- ✅ After adding `@[measurability]` attributes

**When automation doesn't work:**
- ⚠️ Complex set operations (can timeout)
- ⚠️ Custom definitions unknown to fun_prop
- **Solution:** Break into smaller steps or use direct proof

**Real-world results:** Simplified 33 proofs, eliminated ~90 lines of boilerplate.

### Pattern 9: Implicit vs Explicit Parameters

**Core principle:** `{param}` when inferrable, `(param)` when primary data or not inferrable.

**Use implicit `{param}` when:**
```lean
-- ✅ n inferrable from S
def prefixCylinder {n : ℕ} (S : Set (Fin n → α)) : Set (ℕ → α)

-- ✅ n inferrable from c
lemma l2_bound {n : ℕ} {c : Fin n → ℝ} (σSq ρ : ℝ) : ...
```

**Keep explicit `(param)` when:**
```lean
-- ✅ Primary data
theorem deFinetti (μ : Measure Ω) (X : ℕ → Ω → α) : ...

-- ✅ Used in body, not types
def shiftedCylinder (n : ℕ) (F : Ω[α] → ℝ) : Ω[α] → ℝ :=
  fun ω => F ((shift^[n]) ω)

-- ✅ In return type
lemma foo (n : ℕ) : Fin n → α := ...
```

**When in doubt, keep explicit.** See [mathlib-style.md](mathlib-style.md) for conventions.

### Pattern 10: Measurable Structure Must Match Goal

When using `Measurable.const_mul` with sums, structure must match goal's parenthesization.

```lean
-- ❌ WRONG: constant inside each term
have h : Measurable (fun ω => (1/(m:ℝ)) * ∑ k, f k ω) :=
  Finset.measurable_sum _ (fun k _ => Measurable.const_mul ...)
-- Applies const_mul to EACH TERM - wrong variable binding!

-- ✅ CORRECT: constant wraps entire sum
have h : Measurable (fun ω => (1/(m:ℝ)) * ∑ k, f k ω) :=
  Measurable.const_mul (Finset.measurable_sum _ (fun k _ => ...)) _
-- const_mul wraps whole sum, matching goal structure
```

**Key:** Match goal parenthesization: `c * (∑ ...)` not `∑ (c * ...)`

### Pattern 11: Integrable.of_bound Type Matching

Bound expression in measurability hypothesis must match canonical form after `simp`.

```lean
-- ❌ WRONG: Definition uses 1/(m:ℝ) but goal has (m:ℝ)⁻¹ after simp
have h_meas : Measurable (fun ω => 1/(m:ℝ) * ∑ i, f i ω) := ...
apply Integrable.of_bound h_meas.aestronglyMeasurable 1
filter_upwards with ω; simp [Real.norm_eq_abs]
-- Type mismatch: goal has (m:ℝ)⁻¹ but h_meas has 1/(m:ℝ)

-- ✅ CORRECT: Use canonical form (m:ℝ)⁻¹ from start
have h_meas : Measurable (fun ω => (m:ℝ)⁻¹ * ∑ i, f i ω) := ...
apply Integrable.of_bound h_meas.aestronglyMeasurable 1
filter_upwards with ω; simp [Real.norm_eq_abs]
-- Matches exactly after simp!
```

**Rule:** Use canonical forms: `(m:ℝ)⁻¹` not `1/(m:ℝ)`. See [calc-patterns.md](calc-patterns.md).

### Pattern 12: Pointwise Inequalities

**Use `intro ω` for simple pointwise proofs:**

```lean
-- ❌ WRONG: filter_upwards doesn't unfold for simple inequalities
filter_upwards with ω
exact abs_sub_le _ _ _
-- Error: type mismatch in implicit EventuallyEq form

-- ✅ CORRECT: intro for simple pointwise
intro ω
exact abs_sub_le _ _ _
-- Works: explicit inequality with ω
```

**When to use:**
- `intro ω`: Simple pointwise inequalities, just applying lemmas
- `filter_upwards`: Combining multiple ae conditions, measure theory structure

### Common Measure Theory Tactics

```lean
measurability    -- Prove measurability automatically
positivity       -- Prove positivity of measures/integrals
ae_of_all        -- Universal → ae
filter_upwards   -- Combine ae properties
```

**Automation philosophy:**
- ✅ Use for: trivial arithmetic (omega/linarith)
- ❌ Don't hide: key mathematical insights, proof architecture, non-obvious lemma applications

---

## Number Theory & Combinatorics

### Pattern 1: Induction

```lean
lemma property_of_list (l : List α) : P l := by
  induction l with
  | nil => sorry  -- Base case
  | cons head tail ih => sorry  -- Inductive case with ih : P tail
```

**Common tactics:** `linarith`, `norm_num`, `omega`

---

## Cross-Domain Tactics

**Essential for all domains:**

```lean
-- Simplification
simp only [lem1, lem2]  -- Explicit lemmas (preferred)
simpa using h           -- simp then exact h

-- Case analysis
by_cases h : p          -- Split on decidable
rcases h with ⟨x, hx⟩   -- Destructure exists/and/or

-- Rewriting
rw [lemma]              -- Left-to-right
rw [← lemma]            -- Right-to-left

-- Extensionality
ext x                   -- Function equality pointwise
funext x                -- Alternative

-- Application
apply lemma             -- Apply, leaving subgoals
exact expr              -- Close goal exactly
refine template ?_ ?_   -- Apply with placeholders
```

---

## Related References

- [tactics-reference.md](tactics-reference.md) - Comprehensive tactic catalog
- [calc-patterns.md](calc-patterns.md) - Calculation chains and canonical forms
