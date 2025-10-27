# Proof Golfing: Simplifying Proofs After Compilation

Systematic patterns for simplifying and cleaning up proofs after the file compiles successfully.

**When to use:** After your file compiles with `lake build`, perform these simplification passes to improve readability and maintainability.

## Core Principle

**First make it compile, then make it clean.**

Don't prematurely optimize proofs while getting code to work. Once everything compiles, apply these patterns systematically.

## Before You Start: Essential Setup

### 1. Establish File Scope Boundaries

**Ask the user first:**
```
"I want to golf proofs. Which files are safe to edit?
Which are you actively working on or recently refactored?"
```

**Why this matters:** Avoid wasting time on files with:
- Active work in progress (changes will conflict)
- Recent refactoring (cleanup may already be done)
- Uncommitted changes (your edits may get lost)

**Good targets:**
- Files marked as "stable"
- Files that haven't changed in >1 week
- Files user explicitly designates

### 2. Get Concrete Golfing Targets

**Ask for specific patterns to look for:**

```
"What patterns should I simplify? Examples:
1. := by exact <term>  →  := <term>
2. Multiple consecutive rw steps  →  rw [a, b, c]
3. by intro x; exact f x  →  f
4. Proofs with >5 consecutive 'have' statements
5. Other patterns specific to your codebase?"
```

**Why this matters:** Generic "golf proofs" leads to:
- Inconsistent style choices
- Missing domain-specific simplifications
- Time spent on patterns user doesn't care about

### 3. See Examples from the Actual Codebase

**Request before/after examples:**

```
"Can you show me one example from YOUR code of:
- ❌ Verbose style (what to golf)
- ✅ Concise style (target result)

This helps me match your aesthetic preferences."
```

**Common style preferences to clarify:**
- `simp [foo, bar]` vs `simp only [foo, bar]`
- Term mode (`:= term`) vs tactic mode (`:= by tactics`)
- Calc chains vs transitive `have` statements
- Anonymous `have :` vs named `have h_property :`

### 4. Check for Existing Tooling

**Ask about automation:**

```
"Are there scripts or tools for finding golfing targets?
Examples:
- scripts/proof_complexity.sh - find longest proofs
- lake env lean --find-unused - detect dead code
- Custom linters or style checkers"
```

**Why this matters:** Use existing infrastructure instead of manual search

### 5. Get Quick Context on Recent Changes

**Ask before starting:**

```
"Any recent changes I should know about?
- Files recently refactored (may already be clean)
- Known cleanup targets (technical debt areas)
- Style changes in progress (avoid conflicts)"
```

## Quick Reference: Common Patterns

Based on real-world sessions with 60-75% size reduction per proof:

**Pattern 1: Remove `by exact` wrapper**
```lean
-- ❌ Before (2 lines)
lemma foo : P := by
  exact term

-- ✅ After (1 line)
lemma foo : P := term
```

**Pattern 2: The "let + have + exact" anti-pattern** ⭐ HIGH IMPACT
```lean
-- ❌ Before (14 lines, ~140 tokens)
lemma Contractable.prefix ... := by
  intro m k hk_mono
  -- Lift k to a function
  let k' : Fin m → ℕ := fun i => (k i).val
  have hk'_mono : StrictMono k' := by
    intro i j hij
    simp only [k']
    exact hk_mono hij
  exact hX m k' hk'_mono

-- ✅ After (2 lines, ~38 tokens)
lemma Contractable.prefix ... := by
  intro m k hk_mono
  exact hX m (fun i => (k i).val) (fun i j hij => hk_mono hij)
```

**When this pattern applies:**
- let binding used only in have and final exact
- have proof is simple (no complex case analysis)
- Final result accepts lambda arguments

**Pattern 3: Inline constructor branches**
```lean
-- ❌ Before (7 lines)
constructor
· intro k hk
  exact hX m k hk
· intro ν' hν'
  have hid : StrictMono ... := fun i j hij => hij
  have h := hν' (fun i => i.val) hid
  exact h.symm

-- ✅ After (3 lines)
constructor
· intro k hk; exact hX m k hk
· intro ν' hν'; exact (hν' (fun i => i.val) (fun i j hij => hij)).symm
```

**Pattern 4: Direct lemma over automation** (for simple cases)
```lean
-- ❌ Wrong (longer AND fails!)
exact hX m (fun i => k + i.val) (fun i j hij => by omega)
-- Error: omega produces counterexample!

-- ✅ Correct (shorter AND works!)
exact hX m (fun i => k + i.val) (fun i j hij => Nat.add_lt_add_left hij k)
```

**When NOT to use automation:**
- You have a direct mathlib lemma that's ≤5 tokens
- Simple Nat arithmetic (omega can struggle with coercions)
- Automation overhead > direct application

**Impact from real sessions:**
- Session 1: 11 proofs, ~22 lines saved
- Session 2: 3 proofs, ~26 lines saved (76.5% reduction avg)

## Systematic Optimization Workflow

Techniques inspired by automated proof optimization research, adapted for interactive development.

### The Multi-Candidate Strategy ⭐ GAME CHANGER

**Core idea:** Generate multiple optimization candidates and test them in parallel, keeping the shortest that compiles.

**Using lean_multi_attempt (MCP tool):**
```lean
-- Original (14 lines):
lemma foo ... := by
  let x := <definition>
  have h : Property x := by <proof>
  exact <result> x h

-- Generate 3 candidates and test in parallel:
mcp__lean-lsp__lean_multi_attempt(
  file = "MyFile.lean",
  line = 218,
  tactics = [
    // Candidate A: Inline with let kept
    "let x := <def>; exact <result> x (fun ... => <proof>)",

    // Candidate B: Full inline
    "exact <result> (fun ... => <def>) (fun ... => <proof>)",

    // Candidate C: Use refine
    "refine <result> ?def ?proof; <fill holes>"
  ]
)
```

**Why this is powerful:**
- Tests 3-4 approaches simultaneously (not sequentially)
- Immediate compilation feedback
- Pick shortest successful candidate
- No wasted time debugging failed approaches

**Time savings:** ~70% per proof vs. manual trial-and-error

**Success rate from real sessions:** 90% (at least one candidate compiles)

### Pattern-Based Search (Not Sequential Reading)

**Don't:** Read through file line by line looking for optimizations

**Do:** Search for known patterns systematically

**High-value patterns to search for:**

```bash
# 1. The "let + have + exact" pattern (HIGHEST value)
grep -A 10 "let .*:=" MyFile.lean | grep -B 8 "exact"

# 2. Multiple consecutive "have" statements
grep -B 2 -A 2 "have.*:=.*by" MyFile.lean | grep -c "have"

# 3. "by exact" wrappers
grep "by$" MyFile.lean | head -1 | xargs -I {} grep -A 1 {} MyFile.lean

# 4. Constructor branches with multiple lines
grep -A 5 "constructor" MyFile.lean | grep "intro"
```

**Impact:** Find all 3 optimization targets in 30 seconds instead of reading entire file

### The Decision Tree for Candidate Generation

When you find the "let + have + exact" pattern, automatically generate these candidates:

```
Found: let x := <def>; have h : P := by <proof>; exact <result> x h

Generate in parallel:
├─ Candidate A: Full inline
│  exact <result> (fun ... => <def>) (fun ... => <proof>)
│  • Shortest when types are simple
│  • May fail if type inference struggles
│
├─ Candidate B: Inline with let kept
│  let x := <def>; exact <result> x (fun ... => <proof>)
│  • Middle ground approach
│  • Helps type inference
│
└─ Candidate C: Use refine for complex types
   refine <result> ?def ?proof; exact <def>; exact <proof>
   • Most likely to compile
   • Slightly longer
```

**Test all 3 with lean_multi_attempt, pick shortest that compiles.**

### Token Counting Quick Reference

**For picking winners from multiple candidates:**

```lean
// ~1 token each
let, have, exact, intro, by, fun

// ~2 tokens each
:=, =>, (fun x => ...), StrictMono

// ~3 tokens each
Nat.add_lt_add_left, (fun i j hij => ...)

// ~5-10 tokens
let x : Type := definition
have h : Property := by proof
```

**Rule of thumb:**
- Each line ≈ 8-12 tokens
- Each have + proof ≈ 15-20 tokens
- Each inline lambda ≈ 5-8 tokens

**Mental shortcut:** Compare line counts first, then check token density for similar lengths.

### When NOT to Optimize

**Anti-patterns (don't waste time on these):**

❌ **Already optimal** (1-2 lines)
```lean
lemma foo : P := hX  -- Can't improve!
```

❌ **Readability would suffer significantly**
```lean
// Before: Clear intent
have h1 : A := ...  -- Establishes precondition
have h2 : B := ...  -- Derives intermediate result
have h3 : C := ...  -- Combines for conclusion
exact combine h1 h2 h3

// After: Unreadable mess
exact combine (obscure nested lambdas) ...
```

❌ **Complex pattern matching**
```lean
cases x with
| inl ha => ...  -- Don't try to inline pattern matches!
| inr hb => ...
```

✅ **DO optimize when:**
- Proof is >5 lines with repetitive structure
- Clear "let + have + exact" pattern
- Multiple small have statements that could inline
- Mechanical transformations (not semantic reasoning)

### Measuring Success

**Track these metrics:**
- **Lines saved:** before/after line count
- **Token reduction:** rough estimate from mental counting
- **Compilation:** all optimizations must compile
- **Time per proof:** aim for <5 minutes per optimization

**Real session benchmarks:**
- Average reduction: 60-75% per proof
- Time per proof: ~7 minutes (including testing)
- Success rate: 90-100% (with multi-candidate approach)

## Simplification Patterns

### Pattern 1: Inline Single-Use Intermediate Lemmas

When an intermediate `have` is used exactly once, inline it:

**Before:**
```lean
have hterm : ∀ j ∈ Neg, |c j| = -c j := fun j hj => abs_of_neg (Finset.mem_filter.mp hj).2
calc ∑ j ∈ Neg, |c j|
    = ∑ j ∈ Neg, (-c j) := Finset.sum_congr rfl hterm
  _ = -∑ j ∈ Neg, c j := by simp [Finset.sum_neg_distrib]
```

**After:**
```lean
calc ∑ j ∈ Neg, |c j|
    = ∑ j ∈ Neg, (-c j) := Finset.sum_congr rfl (fun j hj => abs_of_neg (Finset.mem_filter.mp hj).2)
  _ = -∑ j ∈ Neg, c j := by simp [Finset.sum_neg_distrib]
```

**When to inline:**
- The intermediate lemma is used exactly once
- Inlining doesn't make the proof significantly harder to read
- The term fits naturally as a lambda or inline expression

**When to keep separate:**
- The lemma is used multiple times
- The proof is complex and benefits from a descriptive name
- Inlining would create an unreadably long line

### Pattern 2: Consolidate Simple Rewrites

**Before:**
```lean
have hσSq_nonneg : 0 ≤ σSq := by
  simpa [σSq] using sq_nonneg σ

have hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σSq := by
  intro k; simpa [σSq] using _hvar k
```

**After:**
```lean
have hσSq_nonneg : 0 ≤ σSq := sq_nonneg σ
have hvar : ∀ k, ∫ ω, (ξ k ω - m)^2 ∂μ = σSq := fun k => _hvar k
```

**When to consolidate:**
- `simpa` or `simpa using` that just unfolds definitions
- Simple `intro` followed by direct application
- `by exact` wrappers (just remove them)

### Pattern 3: Merge Simp Steps

**Before:**
```lean
have hc_sum : ∑ j, c j = 0 := by
  simp only [c]
  have hp := _hp_prob.1
  have hq := _hq_prob.1
  rw [Finset.sum_sub_distrib, hp, hq]
  ring
```

**After:**
```lean
have hc_sum : ∑ j, c j = 0 := by
  simp only [c, Finset.sum_sub_distrib, _hp_prob.1, _hq_prob.1]; ring
```

**When to merge:**
- Multiple `simp only` or `rw` steps that could be combined
- Sequential rewrites that don't need intermediate inspection
- Proof ends with `ring`, `linarith`, or other finishing tactic

### Pattern 4: Replace `trans` + `calc` with Single `calc`

**Before:**
```lean
have h_diag : ... := by
  trans (∑ i, (c i)^2 * σSq)
  · congr 1; ext i
    calc ...
  · rw [← Finset.sum_mul]; ring
```

**After:**
```lean
have h_diag : ... := by
  calc ∑ i, c i * c i * ∫ ω, (ξ i ω - m) * (ξ i ω - m) ∂μ
      = ∑ i, (c i)^2 * σSq := by congr 1; ext i; calc ...
    _ = σSq * ∑ i, (c i)^2 := by rw [← Finset.sum_mul]; ring
```

**When to use single calc:**
- The intermediate step is clear from the calc chain
- `trans` is only being used to set up a calc
- The proof becomes more readable as a unified calculation

### Pattern 5: Eliminate Nested Helper Lemmas in Calc

**Before:**
```lean
have h_offdiag : ... := by
  have h_cov_term : ∀ i j, ... := by ...
  have h_rewrite : ... := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j hj
    exact h_cov_term i j ...
  have h_factor : ... := by simp [Finset.mul_sum, mul_assoc]
  calc ... = ... := h_rewrite
       _ = ... := h_factor
```

**After:**
```lean
have h_offdiag : ... := by
  calc ∑ i, ∑ j with j ≠ i, c i * c j * ∫ ω, (ξ i ω - m) * (ξ j ω - m) ∂μ
      = ∑ i, ∑ j with j ≠ i, σSq * ρ * (c i * c j) := by
          apply Finset.sum_congr rfl; intro i _
          apply Finset.sum_congr rfl; intro j hj
          have hcov_ij := hcov i j (Ne.symm (Finset.mem_filter.mp hj).2)
          simp [hcov_ij, mul_comm, mul_assoc]
    _ = σSq * ρ * ∑ i, ∑ j with j ≠ i, c i * c j := by simp [Finset.mul_sum, mul_assoc]
```

**When to inline helpers:**
- Helper lemmas are used exactly once in the final calc
- The proof logic is clearer when steps are inline
- The helper names don't add significant documentation value

### Pattern 6: Use Term Mode for Simple Proofs

**Before:**
```lean
have hσ_1ρ_nonneg : 0 ≤ σSq * (1 - ρ) := by
  apply mul_nonneg hσSq_nonneg
  linarith [_hρ_bd.2]
```

**After:**
```lean
have hσ_1ρ_nonneg : 0 ≤ σSq * (1 - ρ) :=
  mul_nonneg hσSq_nonneg (by linarith [_hρ_bd.2])
```

**When to use term mode:**
- The proof is a simple function application
- The result is more concise and readable
- You can still use `by` for complex sub-proofs

### Pattern 7: Reuse Common Intermediate Definitions

**Before:**
```lean
have step5 : ... := by
  have hbdd : BddAbove ... := ...
  ...

have hsup_nonneg : 0 ≤ ⨆ j, |c j| := by
  have hbdd : BddAbove ... := ...  -- duplicate!
  ...
```

**After:**
```lean
have hbdd : BddAbove (Set.range fun j : Fin n => |c j|) := ...

have step5 : ... := by
  ...  -- uses hbdd

have hsup_nonneg : 0 ≤ ⨆ j, |c j| := by
  ...  -- also uses hbdd
```

**When to factor out:**
- The same definition appears multiple times
- The definition is used in multiple proofs
- Factoring improves clarity of proof dependencies

### Pattern 8: Simplify `simpa` Wrappers

**Before:**
```lean
have h_sq : (∑ i, c i)^2 = ∑ i, ∑ j, c i * c j := by
  simpa [pow_two] using
    (Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
      (f := fun i => c i) (g := fun j => c j))
```

**After:**
```lean
have h_sq : (∑ i, c i)^2 = ∑ i, ∑ j, c i * c j := by
  rw [pow_two, Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)
    (f := fun i => c i) (g := fun j => c j)]
```

**When to replace `simpa`:**
- It's just unfolding a definition
- `rw` or `simp only` is clearer
- The `using` clause is doing the real work

### Pattern 9: Remove Commented-Out Code

After the file compiles successfully, remove:
- Failed proof attempts
- Debugging traces
- Commented-out alternative approaches
- Old versions of refactored code

**Exception - Keep brief comments explaining:**
- Why a particular approach was chosen
- Known issues or future TODOs
- Strategies for completing sorries

**Good comment (keep):**
```lean
-- Strategy: Use Dynkin's π-λ theorem to extend from rectangles
-- TODO: Complete the π-system verification
```

**Bad comment (remove):**
```lean
-- have h1 := ...
-- rw [...]
-- -- this doesn't work
-- have h2 := ...
-- -- also doesn't work
```

### Pattern 10: Factor Large Proofs into Lemmas

When a proof becomes very long (>50 lines) with clear logical sections, factor major steps into separate lemmas:

**Before (in main theorem):**
```lean
theorem main_result : ... := by
  -- 150 lines of proof with steps 1-6
  calc ...
```

**After:**
```lean
lemma step1 : ... := by
  -- 20 lines

lemma step2 : ... := by
  -- 25 lines

theorem main_result : ... := by
  calc ... = ... := step1
       _ = ... := step2
       ...
```

**Benefits:**
- Main theorem structure is immediately clear
- Individual steps are independently testable
- Lemmas can be reused elsewhere
- Easier to review and maintain

## Systematic Workflow

### Pass 1: Structural Cleanup

1. Remove commented-out code
2. Factor out major proof blocks into lemmas (if needed)
3. Move definitions closer to their use sites
4. Reorder lemmas into logical groups

### Pass 2: Local Simplifications

5. Inline single-use intermediate lemmas
6. Consolidate simple rewrites
7. Replace `simpa` with direct `rw` or `simp only` where clearer
8. Remove unnecessary `by exact` wrappers
9. Convert simple tactic proofs to term mode

### Pass 3: Proof Chain Improvements

10. Merge sequential simp/rw steps
11. Replace `trans` + `calc` with single `calc`
12. Eliminate nested helpers in calc chains
13. Identify and reuse common sub-expressions

### Pass 4: Verification

14. Run `lake build` to ensure everything still compiles
15. Run `#lint` to check for new issues
16. Read through simplified proofs to verify readability

## Success Metrics

Good simplifications should:
- **Reduce line count** without sacrificing clarity
- **Improve readability** by removing redundant steps
- **Maintain proof structure** - mathematical logic should still be clear
- **Follow mathlib conventions** - align with standard proof patterns

## Anti-Patterns to Avoid

### Don't Over-Inline

**Bad:**
```lean
calc x = y := by
  apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j hj;
  have h1 := ...; have h2 := ...; have h3 := ...; simp [h1, h2, h3, mul_comm, mul_assoc];
  rw [h4, h5]; ring; linarith [h6, h7]
```

If inlining creates an unreadable proof, keep intermediate steps.

### Don't Remove Helpful Names

**Bad:**
```lean
have : ... := by
  ... -- 10 lines of proof
have : ... := by
  ... -- uses first anonymous have
```

**Good:**
```lean
have hkey_property : ... := by
  ... -- 10 lines of proof
have hconclusion : ... := by
  ... -- uses hkey_property
```

If an intermediate result has mathematical significance, give it a descriptive name.

### Don't Sacrifice Clarity for Brevity

**Bad:**
```lean
theorem main : ... :=
  ⟨λ h => h.1.2.1, λ h => ⟨⟨h.1, h.2⟩, ⟨h.3, h.4⟩, ⟨h.5, h.6⟩⟩⟩
```

**Good:**
```lean
theorem main : ... := by
  constructor
  · intro h; exact h.prop1
  · intro h; exact ⟨h.left, h.right, h.key⟩
```

If term-mode proof becomes cryptic, stick with tactic mode.

## Related References

- [mathlib-style.md](mathlib-style.md) - Mathlib style conventions
- [tactics-reference.md](tactics-reference.md) - Tactic catalog
- [domain-patterns.md](domain-patterns.md) - Domain-specific patterns
