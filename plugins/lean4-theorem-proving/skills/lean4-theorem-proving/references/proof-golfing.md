# Proof Golfing: Simplifying Proofs After Compilation

## TLDR

**Core principle:** First make it compile, then make it clean.

**When to use:** After `lake build` succeeds on stable files. Expected 30-40% reduction with proper safety filtering.

**When NOT to use:** Active development, already-optimized code (mathlib-quality), or missing verification tools (93% false positive rate without them).

**Critical:** MUST verify let binding usage before inlining. Bindings used ≥3 times should NOT be inlined (would increase code size).

## Quick Reference: Pattern Priority

| Pattern | Savings | Risk | Priority | Notes |
|---------|---------|------|----------|-------|
| `rw; exact` → `rwa` | 50% | Zero | ⭐⭐⭐⭐⭐ | Always safe, instant |
| `ext + rfl` → `rfl` | 67% | Low | ⭐⭐⭐⭐⭐ | Test first, revert if fails |
| let+have+exact inline | 60-80% | HIGH | ⭐⭐⭐⭐⭐ | MUST verify usage ≤2x |
| Redundant `ext` before `simp` | 50% | Medium | ⭐⭐⭐⭐ | Not all ext is redundant |
| `congr; ext; rw` → `simp only` | 67% | Medium | ⭐⭐⭐⭐ | simp is smarter than you think |
| Smart `ext` (nested) | 50% | Low | ⭐⭐⭐ | ext handles multiple layers |
| `simp` closes goals directly | 67% | Low | ⭐⭐⭐ | Remove explicit `exact` |
| have-calc single-use inline | 50% | Low | ⭐⭐⭐ | Only if used once in calc |
| ext-simp chain combination | Variable | Medium | ⭐⭐ | Only when saves ≥2 lines |
| Arithmetic with automation | 30-50% | Medium | ⭐⭐ | Direct lemmas often better |

**ROI Strategy:** Do ⭐⭐⭐⭐⭐ first (instant wins), then ⭐⭐⭐⭐ (quick with testing), skip ⭐-⭐⭐ if time-limited.

## Critical Safety Warnings

### The 93% False Positive Problem

**Key finding:** Without proper analysis, 93% of "optimization opportunities" are false positives that make code WORSE.

**The Multiple-Use Heuristic:**
- Bindings used 1-2 times: Safe to inline
- Bindings used 3-4 times: 40% worth optimizing (check carefully)
- Bindings used 5+ times: NEVER inline (would increase size 2-4×)

**Example - DON'T optimize:**
```lean
let μ_map := Measure.map (fun ω i => X (k i) ω) μ  -- 20 tokens
-- Used 7 times in proof
-- Current: 20 + (2 × 7) = 34 tokens
-- Inlined: 20 × 7 = 140 tokens (4× WORSE!)
```

### When NOT to Optimize

**Skip if ANY of these:**
- ❌ Let binding used ≥3 times
- ❌ Complex proof with case analysis
- ❌ Semantic naming aids understanding
- ❌ Would create deeply nested lambdas (>2 levels)
- ❌ Readability Cost = (nesting depth) × (complexity) × (repetition) > 5

### Saturation Indicators

**Stop when:**
- ✋ Optimization success rate < 20%
- ✋ Time per optimization > 15 minutes
- ✋ Most patterns are false positives
- ✋ Debating whether 2-token savings is worth it

**Benchmark:** Well-maintained codebases reach saturation after ~20-25 optimizations.

## High-Priority Patterns (⭐⭐⭐⭐⭐)

### Pattern 1: `rw; exact` → `rwa`

Standard mathlib idiom. `rwa` = "rewrite and assumption".

```lean
-- Before (2 lines)
rw [hlhs_eq, hrhs_eq] at hproj_eq
exact hproj_eq

-- After (1 line)
rwa [hlhs_eq, hrhs_eq] at hproj_eq
```

**When:** Any `rw [...] at h` followed by `exact h`
**Risk:** Zero (always works)
**Savings:** 50% reduction

### Pattern 2: `ext + rfl` → `rfl`

When terms are definitionally equal, `rfl` suffices without `ext`.

```lean
-- Before (3 lines)
have h : proj ∘ (fun ω => fun i : ℕ => X i ω)
       = fun ω => fun i : Fin n => X i.val ω := by
  ext ω i; rfl

-- After (1 line)
have h : proj ∘ (fun ω => fun i : ℕ => X i ω)
       = fun ω => fun i : Fin n => X i.val ω := rfl
```

**When:** Proof is `by ext ...; rfl` and terms compute to same result
**Risk:** Low (test with build, revert if fails)
**Savings:** 67% reduction
**Warning:** Not all `ext + rfl` can be simplified!

### Pattern 3: let+have+exact Inline

**⚠️ MOST VALUABLE but HIGHEST RISK - MUST verify safety first!**

```lean
-- Before (14 lines, ~140 tokens)
lemma foo ... := by
  intro m k hk_mono
  let k' : Fin m → ℕ := fun i => (k i).val
  have hk'_mono : StrictMono k' := by
    intro i j hij
    simp only [k']
    exact hk_mono hij
  exact hX m k' hk'_mono

-- After (2 lines, ~38 tokens)
lemma foo ... := by
  intro m k hk_mono
  exact hX m (fun i => (k i).val) (fun i j hij => hk_mono hij)
```

**When to apply (ALL must be true):**
- ✅ Let binding used ≤2 times (preferably only in have and exact)
- ✅ Have proof is simple (no complex case analysis)
- ✅ Final result accepts lambda arguments
- ✅ No semantic naming value lost

**When NOT to apply (ANY = skip):**
- ❌ Let binding used ≥3 times
- ❌ Complex proof logic (cases, nested proofs)
- ❌ Let binding represents important semantic concept
- ❌ Would create deeply nested lambdas (>2 levels)

**Verification:** Use `analyze_let_usage.py` to count uses. Manual verification leads to errors.

**Savings:** 60-80% reduction when applicable
**Risk:** HIGH (93% false positive rate without verification)

## Medium-Priority Patterns (⭐⭐⭐⭐)

### Pattern 4: Redundant `ext` Before `simp`

For common types (Fin, Prod, Subtype), `simp` handles extensionality automatically.

```lean
-- Before (2 lines)
have h : (⟨i.val, ...⟩ : Fin n) = ι i := by
  apply Fin.ext
  simp [ι]

-- After (1 line)
have h : (⟨i.val, ...⟩ : Fin n) = ι i := by simp [ι]
```

**When:** `apply X.ext; simp` for Fin, Prod, Subtype
**Risk:** Medium (not all ext is redundant - test!)
**Savings:** 50% reduction

**Failed example - ext was necessary:**
```lean
ext x; simp [foo]  -- ✅ Works
simp [foo]         -- ❌ Fails - simp needs goal decomposed first
```

### Pattern 5: `congr; ext; rw` → `simp only`

`simp` automatically applies congruence and extensionality when needed.

```lean
-- Before (3 lines)
lemma foo ... :
    Measure.map (fun ω i => X (k₁ i) ω) μ =
    Measure.map (fun ω i => X (k₂ i) ω) μ := by
  congr 1; ext ω i; rw [h_range]

-- After (1 line)
lemma foo ... :
    Measure.map (fun ω i => X (k₁ i) ω) μ =
    Measure.map (fun ω i => X (k₂ i) ω) μ := by
  simp only [h_range]
```

**When:** Manual structural reasoning (`congr`, `ext`) before `rw` or `simp`
**Lesson:** simp is smarter than you think - try it first!
**Savings:** 67% reduction

### Pattern 6: Smart `ext`

`ext` handles multiple nested extensionality layers automatically.

```lean
-- Before (4 lines)
apply Subtype.ext
apply Fin.ext
simp [ι]

-- After (2 lines)
ext; simp [ι]
```

**When:** Nested extensionality (Subtype of Fin, functions returning subtypes, etc.)
**Savings:** 50% reduction

### Pattern 7: `simp` Closes Goals Directly

When `simp` makes goal trivial, skip explicit `exact`.

```lean
-- Before (3 lines)
have hlt : j < j_succ := by
  simp only [Fin.lt_iff_val_lt_val, j, j_succ]
  exact Nat.lt_succ_self n

-- After (1 line)
have hlt : j < j_succ := by simp [Fin.lt_iff_val_lt_val, j, j_succ]
```

**When:** Goal becomes trivial after unfolding, or `exact` applies lemma simp knows
**Savings:** 67% reduction

## Medium-Priority Patterns (⭐⭐⭐)

### Pattern 8: have-calc Single-Use Inline

When `have` is used exactly once in subsequent `calc`, inline directly.

```lean
-- Before (4 lines)
have hsqrt : Real.sqrt (Cf / m) < Real.sqrt (ε^2 / 4) :=
  Real.sqrt_lt_sqrt hnonneg hlt
calc Real.sqrt (Cf / m)
    < Real.sqrt (ε^2 / 4) := hsqrt

-- After (2 lines)
calc Real.sqrt (Cf / m)
    < Real.sqrt (ε^2 / 4) := Real.sqrt_lt_sqrt hnonneg hlt
```

**When to inline:**
- ✅ `have` used exactly once in calc
- ✅ Proof term < 40 chars
- ✅ No descriptive value in name

**When NOT:**
- ❌ Used multiple times in calc
- ❌ Proof term > 40 chars
- ❌ Descriptive name aids understanding (e.g., `h_measurable`)
- ❌ Binding reused outside calc

**Savings:** ~50% line reduction

### Pattern 9: Inline Constructor Branches

```lean
-- Before (7 lines)
constructor
· intro k hk
  exact hX m k hk
· intro ν' hν'
  have hid : StrictMono ... := fun i j hij => hij
  have h := hν' (fun i => i.val) hid
  exact h.symm

-- After (3 lines)
constructor
· intro k hk; exact hX m k hk
· intro ν' hν'; exact (hν' (fun i => i.val) (fun i j hij => hij)).symm
```

**When:** Simple constructor branches, saves ≥2 lines, stays readable
**Savings:** 30-57% per instance

### Pattern 10: Direct Lemma Over Automation

For simple goals, direct mathlib lemmas (≤5 tokens) are shorter AND more reliable than automation.

```lean
-- ❌ Wrong (longer AND fails!)
exact hX m (fun i => k + i.val) (fun i j hij => by omega)
-- Error: omega produces counterexample with Fin coercions!

-- ✅ Correct (shorter AND works!)
exact hX m (fun i => k + i.val) (fun i j hij => Nat.add_lt_add_left hij k)
```

**When NOT to use automation:**
- Direct mathlib lemma ≤5 tokens available
- Simple Nat arithmetic (omega struggles with coercions)
- Automation overhead > direct application

**Lesson:** omega with Fin coercions often fails

## Systematic Workflow

### Phase 1: Pattern Discovery (5 min)

Use systematic search, not sequential reading:

```bash
# 1. Find let+have+exact (HIGHEST value)
grep -A 10 "let .*:=" file.lean | grep -B 8 "exact"

# 2. Find by-exact wrappers
grep -B 1 "exact" file.lean | grep "by$"

# 3. Find ext+simp patterns
grep -n "ext.*simp" file.lean

# 4. Find rw+exact (for rwa)
grep -A 1 "rw \[" file.lean | grep "exact"
```

**Expected:** 10-15 targets per file

### Phase 2: Safety Verification (CRITICAL)

For each let+have+exact pattern:

1. Count let binding uses (or use `analyze_let_usage.py`)
2. If used ≥3 times → SKIP (false positive)
3. If used ≤2 times → Proceed with optimization

**Other patterns:** Verify compilation test will catch issues.

### Phase 3: Apply with Testing (5 min per pattern)

1. Apply optimization
2. Run `lake build`
3. If fails: revert immediately, move to next
4. If succeeds: continue

**Strategy:** Apply 3-5 optimizations, then batch test.

### Phase 4: Check Saturation

After 5-10 optimizations, check indicators:
- Success rate < 20% → Stop
- Time per optimization > 15 min → Stop
- Mostly false positives → Stop

**Recommendation:** Declare victory at saturation.

## Anti-Patterns

### Don't Use Semicolons Just to Combine Lines

```lean
-- ❌ Bad (no savings)
intro x; exact proof  -- Semicolon is a token!

-- ✅ Good (when saves ≥2 lines AND sequential)
ext x; simp [...]; use y; simp  -- Sequential operations
```

**When semicolons ARE worth it:**
- ✅ Sequential operations (ext → simp → use)
- ✅ Saves ≥2 lines
- ✅ Simple steps

### Don't Over-Inline

If inlining creates unreadable proof, keep intermediate steps:

```lean
-- ❌ Bad - unreadable
exact combine (obscure nested lambdas spanning 100+ chars)

-- ✅ Good - clear intent
have h1 : A := ...
have h2 : B := ...
exact combine h1 h2
```

### Don't Remove Helpful Names

```lean
-- ❌ Bad
have : ... := by ...  -- 10 lines
have : ... := by ...  -- uses first anonymous have

-- ✅ Good
have h_key_property : ... := by ...
have h_conclusion : ... := by ...  -- uses h_key_property
```

## Failed Optimizations (Learning)

### Not All `ext` Calls Are Redundant

```lean
-- Original (works)
ext x; simp [prefixCylinder]

-- Attempted (FAILS!)
simp [prefixCylinder]  -- simp alone didn't make progress
```

**Lesson:** Sometimes simp needs goal decomposed first. Always test.

### omega with Fin Coercions

```lean
-- Attempted (FAILS with counterexample!)
by omega

-- Correct (works)
Nat.add_lt_add_left hij k
```

**Lesson:** omega struggles with Fin coercions. Direct lemmas more reliable.

## Appendix

### Token Counting Quick Reference

```lean
// ~1 token each
let, have, exact, intro, by, fun

// ~2 tokens each
:=, =>, (fun x => ...), StrictMono

// ~5-10 tokens
let x : Type := definition
have h : Property := by proof
```

**Rule of thumb:**
- Each line ≈ 8-12 tokens
- Each have + proof ≈ 15-20 tokens
- Each inline lambda ≈ 5-8 tokens

### Saturation Metrics

**Session-by-session data:**
- Session 1-2: 60% of patterns worth optimizing
- Session 3: 20% worth optimizing
- Session 4: 6% worth optimizing (diminishing returns)

**Time efficiency:**
- First 15 optimizations: ~2 min each
- Next 7 optimizations: ~5 min each
- Last 3 optimizations: ~18 min each

**Point of diminishing returns:** Success rate < 20% and time > 15 min per optimization.

### Real-World Benchmarks

**Cumulative across sessions:**
- 23 proofs optimized
- ~108 lines removed
- ~34% token reduction average
- ~68% reduction per optimized proof
- 100% compilation success (with multi-candidate approach)

**Technique effectiveness:**
1. let+have+exact: 50% of all savings, 60-80% per instance
2. Smart ext: 50% reduction, no clarity loss
3. ext-simp chains: Saves ≥2 lines when natural
4. rwa: Instant wins, zero risk
5. ext+rfl → rfl: High value when works

### Related References

- [tactics-reference.md](tactics-reference.md) - Tactic catalog
- [domain-patterns.md](domain-patterns.md) - Domain-specific patterns
- [mathlib-style.md](mathlib-style.md) - Style conventions
