# Proof Golfing: Simplifying Proofs After Compilation

## TLDR

**Core principle:** First make it compile, then make it clean.

**When to use:** After `dune build` or `coqc` succeeds on stable files. Expected 20-40% reduction with careful optimization.

**When NOT to use:** Active development, already-optimized code (MathComp-quality), or files in flux.

**Critical:** MUST verify that optimizations don't harm readability. Code is read more than written.

## Quick Reference: Pattern Priority

| Pattern | Savings | Risk | Priority | Notes |
|---------|---------|------|----------|-------|
| `auto` → simpler tactic | Variable | Zero | ⭐⭐⭐⭐⭐ | `auto` often overkill |
| `intros; exact` → term | 60-80% | Low | ⭐⭐⭐⭐⭐ | Direct term when simple |
| `simpl; reflexivity` → `reflexivity` | 50% | Zero | ⭐⭐⭐⭐⭐ | `reflexivity` simplifies |
| `rewrite H; reflexivity` → conversion | 50-70% | Low | ⭐⭐⭐⭐⭐ | When definitional |
| Single-use assert inline | 40-60% | Low | ⭐⭐⭐⭐ | If term is simple |
| `by []` for trivial (SSR) | 70% | Zero | ⭐⭐⭐⭐⭐ | SSReflect: instant close |
| `move=> /= x` vs separate | 50% | Zero | ⭐⭐⭐⭐ | SSReflect: combine ops |
| `rewrite {}H` vs keep | Clarity | Zero | ⭐⭐⭐⭐ | SSReflect: clear as go |
| Tactic sequence → automation | 50-80% | Medium | ⭐⭐⭐ | `lia`, `ring`, `congruence` |
| Multiple destruct → pattern | 30-50% | Low | ⭐⭐⭐ | Deep patterns |
| `trivial` → `assumption` | 0% | Zero | ⭐⭐ | Clarity only |

**ROI Strategy:** Do ⭐⭐⭐⭐⭐ first (instant wins), then ⭐⭐⭐⭐ (quick verification), skip lower priority if time-limited.

## Critical Safety Warnings

### The Readability vs Size Tradeoff

**Key principle:** Smaller isn't always better.

**Readability matters when:**
- Proof is non-trivial (>5 lines)
- Mathematical insight is encoded
- Others will maintain code
- You'll forget the trick in 6 months

**Size matters when:**
- Proof is trivial (reflexivity, contradiction)
- Pattern is standard (repeated 10+ times in file)
- Optimization makes structure clearer

### When NOT to Optimize

**Skip if ANY of these:**
- ❌ Assert used ≥2 times
- ❌ Semantic naming aids understanding
- ❌ Proof structure documents reasoning
- ❌ Would create deeply nested terms
- ❌ Maintainability cost > space savings

### Saturation Indicators

**Stop when:**
- ✋ Optimization success rate < 30%
- ✋ Time per optimization > 10 minutes
- ✋ Debating trivial 1-line savings
- ✋ Breaking proof modularity

## High-Priority Patterns (⭐⭐⭐⭐⭐)

### Pattern 1: Remove Unnecessary `auto`

`auto` is often overkill for simple goals.

```coq
(* Before *)
Proof.
  intros n m H.
  auto.
Qed.

(* After *)
Proof.
  intros n m H.
  assumption.  (* Or: exact H. *)
Qed.
```

**When:** `auto` is sole tactic on simple goal
**Better alternatives:**
- `assumption` - for hypothesis match
- `reflexivity` - for reflexive goals
- `apply H` - when you know the lemma
- `easy` - for slightly harder trivial goals

**Savings:** Clarity, compilation speed
**Risk:** Zero (if build still passes)

### Pattern 2: `intros; exact` → Direct Term

Convert tactic proofs to proof terms when simple.

```coq
(* Before *)
Lemma add_comm_example : forall n m, n + m = m + n.
Proof.
  intros n m.
  exact (Nat.add_comm n m).
Qed.

(* After *)
Lemma add_comm_example : forall n m, n + m = m + n.
Proof. exact Nat.add_comm. Qed.

(* Or even shorter *)
Definition add_comm_example : forall n m, n + m = m + n := Nat.add_comm.
```

**When to apply:**
- Proof is just `intros` then `exact`
- The proof term is simple (not deeply nested)
- No complex pattern matching needed

**SSReflect version:**
```coq
(* Before *)
Lemma example n m : n + m = m + n.
Proof.
  move=> //.  (* Or: by apply: addnC. *)
Qed.

(* After *)
Lemma example n m : n + m = m + n.
Proof. by []. Qed.  (* Or just: Proof. exact: addnC. Qed. *)
```

**Savings:** 60-80% reduction
**Risk:** Low (if term is truly simple)

### Pattern 3: `simpl; reflexivity` → `reflexivity`

`reflexivity` automatically simplifies.

```coq
(* Before *)
Lemma add_0_l : forall n, 0 + n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

(* After *)
Lemma add_0_l : forall n, 0 + n = n.
Proof.
  intro n.
  reflexivity.
Qed.
```

**When:** `simpl` followed by `reflexivity`
**Why:** `reflexivity` performs reduction automatically
**Savings:** 50% reduction
**Risk:** Zero

**SSReflect version:**
```coq
(* Before *)
Proof.
  move=> n /=.
  by [].
Qed.

(* After - /= is redundant *)
Proof.
  move=> n.
  by [].
Qed.
```

### Pattern 4: Definitional Equality → Remove Rewrite

When equality is definitional, no rewrite needed.

```coq
(* Before *)
Lemma example : forall n, n + 0 = n.
Proof.
  intro n.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

(* After - if equality is definitional *)
Lemma example_def : forall l, l ++ [] = l.
Proof.
  intro l.
  (* For lists, ++ [] is NOT definitional, rewrite needed *)
  rewrite app_nil_r.
  reflexivity.
Qed.

(* But for this: *)
Lemma example_def2 : forall n, 0 + n = n.
Proof.
  intro n.
  (* 0 + n reduces to n by definition *)
  reflexivity.  (* No rewrite needed! *)
Qed.
```

**When:** Equality holds by reduction (compute, simpl)
**Test:** Try `reflexivity` first, add rewrites only if needed
**Savings:** 50-70% reduction
**Risk:** Low (compilation will fail if wrong)

### Pattern 5: SSReflect `by []` for Trivial Goals

SSReflect's `by []` tries multiple closing tactics.

```coq
From mathcomp Require Import all_ssreflect.

(* Before *)
Lemma trivial_example n : n = n.
Proof.
  reflexivity.
Qed.

(* After - SSReflect style *)
Lemma trivial_example n : n = n.
Proof. by []. Qed.

(* Or combined with intro *)
Lemma add_same n m : n = m -> n = m.
Proof. by []. Qed.  (* Handles intro + assumption *)
```

**What `by []` tries:**
- `reflexivity`
- `assumption`
- `discriminate`
- `contradiction`
- Simple `auto`

**Savings:** 70% reduction for trivial proofs
**Risk:** Zero
**Style:** Idiomatic SSReflect

### Pattern 6: SSReflect Combined Operations

SSReflect allows combining operations.

```coq
(* Before *)
Proof.
  move=> x.
  simpl.
  (* ... *)

(* After *)
Proof.
  move=> /= x.  (* Intro and simplify *)
  (* ... *)

(* More examples *)
move=> {H} x.     (* Intro x, clear H *)
rewrite {}H.      (* Rewrite and clear H *)
case: x => //.    (* Case and try to close *)
by rewrite H.     (* Rewrite and close *)
```

**Savings:** 50% reduction per combination
**Risk:** Zero
**Principle:** SSReflect is designed for composition

---

## Medium-Priority Patterns (⭐⭐⭐⭐)

### Pattern 7: Single-Use Assert Inlining

Inline assertions used only once.

```coq
(* Before *)
Lemma example n m : n < m -> n + 1 <= m.
Proof.
  intro H.
  assert (Hle : n <= m - 1). { lia. }
  assert (Hfinal : n + 1 <= m). { lia. }
  exact Hfinal.
Qed.

(* After *)
Lemma example n m : n < m -> n + 1 <= m.
Proof.
  intro H.
  lia.  (* Solves directly *)
Qed.
```

**When to inline:**
- ✅ Assert used exactly once
- ✅ Proof term is simple (< 40 chars)
- ✅ No important semantic meaning in name
- ✅ Doesn't break proof narrative

**When NOT to inline:**
- ❌ Assert used multiple times
- ❌ Name documents mathematical concept
- ❌ Part of structured proof
- ❌ Long or complex proof term

**Savings:** 40-60% per instance
**Risk:** Low (if truly single-use)

**SSReflect version:**
```coq
(* Before *)
have H: intermediate. { proof. }
use H once.

(* After - inline if simple *)
direct_use_of_proof.
```

### Pattern 8: Tactic Sequences → Automation

Replace tactic sequences with decision procedures.

```coq
(* Before *)
Lemma arith_example n m : n + m <= n + m.
Proof.
  intros.
  apply Nat.le_refl.
Qed.

(* After *)
Require Import Lia.
Lemma arith_example n m : n + m <= n + m.
Proof. lia. Qed.

(* Before *)
Lemma ring_example x y : (x + y) * (x + y) = x * x + 2 * x * y + y * y.
Proof.
  ring.  (* Already optimal! *)
Qed.
```

**Automation tactics:**
- `lia` - linear integer arithmetic
- `lra` - linear real arithmetic
- `ring` - ring equations
- `field` - field equations
- `congruence` - equality reasoning
- `tauto` - propositional tautologies
- `easy` - simple goals
- `firstorder` - first-order logic

**Savings:** 50-80% when applicable
**Risk:** Medium (know what automation handles)
**When:** Tactic sequence matches automation domain

### Pattern 9: Deep Pattern Matching

Use nested patterns instead of multiple destructs.

```coq
(* Before *)
Proof.
  intros n.
  destruct n as [| n'].
  - (* 0 case *)
  - destruct n' as [| n''].
    + (* 1 case *)
    + (* >= 2 case *)
Qed.

(* After *)
Proof.
  intros [| [| n]].
  - (* 0 case *)
  - (* 1 case *)
  - (* >= 2 case *)
Qed.
```

**SSReflect version:**
```coq
(* Before *)
case: n => [| n'].
- (* 0 *)
- case: n' => [| n''].
  + (* 1 *)
  + (* >= 2 *)

(* After *)
case: n => [| [| n]].
- (* 0 *)
- (* 1 *)
- (* >= 2 *)
```

**Savings:** 30-50% reduction
**Risk:** Low
**Readability:** Often clearer with patterns

### Pattern 10: Eliminate Intermediate Goals

Sometimes proofs have unnecessary intermediate steps.

```coq
(* Before *)
Lemma example n : n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - (* Base *)
    simpl. reflexivity.
  - (* Step *)
    simpl. rewrite IHn'. reflexivity.
Qed.

(* After - more direct *)
Lemma example n : n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

(* Or with automation *)
Lemma example n : n + 0 = n.
Proof.
  induction n; simpl; auto.
Qed.
```

**When:** Intermediate steps don't add clarity
**Savings:** Variable
**Risk:** Low (test with build)

---

## Domain-Specific Patterns

### SSReflect Golfing

SSReflect has unique optimization opportunities.

#### Clear as You Go

```coq
(* Before *)
move=> H x.
(* use H once *)
clear H.

(* After *)
move=> {H} x.  (* Intro x, clear H *)

(* Or *)
rewrite H.
clear H.

(* After *)
rewrite {}H.   (* Rewrite and clear *)
```

#### Closing Tactics

```coq
(* Long form *)
move=> H.
apply: H.
done.

(* Short form *)
by move=> H; apply: H.

(* Or *)
case: n => [| m] //.  (* // closes trivial branches *)
```

#### View Lemmas

```coq
(* Before *)
move=> H.
have /eqP Heq: (n == m) = true. { apply H. }
(* use Heq : n = m *)

(* After *)
move/eqP=> Heq.  (* Apply view during intro *)
```

### Standard Coq Golfing

#### Use `now`

```coq
(* Before *)
apply lemma.
auto.

(* After *)
now apply lemma.  (* Apply and close *)
```

#### Chained Tactics

```coq
(* Before *)
intro H.
destruct H as [H1 H2].
apply H1.

(* After *)
intros [H1 H2]; apply H1.
```

#### Semicolon Branching

```coq
(* Before *)
destruct b.
- reflexivity.
- reflexivity.

(* After *)
destruct b; reflexivity.
```

---

## Anti-Patterns (Don't Do This)

### Anti-Pattern 1: Over-Golfing

```coq
(* ❌ BAD: Unreadable *)
Lemma foo : forall n m k p, complex_property n m k p.
Proof. intros; repeat (destruct *; auto; try lia). Qed.

(* ✅ GOOD: Clear structure *)
Lemma foo : forall n m k p, complex_property n m k p.
Proof.
  intros n m k p.
  destruct n as [| n'].
  - (* n = 0 case *)
    lia.
  - (* n = S n' case *)
    destruct m as [| m'].
    + (* m = 0 *) auto.
    + (* m = S m' *) lia.
Qed.
```

### Anti-Pattern 2: Inlining Important Lemmas

```coq
(* ❌ BAD: Inline meaningful intermediate result *)
Lemma main_theorem : big_property.
Proof.
  (* 20 lines of proof inline *)
Qed.

(* ✅ GOOD: Factor out meaningful lemmas *)
Lemma key_insight : intermediate_property.
Proof. (* ... *) Qed.

Lemma main_theorem : big_property.
Proof.
  apply key_insight.
Qed.
```

### Anti-Pattern 3: Abusing Automation

```coq
(* ❌ BAD: Slow, opaque *)
Proof. intuition; firstorder; auto with *. Qed.

(* ✅ GOOD: Explicit, fast *)
Proof. split; [apply H1 | apply H2]. Qed.
```

---

## Optimization Workflow

### Step 1: Identify Candidates

Look for:
- Trivial proofs with multiple tactics
- Single-use assertions
- Redundant simplifications
- Standard patterns (like `intro; exact`)

### Step 2: Test Optimization

```bash
# Make the change
# Then immediately test
dune build  # or: coqc file.v

# If it fails, revert
# If it succeeds, review for readability
```

### Step 3: Readability Check

Ask yourself:
- Is the optimized version still clear?
- Would I understand this in 6 months?
- Does it document the proof strategy?

If "no" to any: **consider reverting**

### Step 4: Commit Atomic Changes

```bash
# One optimization pattern at a time
git add file.v
git commit -m "refactor: inline single-use assertion in theorem_name"

# Not:
git commit -m "golf proofs"  # Too vague!
```

---

## Measurement and Goals

### Before Optimizing

```bash
# Count lines
wc -l file.v

# Count proof lines (exclude definitions)
# Manually or with script
```

### After Optimizing

```bash
# Measure reduction
# Typical: 20-40% for already-decent code
# Possible: 50%+ for verbose initial drafts

# More important: readability maintained?
```

### Realistic Goals

**Don't expect:**
- MathComp-level terseness immediately
- 80% reductions (unless code was very redundant)
- Every proof to be 1-line

**Do expect:**
- 20-40% reduction in proof lines
- Clearer proof structure
- Faster compilation (less tactic overhead)

---

## Tools for Proof Golfing

### Manual Tools

```coq
(* Test if simpl needed *)
Goal P.
Proof.
  reflexivity.  (* Try without simpl first *)
Abort.

(* Test if automation works *)
Goal P.
Proof.
  lia.  (* or ring, auto, etc. *)
Abort.
```

### Search for Patterns

```bash
# Find all "simpl; reflexivity"
grep -A 1 "simpl\." file.v | grep "reflexivity"

# Find all "intro; exact"
grep -A 1 "intro " file.v | grep "exact"

# Find single-use assertions
# (Manually search for assert patterns)
```

---

## Priority Decision Tree

```
Is proof trivial (< 3 lines)?
├─ Yes → Try automation (lia, ring, auto)
│  ├─ Works → Use it ⭐⭐⭐⭐⭐
│  └─ Doesn't → Keep manual proof
│
└─ No → Is it standard pattern?
   ├─ intro; exact → Direct term ⭐⭐⭐⭐⭐
   ├─ simpl; reflexivity → Just reflexivity ⭐⭐⭐⭐⭐
   ├─ SSReflect combinable → Combine ⭐⭐⭐⭐
   ├─ Single-use assert → Consider inline ⭐⭐⭐⭐
   └─ Complex proof → Don't golf ⭐
```

---

## When to Stop

**Stop optimizing when:**
1. ✋ Build time for testing > time saved
2. ✋ Readability degrading
3. ✋ Success rate < 30%
4. ✋ File is stable and good enough

**Remember:** Perfect is the enemy of good.

Proofs don't need to be minimal, they need to be:
- Correct (compiles)
- Clear (understandable)
- Maintainable (modifiable)

---

## See Also

- [tactics-reference.md](tactics-reference.md) - Understand tactics for optimization
- [ssreflect-patterns.md](ssreflect-patterns.md) - SSReflect golfing patterns
- [rocq-phrasebook.md](rocq-phrasebook.md) - Alternative phrasings
- [compilation-errors.md](compilation-errors.md) - Fix broken optimizations

---

**Philosophy:** Proof golfing is like code refactoring. Do it to improve clarity and maintainability, not just to make numbers smaller. The best proof is the one that's easy to understand and modify.
