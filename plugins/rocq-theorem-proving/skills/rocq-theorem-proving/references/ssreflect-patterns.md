# SSReflect Patterns and Idioms

This guide covers SSReflect (Small Scale Reflection), the proof language used by MathComp. SSReflect provides a more explicit, composable, and predictable style for proof development.

**Philosophy:** Explicit bookkeeping, stack-based reasoning, boolean reflection, compositional tactics.

**When to use:** MathComp projects, algebraic proofs, when you want predictable tactic behavior.

---

## Table of Contents

1. [Core Principles](#core-principles)
2. [Basic Stack Operations](#basic-stack-operations)
3. [Rewriting Patterns](#rewriting-patterns)
4. [Case Analysis](#case-analysis)
5. [Induction](#induction)
6. [Views](#views)
7. [Bookkeeping](#bookkeeping)
8. [Closing Tactics](#closing-tactics)
9. [Boolean Reflection](#boolean-reflection)
10. [Common Idioms](#common-idioms)
11. [Comparison with Standard Coq](#comparison-with-standard-coq)

---

## Core Principles

### 1. Stack-Based Reasoning

SSReflect treats the proof state as a stack:
- Goal is at the top
- Hypotheses are in the context (stack below)
- Tactics manipulate this stack

**Stack operations:**
- `move=>` - Pop from goal to context (like `intro`)
- `move:` - Push from context to goal (like `revert`)
- `case:` - Case analysis on top of stack
- `elim:` - Induction on top of stack
- `apply:` - Apply lemma

### 2. Explicit Bookkeeping

Everything is explicit:
- Name introductions: `move=> x` not just `intro`
- Rewrite clearing: `rewrite {}H` clears H after rewriting
- Pattern matching: `case: n => [| m]` not implicit

### 3. Boolean Reflection

Prefer `bool` over `Prop` when possible:
- `b = true` rather than `P : Prop`
- Enables computation, decision procedures
- Views connect bool and Prop

---

## Basic Stack Operations

### `move` - The Universal Tactic

**Syntax:** `move: source => destination`

**Moving from context to goal:**
```coq
move: H.           (* Generalize H - push to goal *)
move: x y H.       (* Generalize multiple *)
```

**Moving from goal to context:**
```coq
move=> x.          (* Introduce x - pop from goal *)
move=> x y H.      (* Introduce multiple *)
move=> *.          (* Introduce all *)
```

**Renaming:**
```coq
move: H => H'.     (* Rename H to H' *)
```

**Introduction patterns:**
```coq
move=> [x | y].    (* Case split on or *)
move=> [x y].      (* Split and *)
move=> x /=.       (* Introduce and simplify *)
move=> x {H}.      (* Introduce x and clear H *)
```

**Examples:**
```coq
(* Standard: *)
Goal forall n m : nat, n = m -> n + 0 = m.
Proof.
  intros n m H.

(* SSReflect: *)
Goal forall n m : nat, n = m -> n + 0 = m.
Proof.
  move=> n m H.    (* More explicit *)
```

### Combining move with other tactics

```coq
move=> x; case: x => [| n].    (* Intro then case *)
move: H; apply.                 (* Generalize then apply *)
move=> /= n.                    (* Intro with simplification *)
move=> {H} x.                   (* Intro x, clear H *)
```

---

## Rewriting Patterns

### Basic Rewriting

**Syntax:** `rewrite lemma` or `rewrite -lemma` (reverse)

```coq
rewrite H.         (* Rewrite using H *)
rewrite -H.        (* Reverse direction (not <-) *)
rewrite /def.      (* Unfold definition *)
rewrite !H.        (* Rewrite as many times as possible *)
rewrite ?H.        (* Rewrite if applies, don't fail *)
rewrite 2!H.       (* Rewrite exactly twice *)
```

### Rewrite Patterns with Clearing

```coq
rewrite {}H.       (* Rewrite and clear H *)
rewrite {H}E.      (* Rewrite with E, clear H *)
```

### Rewrite with Selection

```coq
(* Rewrite only in specific places *)
rewrite [X in _ = X]H.     (* Rewrite only in RHS *)
rewrite [in X + _]H.       (* Rewrite in first arg of + *)
rewrite [X in Y]H.         (* Rewrite X in pattern Y *)
```

**Examples:**
```coq
Goal forall n : nat, n + 0 + (n + 0) = n + n.
Proof.
  move=> n.
  (* Rewrite only second occurrence *)
  rewrite [in X + _]addnO.  (* or addnO in MathComp *)
  rewrite [in _ + X]addnO.
  reflexivity.
Qed.
```

### Chaining Rewrites

```coq
rewrite H1 H2 H3.          (* Multiple rewrites *)
rewrite -H1 H2 -H3.        (* Mixed directions *)
rewrite /def1 /def2.       (* Multiple unfolds *)
rewrite !addnA.            (* Associativity repeatedly *)
```

### Rewrite with Simplification

```coq
rewrite /=.        (* Just simplify, don't rewrite *)
rewrite H /=.      (* Rewrite then simplify *)
```

---

## Case Analysis

### `case` - SSReflect Case Analysis

**Basic usage:**
```coq
case: x.           (* Case on x *)
case: x => [| n].  (* With intro pattern *)
```

**With equation remembering:**
```coq
case E: x => [| n].    (* Remember x = ... as E *)
```

**Examples:**
```coq
(* Natural number case *)
Lemma nat_case : forall n : nat, {n = 0} + {n <> 0}.
Proof.
  case.
  - left. reflexivity.      (* n = 0 case *)
  - move=> m. right. discriminate.  (* n = S m case *)
Qed.

(* With intro pattern *)
Lemma add_cases n m : n + m = 0 -> n = 0.
Proof.
  case: n => [| k] //=.     (* [| k] names S case *)
  - reflexivity.            (* n = 0 *)
  - discriminate.           (* n = S k, 0 = S _ + _ impossible *)
Qed.
```

### Boolean Case Analysis

```coq
case: (b : bool).      (* Case on boolean *)
case: ifP => [H | H].  (* Case on if with proof *)
```

**With boolean reflection:**
```coq
case: (ltnP n m) => [H | H].
(* ltnP provides view: true case gives n < m, false gives m <= n *)
```

---

## Induction

### `elim` - SSReflect Induction

**Basic usage:**
```coq
elim: n.           (* Induction on n *)
elim: n => [| m IHm].  (* With intro pattern *)
```

**Examples:**
```coq
Lemma addn0 : forall n, n + 0 = n.
Proof.
  elim=> [| n IHn].
  - reflexivity.     (* Base case: 0 + 0 = 0 *)
  - by rewrite IHn.  (* Step: S n + 0 = S n *)
Qed.
```

**With generalizing:**
```coq
elim: n m => [| n IHn] m.
(* Generalizes m before induction on n *)
```

**Custom induction:**
```coq
elim/custom_ind: n => [base_case | step_case IH].
```

---

## Views

Views are the bridge between `bool` and `Prop`.

### View Syntax

**Apply view to hypothesis:**
```coq
move/view: H.      (* Transform H using view *)
```

**Apply view to goal:**
```coq
apply/view.        (* Transform goal using view *)
```

**Common views:**
```coq
(* Reflection views *)
move/eqP: H.       (* H : (n == m) = true   becomes   H : n = m *)
apply/eqP.         (* Goal: n = m           becomes   (n == m) = true *)

move/andP: H.      (* H : b1 && b2 = true   becomes   H : b1 = true /\ b2 = true *)
move/orP: H.       (* H : b1 || b2 = true   becomes   H : b1 = true \/ b2 = true *)
```

### View Examples

```coq
Require Import mathcomp.ssreflect.ssreflect.
Require Import mathcomp.ssreflect.ssrbool.
Require Import mathcomp.ssreflect.eqtype.
Require Import mathcomp.ssreflect.ssrnat.

Lemma eqP_example n m : (n == m) = true -> n = m.
Proof.
  move/eqP.          (* View: bool eq to Prop eq *)
  (* Now have: n = m ⊢ n = m *)
  by [].
Qed.

Lemma andP_example b1 b2 : b1 && b2 -> b1.
Proof.
  move/andP => [H1 H2].  (* Split conjunction *)
  exact H1.
Qed.
```

### Combining Views

```coq
move/view1/view2: H.   (* Apply view1, then view2 *)
apply/view1/view2.     (* Apply views to goal *)
```

---

## Bookkeeping

SSReflect provides precise control over context.

### Clearing

```coq
{H}            (* Clear H *)
{H1 H2}        (* Clear multiple *)
{->}           (* Clear after rewriting *)
```

**In tactics:**
```coq
move=> {H} x.          (* Intro x, clear H *)
rewrite {}H.           (* Rewrite and clear H *)
case: x => {x} [| n].  (* Case and clear x *)
```

### Naming and Wildcard

```coq
move=> _.      (* Intro and discard (anonymous) *)
move=> ?.      (* Let Coq choose name *)
case=> [| ?].  (* Wildcard in pattern *)
```

### Equation Remembering

```coq
case E: x => [| n].    (* Remember equation as E *)
elim E: n => [| m IHm].
```

---

## Closing Tactics

### `by` - Close with Simple Tactics

**Syntax:** `by tactic` or `by []`

```coq
by [].             (* Close trivially *)
by reflexivity.    (* Close with reflexivity *)
by apply: H.       (* Apply H and close *)
by rewrite H.      (* Rewrite and close *)
```

**Examples:**
```coq
Lemma trivial n : n = n.
Proof. by []. Qed.

Lemma add_comm n m : n + m = m + n.
Proof. by rewrite addnC. Qed.  (* addnC is commutativity *)
```

### `done` - Solve Goal

**Similar to `by []` but doesn't take argument.**

```coq
move=> n.
done.              (* Close with trivial tactics *)
```

**What `done` tries:**
- reflexivity
- assumption
- discriminate
- contradiction

### `//` - Automatic Cleanup

**Suffix: try to close subgoals.**

```coq
case: n => [| m] //.
(* Tries to close each branch automatically *)
- (* Only non-trivial goals remain *)
```

**Infix: try to close immediately.**

```coq
case: n => // m.
(* Closes first branch if trivial, introduces m in second *)
```

---

## Boolean Reflection

### Core Idea

**Use `bool` for computation, `Prop` for logic.**

```coq
(* Boolean predicate *)
Definition is_even n := ~~ (odd n).

(* Reflection lemma *)
Lemma is_evenP n : reflect (exists k, n = k + k) (is_even n).
```

### Reflect Inductive

```coq
Inductive reflect (P : Prop) : bool -> Type :=
| ReflectT : P -> reflect P true
| ReflectF : ~ P -> reflect P false.
```

**Standard views:**
- `eqP` : `reflect (x = y) (x == y)`
- `andP` : `reflect (P /\ Q) (p && q)`
- `orP` : `reflect (P \/ Q) (p || q)`
- `nandP`, `norP`, `implyP`, etc.

### Using Reflection

```coq
Lemma reflect_example n m :
  n == m -> n + 1 = m + 1.
Proof.
  move/eqP => Hnm.   (* View: bool eq to Prop eq *)
  by rewrite Hnm.
Qed.
```

**Decision procedure:**
```coq
(* Decide using computation *)
if n == m then ... else ...

(* Proof by computation *)
Lemma concrete : 5 == 3 = false.
Proof. by []. Qed.  (* Computed *)
```

---

## Common Idioms

### Idiom: Case and intro

```coq
case: x => [| n].
(* Prefer over: case x. intros. *)
```

### Idiom: Rewrite and close

```coq
by rewrite H.
(* Prefer over: rewrite H. reflexivity. *)
```

### Idiom: Generalize before induction

```coq
elim: n m => [| n IHn] m.
(* Generalizes m automatically *)
(* Prefer over: revert m. induction n. intro m. *)
```

### Idiom: Clear as you go

```coq
move=> {H} x.
rewrite {}H.
(* Keep context clean *)
```

### Idiom: Case with equation

```coq
case E: (f x) => [| y].
(* Remember what case you're in *)
```

### Idiom: Apply with views

```coq
apply/eqP.
apply/andP; split.
(* Bridge bool and Prop *)
```

### Idiom: Simplification during intro

```coq
move=> /= x.
(* Simplify while introducing *)
```

---

## Comparison with Standard Coq

| Task | Standard Coq | SSReflect |
|------|--------------|-----------|
| Introduce | `intros x y.` | `move=> x y.` |
| Generalize | `revert H.` | `move: H.` |
| Rename | `rename H into H'.` | `move: H => H'.` |
| Case | `destruct x.` | `case: x.` |
| Induction | `induction n.` | `elim: n.` |
| Rewrite | `rewrite H.` | `rewrite H.` (same!) |
| Rewrite reverse | `rewrite <- H.` | `rewrite -H.` |
| Rewrite & clear | `rewrite H. clear H.` | `rewrite {}H.` |
| Apply | `apply H.` | `apply: H.` or `apply/H.` |
| Close trivial | `reflexivity.` | `by [].` |
| Case with eq | `destruct x eqn:E.` | `case E: x.` |

### Philosophy Differences

**Standard Coq:**
- Implicit: tactics guess what you want
- Flexible: multiple ways to do things
- Automation-friendly: `auto`, `eauto`, `firstorder`

**SSReflect:**
- Explicit: you say exactly what you want
- Consistent: one clear way to do things
- Computation-friendly: boolean reflection, `by []`

**When to use each:**
- **Standard Coq:** General theorem proving, when you want automation
- **SSReflect:** Algebraic proofs, large developments, when you want control

---

## SSReflect Patterns Cookbook

### Pattern: Induction with generalization

```coq
Lemma example : forall n m, P n m.
Proof.
  (* Generalize m before induction *)
  elim=> [| n IHn] m.
  - (* base case with m *)
  - (* step case with m and IHn *)
Qed.
```

### Pattern: Case analysis with multiple branches

```coq
case: x => [| [| n]] //.
- (* x = 0, non-trivial *)
- (* x = 1, non-trivial *)
(* x = S (S n), trivial branches closed by // *)
```

### Pattern: Rewrite chain with simplification

```coq
rewrite /f /g H1 H2 /=.
(* Unfold f, unfold g, rewrite H1, H2, simplify *)
```

### Pattern: Apply with split

```coq
apply/andP; split.
- (* Prove first conjunct *)
- (* Prove second conjunct *)
```

### Pattern: Case on boolean with views

```coq
case: ifP => [H | H].
- (* true case with proof *)
- (* false case with proof *)
```

### Pattern: Induction with intermediate have

```coq
elim: n => [| n IHn].
- (* base case *)
- have H: (intermediate fact). { by apply: IHn. }
  (* use H to prove goal *)
```

---

## Advanced Patterns

### Pattern: Under modality (rewrite under binders)

```coq
Require Import mathcomp.ssreflect.under.

under eq_map => i.
  rewrite somelemma.
over.
```

### Pattern: Setoid rewriting

```coq
rewrite (eqtype someEq).
(* Use equivalence for rewriting *)
```

### Pattern: Big operator manipulation

```coq
Require Import mathcomp.ssreflect.bigop.

rewrite big_cons.      (* Expand one step *)
rewrite big_nil.       (* Empty sum *)
rewrite big_nat_recr.  (* Recurrence on right *)
```

### Pattern: View with case split

```coq
case/andP: H => [H1 H2].
(* Case and apply view *)
```

---

## Common Mistakes

### Mistake 1: Forgetting `move=>`

```coq
(* ❌ BAD *)
case: n.
intro.  (* Standard Coq style creeping in *)

(* ✅ GOOD *)
case: n => [| k].
```

### Mistake 2: Not using views

```coq
(* ❌ BAD *)
have H: (n == m) = true.
destruct H. (* Can't destruct bool! *)

(* ✅ GOOD *)
have/eqP H: (n == m).  (* View to Prop *)
```

### Mistake 3: Forgetting simplification

```coq
(* ❌ LESS EFFICIENT *)
simpl.
move=> x.

(* ✅ BETTER *)
move=> /= x.
```

### Mistake 4: Not clearing

```coq
(* ❌ CLUTTERED *)
move=> H x.
(* H clutters context *)

(* ✅ CLEAN *)
move=> {H} x.
(* or *)
rewrite {}H.
```

---

## See Also

- [rocq-phrasebook.md](rocq-phrasebook.md) - General proof patterns
- [tactics-reference.md](tactics-reference.md) - All tactics including SSReflect
- [stdlib-guide.md](stdlib-guide.md) - Finding lemmas
- [Mathematical Components Book](https://math-comp.github.io/mcb/)
- [SSReflect Manual](https://coq.inria.fr/refman/proof-engine/ssreflect-proof-language.html)

---

**Learning Resources:**
- [MathComp Book](https://math-comp.github.io/mcb/) - Comprehensive SSReflect guide
- [SSReflect Tutorial](https://hal.inria.fr/inria-00258384v11/document) - Original SSReflect paper
- [MathComp Documentation](https://math-comp.github.io/) - Library documentation
