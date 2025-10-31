# Rocq/Coq Tactics Reference

This reference provides comprehensive guidance on essential Rocq/Coq tactics, when to use them, and common patterns. Includes both standard Coq tactics and SSReflect/MathComp tactics.

**For natural language translations:** See [rocq-phrasebook.md](rocq-phrasebook.md) for "Mathematical English to Rocq" patterns organized by proof situation.

## Quick Reference

| Want to... | Standard Coq | SSReflect |
|------------|-------------|-----------|
| Close with exact term | `exact` | `exact` |
| Apply lemma | `apply` | `apply:` or `apply/` |
| Rewrite once | `rewrite lemma` | `rewrite lemma` or `rewrite -lemma` |
| Normalize expression | `simpl`, `compute` | `simpl`, `/=` |
| Split cases | `destruct`, `case_eq` | `case:`, `case` |
| Prove exists | `exists witness` | `exists witness` |
| Prove and/iff | `split`, `constructor` | `split` |
| Prove function equality | `extensionality` | `apply: functional_extensionality` |
| Introduce assumptions | `intros` | `move=>` |
| Search for lemmas | `Search`, `SearchPattern` | `Search` |
| Automate | `auto`, `easy`, `lia`, `ring` | `by`, `done` |

The most important tactic is the one you understand!

## Table of Contents

1. [Core Introduction Tactics](#core-introduction-tactics)
2. [Application and Exact Tactics](#application-and-exact-tactics)
3. [Rewriting Tactics](#rewriting-tactics)
4. [Simplification Tactics](#simplification-tactics)
5. [Case Analysis Tactics](#case-analysis-tactics)
6. [Induction Tactics](#induction-tactics)
7. [Existential and Universal Tactics](#existential-and-universal-tactics)
8. [Automation Tactics](#automation-tactics)
9. [Decision Procedures](#decision-procedures)
10. [Specialized Domain Tactics](#specialized-domain-tactics)
11. [Equality and Congruence](#equality-and-congruence)
12. [Goal Management](#goal-management)
13. [SSReflect Tactics](#ssreflect-tactics)
14. [Advanced Tactics](#advanced-tactics)

---

## Core Introduction Tactics

### `intros` - Introduce Hypotheses

**What it does:** Moves universal quantifiers and implications from goal into context.

**Basic usage:**
```coq
intros.                (* Introduce all *)
intros x.              (* Introduce one, name it x *)
intros x y H.          (* Introduce multiple *)
intros [x | y].        (* Introduction with pattern matching *)
intros ?.              (* Let Coq choose name *)
```

**Examples:**
```coq
Goal forall n m : nat, n = m -> n + 0 = m.
Proof.
  intros n m H.        (* Context: n, m : nat, H : n = m *)
  (* Goal: n + 0 = m *)
```

**When to use:**
- Beginning of almost every proof
- To bring assumptions into context
- To name variables and hypotheses

**SSReflect equivalent:** `move=>`
```coq
move=> n m H.          (* Same as intros n m H *)
move=> *.              (* Introduce everything *)
```

### `intro` - Introduce One Hypothesis

**What it does:** Like `intros` but introduces exactly one assumption.

```coq
intro H.               (* Introduce and name it H *)
intro.                 (* Let Coq choose name *)
```

**When to use:**
- When you want fine control over each introduction
- For proofs of negation (`~P` becomes `P -> False`)

### `assumption` - Use Hypothesis Directly

**What it does:** Closes goal with exact match from context.

```coq
assumption.            (* Searches for matching hypothesis *)
```

**When to use:**
- Goal exactly matches a hypothesis
- Quick closure when obvious

**SSReflect equivalent:** `by []`

---

## Application and Exact Tactics

### `exact` - Close with Exact Term

**What it does:** Closes goal with a term of the exact right type.

```coq
exact H.               (* H has exactly the goal type *)
exact (f x y).         (* Apply function to get exact type *)
```

**Examples:**
```coq
Goal forall n : nat, n = n.
Proof.
  intro n.
  exact (eq_refl n).   (* eq_refl n : n = n *)
Qed.
```

**When to use:**
- You have exact proof term
- Closing goals with reflexivity, assumptions, or lemmas

**SSReflect equivalent:** Same (`exact`)

### `apply` - Backward Reasoning

**What it does:** Applies lemma/hypothesis to reduce goal.

**Basic usage:**
```coq
apply H.               (* H : P -> Q, goal Q becomes P *)
apply H in H'.         (* Forward: use H on H' *)
apply H with (x := t). (* Provide implicit argument *)
eapply H.              (* Leave unification variables *)
```

**Examples:**
```coq
Lemma example : forall n m : nat, n <= m -> n <= S m.
Proof.
  intros n m H.
  apply le_S.          (* le_S : forall n m, n <= m -> n <= S m *)
  exact H.
Qed.
```

**When to use:**
- Backward reasoning from goal
- Reducing goal to simpler one
- Using implications, universal statements

**SSReflect variants:**
```coq
apply: H.              (* SSReflect apply *)
apply/H.               (* Apply with view mechanism *)
```

### `refine` - Apply Partial Term

**What it does:** Applies term with holes, creates subgoals for holes.

```coq
refine (lemma _ _ ?).  (* ? creates subgoal *)
```

**When to use:**
- You know proof structure but not all details
- More control than `apply`
- Building complex proof terms

---

## Rewriting Tactics

### `rewrite` - Rewrite with Equality

**What it does:** Replaces term using equality.

**Basic usage:**
```coq
rewrite H.             (* Rewrite using H : x = y *)
rewrite <- H.          (* Rewrite in reverse direction *)
rewrite H1, H2, H3.    (* Multiple rewrites *)
rewrite H in H'.       (* Rewrite in hypothesis H' *)
rewrite H at n.        (* Rewrite only nth occurrence *)
```

**Examples:**
```coq
Lemma add_comm_example : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  rewrite Nat.add_comm. (* Use commutativity *)
  reflexivity.
Qed.
```

**Advanced usage:**
```coq
rewrite !H.            (* Rewrite as many times as possible *)
rewrite /definition.   (* Unfold definition while rewriting *)
rewrite -[X in _ = X]H. (* Rewrite only in specific position *)
```

**When to use:**
- Transforming expressions with equalities
- Most common tactic after `intros`
- Chaining equalities

**SSReflect enhancements:**
```coq
rewrite H.             (* Standard rewrite *)
rewrite -H.            (* Reverse (instead of <-) *)
rewrite {}H.           (* Rewrite and clear H *)
rewrite [LHS]H.        (* Rewrite only left-hand side *)
```

### `setoid_rewrite` - Rewrite with Custom Equivalences

**What it does:** Rewrite using equivalence relations (not just =).

```coq
setoid_rewrite H.      (* H uses custom equivalence *)
```

**When to use:**
- Working with custom equivalence relations
- Requires proper `Setoid` instances

**Requirements:**
```coq
Require Import Setoid.
```

### `replace` - Replace and Create Subgoal

**What it does:** Replaces term and creates equality subgoal.

```coq
replace X with Y.      (* Changes X to Y, must prove X = Y *)
replace X with Y by tactic. (* Prove equality immediately *)
```

**Examples:**
```coq
Lemma example : forall n : nat, n + 0 = n.
Proof.
  intro n.
  replace (n + 0) with n by (apply Nat.add_0_r).
  reflexivity.
Qed.
```

**When to use:**
- You know two things are equal but don't have the lemma handy
- Want to make replacement and prove equality separately

---

## Simplification Tactics

### `simpl` - Simplify by Reduction

**What it does:** Reduces fixpoint definitions and match expressions.

**Basic usage:**
```coq
simpl.                 (* Simplify goal *)
simpl in H.            (* Simplify hypothesis *)
simpl in *.            (* Simplify everywhere *)
simpl (f x).           (* Simplify specific term *)
```

**Examples:**
```coq
Fixpoint add (n m : nat) : nat :=
  match n with
  | 0 => m
  | S n' => S (add n' m)
  end.

Goal add 2 3 = 5.
Proof.
  simpl.               (* Reduces to: S (S (S (S (S 0)))) = 5 *)
```

**When to use:**
- After defining recursive functions
- To see "real" form of expressions
- Before pattern matching

**SSReflect shorthand:** `/=`
```coq
move=> /= n.           (* Introduce and simplify *)
```

### `unfold` - Unfold Definitions

**What it does:** Expands definition to its body.

```coq
unfold f.              (* Unfold definition of f *)
unfold f in H.         (* Unfold in hypothesis *)
unfold f at n.         (* Unfold only nth occurrence *)
```

**When to use:**
- Making definitions transparent
- Before rewriting through definitions
- Debugging what a term means

**Control:**
```coq
unfold f; fold f.      (* Unfold then re-fold *)
```

### `compute` / `vm_compute` / `native_compute` - Full Computation

**What it does:** Fully evaluates computable expressions.

```coq
compute.               (* Full reduction *)
vm_compute.            (* Faster with VM *)
native_compute.        (* Fastest, uses native code *)
```

**Examples:**
```coq
Goal 100 + 50 = 150.
Proof.
  compute.             (* Reduces to: 150 = 150 *)
  reflexivity.
Qed.
```

**When to use:**
- Numerical verification
- Fully evaluating computable functions
- `vm_compute` for large computations

### `cbv` / `lazy` / `cbn` - Controlled Reduction

**Fine-grained reduction strategies:**
```coq
cbv.                   (* Call-by-value *)
lazy.                  (* Call-by-need (lazy) *)
cbn.                   (* Call-by-name (recommended) *)
```

**Selective reduction:**
```coq
cbv [f g].             (* Reduce only f and g *)
cbv -[f g].            (* Reduce everything except f, g *)
```

**When to use:**
- Fine control over reduction
- `cbn` is usually the best default

---

## Case Analysis Tactics

### `destruct` - Case Analysis

**What it does:** Performs case analysis on term.

**Basic usage:**
```coq
destruct n.            (* Cases on nat: 0 and S n *)
destruct n as [| n'].  (* With names *)
destruct H as [HA | HB]. (* Cases on A \/ B *)
destruct H as [HA HB]. (* Cases on A /\ B *)
destruct n eqn:Heq.    (* Remember equality *)
```

**Examples:**
```coq
Lemma nat_cases : forall n : nat, n = 0 \/ exists m, n = S m.
Proof.
  intro n.
  destruct n as [| m].
  - left. reflexivity.
  - right. exists m. reflexivity.
Qed.
```

**Pattern matching:**
```coq
destruct n as [| [| n]]. (* Deep patterns: 0, 1, ≥2 *)
- (* n = 0 *)
- (* n = 1 *)
- (* n = S (S n) *)
```

**When to use:**
- Case analysis on inductive types
- Splitting or/and hypotheses
- Beginning of case-based proofs

**SSReflect equivalent:** `case:`

### `case_eq` - Destruct with Equation

**What it does:** Like `destruct` but remembers equation.

```coq
case_eq (f x); intros.
(* For each case, adds equation: f x = result *)
```

**When to use:**
- Need to remember what case you're in
- Generalizing before destruct

**SSReflect has better version:** `case: (f x) (erefl : f x = _)`

### `inversion` - Invert Inductive Hypothesis

**What it does:** Analyzes inductive hypothesis, extracting equalities.

```coq
inversion H.           (* Analyze inductive hypothesis *)
inversion H; subst.    (* Invert and substitute *)
inversion H as [x y Hxy]. (* With pattern *)
```

**Examples:**
```coq
Inductive even : nat -> Prop :=
| even_0 : even 0
| even_SS : forall n, even n -> even (S (S n)).

Lemma even_inv : forall n, even (S (S n)) -> even n.
Proof.
  intros n H.
  inversion H.         (* Extracts: even n *)
  assumption.
Qed.
```

**When to use:**
- Hypotheses about inductive types
- Extracting "how" something was constructed
- Getting impossible cases automatically

**Cleanup:**
```coq
inversion H; subst; clear H. (* Typical pattern *)
```

---

## Induction Tactics

### `induction` - Proof by Induction

**What it does:** Creates base case and inductive step.

**Basic usage:**
```coq
induction n.           (* Induction on nat *)
induction n as [| n' IHn']. (* With names *)
induction H.           (* Induction on inductive hypothesis *)
```

**Examples:**
```coq
Lemma add_0_r : forall n : nat, n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - (* Base: 0 + 0 = 0 *)
    reflexivity.
  - (* Step: S n' + 0 = S n', have IHn' : n' + 0 = n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.
```

**Generalizing before induction:**
```coq
revert m.              (* Move m back to goal *)
induction n.           (* Induction with m generalized *)
```

**When to use:**
- Proving properties of recursive structures
- Need inductive hypothesis
- Most `forall n : nat` proofs

**SSReflect equivalent:** `elim:`

### `elim` - Elimination Principle

**What it does:** Applies elimination principle directly.

```coq
elim H.                (* Apply eliminator for H's type *)
elim n using custom_ind. (* Use custom induction principle *)
```

**When to use:**
- Custom induction principles
- More control than `induction`
- SSReflect style prefers this

---

## Existential and Universal Tactics

### `exists` - Prove Existential

**What it does:** Provides witness for existential.

```coq
exists t.              (* For goal: exists x, P x *)
exists t1, t2, t3.     (* Multiple witnesses *)
eexists.               (* Let Coq figure out witness *)
```

**Examples:**
```coq
Lemma exists_example : exists n : nat, n + 5 = 8.
Proof.
  exists 3.
  reflexivity.
Qed.
```

**When to use:**
- Proving `exists x, P x`
- You know the witness
- `eexists` when witness is computable from rest of proof

### `specialize` - Instantiate Universal

**What it does:** Applies universal hypothesis to specific value.

```coq
specialize (H x).      (* H : forall x, P x becomes H : P x *)
specialize (H x y).    (* Multiple arguments *)
```

**Examples:**
```coq
Lemma spec_example : (forall n, n > 0 -> n > 0) -> 5 > 0.
Proof.
  intro H.
  specialize (H 5).    (* H : 5 > 0 -> 5 > 0 *)
```

**When to use:**
- Instantiating universals
- Replacing general hypothesis with specific case
- Be careful: destructive (replaces H)

**Non-destructive alternative:**
```coq
pose proof (H x) as Hx. (* Keep original H *)
```

---

## Automation Tactics

### `auto` - Simple Automation

**What it does:** Tries simple tactics (intros, apply, reflexivity).

```coq
auto.                  (* Basic automation *)
auto with database.    (* Use hint database *)
auto 10.               (* Depth limit *)
```

**When to use:**
- Finishing simple goals
- After setting up main structure
- Try as last resort

**Power levels:**
- `trivial` - Very weak (depth 0)
- `auto` - Weak (default depth 5)
- `auto 10` - Moderate
- `auto 100` - Strong but slow

### `eauto` - Auto with Existentials

**What it does:** Like `auto` but handles existential variables.

```coq
eauto.                 (* auto + existentials *)
eauto with database.
```

**When to use:**
- When `auto` fails due to existentials
- More powerful than `auto`
- Slightly slower

### `easy` - Stronger Simple Automation

**What it does:** `auto` + `trivial` + simple inversions.

```coq
easy.                  (* Strong simple automation *)
```

**When to use:**
- When `auto` isn't enough
- Still want predictable automation
- Recommended over complex `auto` invocations

### `tauto` - Propositional Tautology

**What it does:** Proves propositional tautologies.

```coq
tauto.                 (* Proves tautologies *)
```

**Examples:**
```coq
Lemma tauto_example : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  tauto.
Qed.
```

**When to use:**
- Pure propositional logic
- Complex boolean reasoning
- After reducing to propositional form

### `intuition` - Intuitionistic Tautology

**What it does:** Like `tauto` but intuitionistic.

```coq
intuition.             (* Intuitionistic tautology *)
intuition auto.        (* With automation for subgoals *)
```

**When to use:**
- Don't want to rely on classical logic
- Weaker than `tauto` but more principled

---

## Decision Procedures

### `lia` - Linear Integer Arithmetic

**What it does:** Decides linear integer arithmetic.

```coq
lia.                   (* Formerly omega *)
```

**Requires:**
```coq
Require Import Lia.
```

**Examples:**
```coq
Lemma lia_example : forall n m : nat,
  n <= m -> n <= m + 1.
Proof.
  intros. lia.
Qed.
```

**Can prove:**
- Linear inequalities over integers/nats
- Equations and inequalities
- Combined with basic arithmetic

**When to use:**
- Any linear arithmetic goal
- After reducing to arithmetic
- Very powerful and reliable

### `lia` / `lra` / `nra` / `nia` - Arithmetic Family

```coq
lia.                   (* Linear Integer Arithmetic *)
lra.                   (* Linear Real Arithmetic *)
nia.                   (* Nonlinear Integer Arithmetic *)
nra.                   (* Nonlinear Real Arithmetic *)
```

**Requires:**
```coq
Require Import Lra.    (* For lra *)
Require Import Nia.    (* For nia *)
```

**When to use which:**
- `lia`: Integer/nat linear arithmetic (most common)
- `lra`: Real number linear arithmetic
- `nia`: Integer polynomial arithmetic
- `nra`: Real polynomial arithmetic (experimental)

### `ring` - Ring Equality

**What it does:** Proves equalities in rings.

```coq
ring.                  (* Proves ring equations *)
ring_simplify.         (* Normalizes but doesn't close *)
```

**Requires:**
```coq
Require Import Ring.
```

**Examples:**
```coq
Lemma ring_example : forall x y : Z,
  (x + y) * (x - y) = x * x - y * y.
Proof.
  intros. ring.
Qed.
```

**When to use:**
- Algebraic identities in rings
- Polynomial equalities
- After expanding expressions

### `field` - Field Equality

**What it does:** Proves equalities in fields (handles division).

```coq
field.                 (* Proves field equations *)
field_simplify.        (* Normalizes with denominators *)
```

**Requires:**
```coq
Require Import Field.
```

**When to use:**
- Working with real numbers, rationals
- Division involved
- After setting up non-zero conditions

### `congruence` - Equality Decision Procedure

**What it does:** Decides equality reasoning with congruence closure.

```coq
congruence.            (* Powerful equality reasoning *)
```

**Examples:**
```coq
Lemma cong_example : forall f x y,
  x = y -> f x = f y.
Proof.
  congruence.
Qed.
```

**When to use:**
- Complex equality reasoning
- Multiple equalities to combine
- With function applications
- Very powerful, try it!

---

## Specialized Domain Tactics

### `reflexivity` - Prove Reflexive Equality

**What it does:** Proves `x = x` (and convertible terms).

```coq
reflexivity.           (* Proves definitional equality *)
```

**When to use:**
- Closing equality goals
- After simplification
- Most common closing tactic

**SSReflect equivalent:** `by []`

### `symmetry` - Flip Equality

**What it does:** Changes `x = y` to `y = x`.

```coq
symmetry.              (* x = y becomes y = x *)
symmetry in H.         (* Flip hypothesis *)
```

**When to use:**
- Wrong direction of equality
- Before rewriting

### `transitivity` - Transitivity of Equality

**What it does:** For `x = z`, suffices to find `y` with `x = y` and `y = z`.

```coq
transitivity y.        (* x = z becomes x = y and y = z *)
```

**When to use:**
- Chaining equalities
- Calculation chains
- Before rewrite sequences

### `f_equal` - Congruence

**What it does:** For `f x = f y`, reduces to `x = y`.

```coq
f_equal.               (* Applies congruence *)
```

**When to use:**
- Proving function applications equal
- When arguments are equal

### `injection` - Injectivity

**What it does:** Uses constructor injectivity.

```coq
injection H.           (* From S n = S m get n = m *)
injection H as Heq.    (* Name resulting equality *)
```

**When to use:**
- Hypotheses with same constructor
- Extracting equalities from constructor equality

### `discriminate` - Constructor Distinction

**What it does:** Proves False from different constructors being equal.

```coq
discriminate.          (* 0 = S n is absurd *)
discriminate H.        (* Use hypothesis H *)
```

**When to use:**
- Impossible cases
- Different constructors equal

---

## Equality and Congruence

### `extensionality` - Function Extensionality

**What it does:** For `f = g`, reduces to `forall x, f x = g x`.

```coq
extensionality x.      (* Introduces x, goal becomes f x = g x *)
```

**Requires:**
```coq
Require Import FunctionalExtensionality.
```

**When to use:**
- Proving function equality
- Different definitions, same behavior

### `apply functional_extensionality` - Alternative Form

```coq
apply functional_extensionality.
intro x.
(* Same effect as extensionality *)
```

### `subst` - Substitute Equalities

**What it does:** Substitutes all equalities of form `x = t` or `t = x`.

```coq
subst.                 (* Substitute all *)
subst x.               (* Substitute only x *)
```

**When to use:**
- After `inversion`
- Cleaning up equalities
- Before finishing proof

**Typical pattern:**
```coq
inversion H; subst; clear H.
```

---

## Goal Management

### Multiple Goals

**Focusing on specific goal:**
```coq
1: { tactics }.        (* Solve goal 1 *)
2: { tactics }.        (* Solve goal 2 *)
all: tactics.          (* Apply to all goals *)
```

**Bullets:**
```coq
- tactic.              (* First subgoal *)
- tactic.              (* Second subgoal *)
+ tactic.              (* Sub-subgoal *)
+ tactic.
* tactic.              (* Sub-sub-subgoal *)
```

**Braces:**
```coq
{ tactic. }            (* First subgoal *)
{ tactic. }            (* Second subgoal *)
```

### `clear` - Remove Hypothesis

```coq
clear H.               (* Remove H from context *)
clear H1 H2 H3.        (* Remove multiple *)
clear - H.             (* Keep only H *)
```

### `revert` - Move Hypothesis to Goal

```coq
revert x.              (* Opposite of intro *)
revert x y H.          (* Move multiple *)
```

**When to use:**
- Before induction (generalize)
- Cleaning context
- Strengthening induction hypothesis

### `generalize` - Generalize Term

```coq
generalize t.          (* Replace t with fresh variable *)
generalize dependent x. (* Generalize x and dependencies *)
```

### `rename` - Rename Hypothesis

```coq
rename H into H'.      (* Rename H to H' *)
```

### `assert` - Add Intermediate Lemma

```coq
assert (H : P).        (* Add P as hypothesis, must prove *)
{ proof of P }
(* Now have H : P *)
```

**When to use:**
- Forward reasoning
- Need intermediate fact
- Breaking complex proof

**SSReflect equivalent:** `have`

---

## SSReflect Tactics

SSReflect provides a consistent, composable tactical language. Key principles:
- Stack-based: `move`, `case`, `apply`, `elim`
- Explicit: `move=> x` vs implicit `intro x`
- Rewrite: `rewrite` is core, enhanced with selectors
- Views: `/` operator for view lemmas
- Bookkeeping: `{}` for clearing, `//` for closing

### `move` - Generic Stack Operation

**What it does:** Most general tactic, moves items intro/discharge.

```coq
move=> x.              (* intro x *)
move=> x y H.          (* intros x y H *)
move: H.               (* revert H *)
move: H => H'.         (* rename H to H' *)
```

**When to use:**
- Almost always instead of `intro/intros`
- SSReflect style
- More composable

### `case` - Case Analysis

**What it does:** Destruct with SSReflect style.

```coq
case: H.               (* destruct H *)
case: H => [x | y].    (* with pattern *)
case: n => [|n'].      (* nat case *)
case=> x y.            (* case and intro *)
```

**When to use:**
- SSReflect style case analysis
- More predictable than `destruct`
- Composable with other tactics

### `elim` - Induction

**What it does:** Induction with SSReflect style.

```coq
elim: n.               (* induction n *)
elim: n => [|n' IHn']. (* with pattern *)
elim/custom_ind: n.    (* custom induction *)
```

### `apply:` and `apply/` - Application

```coq
apply: lemma.          (* backward *)
apply/view.            (* with view *)
apply: lemma => //.    (* apply and try close *)
```

### `have` - Forward Reasoning

**What it does:** Like `assert` but SSReflect style.

```coq
have H : P.            (* assert P *)
{ proof }
(* Now have H : P *)

have H : P by tactic.  (* prove immediately *)
have := proof.         (* have without naming *)
```

**When to use:**
- Forward reasoning
- SSReflect style
- More flexible than `assert`

### `suff` - Suffices (Backward `have`)

**What it does:** Like `enough`.

```coq
suff H : P.            (* suffices to prove P *)
{ proof of goal using P }
proof of P.
```

### SSReflect Rewrite Enhancements

```coq
rewrite H.             (* standard *)
rewrite -H.            (* reverse *)
rewrite {}H.           (* rewrite and clear *)
rewrite /def.          (* unfold def *)
rewrite [X]H.          (* rewrite only X *)
rewrite !H.            (* rewrite repeatedly *)
rewrite ?H.            (* rewrite if applies *)
```

### Closing Tactics

```coq
by tactic.             (* tactic then close with trivial *)
done.                  (* close trivial goal *)
//.                    (* try to close *)
```

**Examples:**
```coq
by rewrite H.          (* rewrite H; done *)
case=> n; by case: n.  (* case on n, each case closes *)
```

### Combinators

```coq
tac1; tac2.            (* sequence *)
tac1 || tac2.          (* first one that works *)
tac1; last tac2.       (* tac1 then tac2 on last goal *)
tac1; first tac2.      (* tac1 then tac2 on first goal *)
```

---

## Advanced Tactics

### `remember` - Remember with Equation

**What it does:** Abbreviates term and remembers equation.

```coq
remember t as x eqn:Hx. (* Replace t with x, get Hx : x = t *)
```

**When to use:**
- Generalizing before induction
- Need to remember what term was
- Preventing reduction

### `pose` - Add Definition to Context

```coq
pose (x := t).         (* Add x := t to context *)
pose proof H as H'.    (* Copy hypothesis *)
```

**When to use:**
- Abbreviating complex terms
- Keeping definitions local
- Non-destructive hypothesis copying

### `set` - Replace with Variable

```coq
set (x := t).          (* Replace t with x everywhere *)
set (x := t) in H.     (* Only in H *)
```

**When to use:**
- Abbreviating repeated terms
- Cleaning goals
- Before pattern matching

### `dependent destruction` / `dependent induction`

**What it does:** Handles dependent types properly.

```coq
dependent destruction H.
dependent induction n.
```

**Requires:**
```coq
Require Import Program.
```

**When to use:**
- Dependent types
- Regular `destruct`/`induction` fails
- Vectors, dependent pairs

### `now` - Solve Immediately

**What it does:** Applies tactic and ensures it closes goal.

```coq
now auto.              (* auto must close *)
now lia.               (* lia must close *)
```

**When to use:**
- Assert tactic must succeed
- Debugging (fails if doesn't close)

### `try` - Try Tactic

**What it does:** Applies tactic, doesn't fail if it fails.

```coq
try tactic.            (* no-op if fails *)
all: try ring.         (* try ring on all goals *)
```

### `repeat` - Repeat Tactic

**What it does:** Repeats tactic until it fails.

```coq
repeat rewrite H.      (* rewrite as many times as possible *)
repeat constructor.    (* split all conjunctions *)
```

**When to use:**
- Saturating applications
- Be careful of infinite loops!

### `fix` / `cofix` - Manual Fixpoint/Cofixpoint

**What it does:** Manual recursion/corecursion.

```coq
fix IH n.              (* Start fixpoint with rec arg n *)
cofix.                 (* Start cofixpoint *)
```

**When to use:**
- Complex recursive proofs
- When `induction` isn't enough
- Expert-level tactic

---

## Tactical Combinators

### Standard Combinators

```coq
tac1; tac2.            (* Sequence *)
tac1 || tac2.          (* Disjunction (first success) *)
try tac.               (* Optional *)
repeat tac.            (* Iterate *)
tac; [tac1 | tac2].    (* Split branching *)
all: tac.              (* Apply to all goals *)
```

### Advanced Tactical Control

```coq
idtac.                 (* Do nothing *)
fail.                  (* Always fail *)
fail "message".        (* Fail with message *)
progress tac.          (* Fail if no progress *)
solve [tac].           (* Only if solves goal *)
```

---

## Proof Structuring

### Comments

```coq
(* This is a comment *)
```

### Sectioning

```coq
Section ExampleSection.
  Variable (x : nat).
  Hypothesis Hx : x > 0.

  Lemma example : x >= 1.
  Proof.
    lia.
  Qed.
End ExampleSection.
(* x and Hx become arguments to example *)
```

### Bullets and Braces

```coq
Proof.
  tactic.
  - (* First subgoal *)
    tactic.
    + (* Sub-subgoal *)
    + (* Another sub-subgoal *)
  - (* Second subgoal *)
    tactic.
    { tactic. }    (* Alternative: braces *)
    { tactic. }
Qed.
```

---

## Decision Trees for Tactic Selection

### "I need to introduce something"

```
What are you introducing?
├─ Universal/implication → intros / move=>
├─ Pattern match needed → intros [pat1 | pat2] / case=> [pat1 | pat2]
└─ One at a time → intro / move=>
```

### "I need to split cases"

```
What are you splitting?
├─ Inductive type → destruct / case:
├─ Boolean/decidable → destruct (classic P) / case: (boolP P)
├─ Or hypothesis → destruct H as [H1 | H2] / case: H => [H1 | H2]
├─ And hypothesis → destruct H as [H1 H2] / case: H => [H1 H2]
└─ If expression → destruct (if ...) / case: (if ...)
```

### "I need to prove exists x, P x"

```
Do you know the witness?
├─ Yes → exists t
├─ Will be computed → eexists
└─ SSReflect → exists t
```

### "I need to rewrite"

```
What kind of rewrite?
├─ Simple equality → rewrite H / rewrite -H
├─ Multiple times → rewrite !H (SSR) or repeat rewrite H
├─ In hypothesis → rewrite H in H'
├─ Custom equivalence → setoid_rewrite H
└─ With unfolding → rewrite /def (SSR) or unfold def; rewrite H
```

### "I want to automate"

```
How complex is the goal?
├─ Trivial → reflexivity / by []
├─ Simple → auto / easy
├─ Propositional logic → tauto / intuition
├─ Linear arithmetic → lia / lra
├─ Ring/field equation → ring / field
├─ Polynomial arithmetic → nia / nra
└─ Equality reasoning → congruence
```

---

## Common Patterns and Idioms

### Pattern: Inversion and cleanup

```coq
inversion H; subst; clear H.
```

### Pattern: Case analysis with equation

```coq
destruct x eqn:Hx.
(* SSReflect: case E: x => [|]. *)
```

### Pattern: Forward reasoning

```coq
assert (intermediate : P). { proof. }
(* SSReflect: have intermediate : P by proof. *)
```

### Pattern: Backward reasoning

```coq
enough (sufficient : P). { use P to prove goal. }
proof of P.
(* SSReflect: suff sufficient : P. { use P }. proof of P. *)
```

### Pattern: Generalize before induction

```coq
revert m.
induction n.
(* SSReflect: elim: n m. *)
```

### Pattern: Existential elimination

```coq
destruct H as [x Hx].
(* SSReflect: case: H => x Hx. *)
```

---

## See Also

- [rocq-phrasebook.md](rocq-phrasebook.md) - Natural language to Rocq translations
- [ssreflect-patterns.md](ssreflect-patterns.md) - Detailed SSReflect guide
- [compilation-errors.md](compilation-errors.md) - Debugging tactic failures
- [domain-patterns.md](domain-patterns.md) - Domain-specific tactics