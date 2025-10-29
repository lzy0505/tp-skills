# Domain-Specific Patterns for Rocq/Coq

This guide provides tactics, lemmas, and patterns specific to common proof domains: software foundations, algebra, analysis, logic, and type theory.

**Principle:** Each domain has its own idioms. Learn the patterns, don't reinvent the wheel.

---

## Table of Contents

1. [Software Foundations](#software-foundations)
2. [Algebra](#algebra)
3. [Analysis and Real Numbers](#analysis-and-real-numbers)
4. [Logic and Set Theory](#logic-and-set-theory)
5. [Type Theory and Dependent Types](#type-theory-and-dependent-types)
6. [Program Verification](#program-verification)
7. [MathComp Algebraic Hierarchy](#mathcomp-algebraic-hierarchy)

---

## Software Foundations

Patterns for inductive types, structural induction, programming language semantics.

### Pattern: Defining Inductive Types

```coq
(* Simple inductive *)
Inductive day : Type :=
| monday | tuesday | wednesday | thursday | friday | saturday | sunday.

(* Parameterized inductive *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

(* Indexed inductive *)
Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : forall n, A -> vector A n -> vector A (S n).
```

### Pattern: Structural Induction on Lists

```coq
Require Import Coq.Lists.List.
Import ListNotations.

Lemma app_nil_r : forall (A : Type) (l : list A),
  l ++ [] = l.
Proof.
  induction l as [| h t IHt].
  - (* l = [] *)
    reflexivity.
  - (* l = h :: t *)
    simpl. rewrite IHt. reflexivity.
Qed.
```

### Pattern: Strong Induction

```coq
Require Import Coq.Arith.Wf_nat.

Lemma strong_induction (P : nat -> Prop) :
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
  intros H n.
  apply (lt_wf_ind n).
  apply H.
Qed.
```

### Pattern: Mutual Induction

```coq
Inductive even : nat -> Prop :=
| even_0 : even 0
| even_SS : forall n, even n -> even (S (S n)).

Inductive odd : nat -> Prop :=
| odd_1 : odd 1
| odd_SS : forall n, odd n -> odd (S (S n)).

Scheme even_ind_mut := Induction for even Sort Prop
with odd_ind_mut := Induction for odd Sort Prop.
```

### Pattern: Inversion on Inductive Hypothesis

```coq
Lemma even_inv : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n H.
  inversion H.      (* Extracts even n from even (S (S n)) *)
  assumption.
Qed.
```

### Pattern: Custom Induction Principles

```coq
(* Induction on pairs of natural numbers *)
Lemma nat_pair_ind (P : nat -> nat -> Prop) :
  (forall m, P 0 m) ->
  (forall n, P (S n) 0) ->
  (forall n m, P n m -> P (S n) (S m)) ->
  forall n m, P n m.
Proof.
  intros H0 HS0 HSS.
  induction n as [| n IHn].
  - apply H0.
  - destruct m as [| m].
    + apply HS0.
    + apply HSS, IHn.
Qed.
```

---

## Algebra

Patterns for groups, rings, fields, and algebraic structures.

### Pattern: Ring Equations

```coq
Require Import Coq.setoid_ring.Ring.
Require Import ZArith.
Open Scope Z_scope.

Lemma ring_example : forall x y : Z,
  (x + y) * (x - y) = x * x - y * y.
Proof.
  intros. ring.
Qed.
```

### Pattern: Field Equations

```coq
Require Import Coq.Reals.Reals.
Require Import Coq.setoid_ring.Field.
Open Scope R_scope.

Lemma field_example : forall x y : R,
  x <> 0 -> y <> 0 ->
  (x + y) / (x * y) = 1/y + 1/x.
Proof.
  intros x y Hx Hy.
  field.
  split; assumption.
Qed.
```

### Pattern: Monoid Laws

```coq
Class Monoid (A : Type) (op : A -> A -> A) (e : A) := {
  assoc : forall x y z, op (op x y) z = op x (op y z);
  left_id : forall x, op e x = x;
  right_id : forall x, op x e = x
}.

(* Example: Nat addition is a monoid *)
#[export] Instance nat_add_monoid : Monoid nat Nat.add 0.
Proof.
  split.
  - apply Nat.add_assoc.
  - apply Nat.add_0_l.
  - apply Nat.add_0_r.
Qed.
```

### Pattern: Group Laws

```coq
Class Group (A : Type) (op : A -> A -> A) (e : A) (inv : A -> A) := {
  group_monoid :> Monoid A op e;
  left_inverse : forall x, op (inv x) x = e;
  right_inverse : forall x, op x (inv x) = e
}.
```

### Pattern: MathComp Algebraic Hierarchy

```coq
From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory.

(* Working with rings *)
Lemma ring_morph_example (R S : ringType) (f : {rmorphism R -> S}) x y :
  f (x + y) = f x + f y.
Proof.
  by rewrite rmorphD.  (* Ring morphism preserves addition *)
Qed.

(* Working with fields *)
Lemma field_example (F : fieldType) (x : F) :
  x != 0 -> x * x^-1 = 1.
Proof.
  by move=> Hx; rewrite mulVf.
Qed.
```

### Pattern: Module Laws

```coq
(* Vector space / module structure *)
Class Module (R : Type) (M : Type)
  (add : M -> M -> M) (zero : M) (scale : R -> M -> M) := {
  (* Module laws *)
  module_add_assoc : forall x y z, add (add x y) z = add x (add y z);
  module_add_comm : forall x y, add x y = add y x;
  module_add_zero : forall x, add zero x = x;
  scale_assoc : forall (r s : R) x, scale r (scale s x) = scale (r * s)%ring x;
  scale_one : forall x, scale 1%ring x = x;
  scale_add : forall r x y, scale r (add x y) = add (scale r x) (scale r y)
}.
```

---

## Analysis and Real Numbers

Patterns for limits, continuity, derivatives, integration.

### Pattern: Real Arithmetic

```coq
Require Import Coq.Reals.Reals.
Require Import Lra.
Open Scope R_scope.

Lemma real_arith : forall x y : R,
  x > 0 -> y > 0 -> x + y > 0.
Proof.
  intros. lra.  (* Linear Real Arithmetic *)
Qed.
```

### Pattern: Limits (Standard Library)

```coq
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Ranalysis1.

(* Limit definition *)
Definition limit_at (f : R -> R) (a l : R) :=
  forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
    forall x : R, x <> a -> Rabs (x - a) < delta -> Rabs (f x - l) < eps.
```

### Pattern: Coquelicot Real Analysis

```coq
Require Import Coquelicot.Coquelicot.

(* Limits in Coquelicot (cleaner) *)
Lemma continuous_add (f g : R -> R) (a : R) :
  continuous f a -> continuous g a ->
  continuous (fun x => f x + g x) a.
Proof.
  intros Hf Hg.
  apply continuous_plus; assumption.
Qed.

(* Derivatives *)
Lemma derivative_poly :
  forall x : R, is_derive (fun x => x ^ 2) x (2 * x).
Proof.
  intro x.
  auto_derive; ring.
Qed.
```

### Pattern: Series and Convergence

```coq
From Coquelicot Require Import Coquelicot.

Lemma geometric_series :
  forall r : R, Rabs r < 1 ->
  is_series (fun n => r ^ n) (1 / (1 - r)).
Proof.
  intros r Hr.
  apply is_series_geometric.
  assumption.
Qed.
```

### Pattern: MathComp Analysis

```coq
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.analysis Require Import reals.

(* Using MathComp's real interface *)
Lemma analysis_example (R : realType) (x y : R) :
  0 < x -> 0 < y -> 0 < x + y.
Proof.
  move=> Hx Hy.
  by apply: addr_gt0.
Qed.
```

---

## Logic and Set Theory

Patterns for classical logic, set operations, and relations.

### Pattern: Classical Reasoning

```coq
Require Import Classical.

Lemma excluded_middle_example (P : Prop) :
  P \/ ~P.
Proof.
  apply classic.
Qed.

Lemma double_negation (P : Prop) :
  ~~P -> P.
Proof.
  apply NNPP.
Qed.
```

### Pattern: Set Operations

```coq
Require Import Coq.Sets.Ensembles.

(* Set membership *)
Definition In {U : Type} (A : Ensemble U) (x : U) : Prop :=
  A x.

(* Subset *)
Lemma subset_example {U : Type} (A B : Ensemble U) :
  (forall x, In A x -> In B x) -> Included U A B.
Proof.
  intros H.
  unfold Included, In in *.
  assumption.
Qed.
```

### Pattern: Relations

```coq
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

(* Reflexive transitive closure *)
Lemma rtc_example {A : Type} (R : relation A) (x z : R) :
  clos_refl_trans A R x z ->
  exists y, clos_refl_trans A R x y /\ clos_refl_trans A R y z.
Proof.
  intros H.
  exists z.
  split.
  - exact H.
  - apply rt_refl.
Qed.
```

### Pattern: Equivalence Relations

```coq
Require Import Coq.Classes.RelationClasses.

(* Define equivalence relation *)
#[export] Instance nat_mod_equiv (n : nat) : Equivalence (fun x y => (x - y) mod n = 0).
Proof.
  split.
  - (* Reflexivity *) intro x. apply Nat.sub_diag.
  - (* Symmetry *) intros x y H. symmetry. (* prove *) admit.
  - (* Transitivity *) intros x y z Hxy Hyz. (* prove *) admit.
Admitted.
```

---

## Type Theory and Dependent Types

Patterns for dependent types, equality, and proof irrelevance.

### Pattern: Dependent Pattern Matching

```coq
Require Import Coq.Vectors.Vector.
Import VectorNotations.

Definition vector_hd {A : Type} {n : nat} (v : Vector.t A (S n)) : A :=
  match v with
  | h :: t => h
  end.
```

### Pattern: Equality Reasoning

```coq
(* Leibniz equality *)
Lemma eq_trans {A : Type} (x y z : A) :
  x = y -> y = z -> x = z.
Proof.
  intros H1 H2.
  rewrite H1, H2.
  reflexivity.
Qed.

(* Heterogeneous equality (JMeq) *)
Require Import Coq.Logic.JMeq.

Lemma jmeq_example {A : Type} (x : A) :
  JMeq x x.
Proof.
  apply JMeq_refl.
Qed.
```

### Pattern: Proof Irrelevance

```coq
Require Import Coq.Logic.ProofIrrelevance.

Lemma proof_irr_example (P : Prop) (p1 p2 : P) :
  p1 = p2.
Proof.
  apply proof_irrelevance.
Qed.
```

### Pattern: Sigma Types (Dependent Pairs)

```coq
Require Import Coq.Init.Specif.

Definition bounded_nat (n : nat) : Type :=
  {m : nat | m < n}.

Definition make_bounded (n m : nat) (H : m < n) : bounded_nat n :=
  exist _ m H.

Lemma bounded_example (n : nat) (x : bounded_nat n) :
  proj1_sig x < n.
Proof.
  destruct x as [m Hm].
  exact Hm.
Qed.
```

### Pattern: Program for Dependent Types

```coq
Require Import Coq.Program.Program.

Program Definition safe_div (n m : nat) (H : m <> 0) : nat :=
  n / m.
```

---

## Program Verification

Patterns for Hoare logic, program correctness, and verification conditions.

### Pattern: Hoare Triples

```coq
(* Simple imperative language *)
Inductive com : Type :=
| CSkip
| CAssign (x : string) (a : nat)
| CSeq (c1 c2 : com)
| CIf (b : bool) (c1 c2 : com)
| CWhile (b : bool) (c : com).

(* State *)
Definition state := string -> nat.

(* Hoare triple *)
Definition hoare_triple (P : state -> Prop) (c : com) (Q : state -> Prop) : Prop :=
  forall st st', P st -> eval_com st c st' -> Q st'.
```

### Pattern: Weakest Precondition

```coq
Fixpoint wp (c : com) (Q : state -> Prop) : state -> Prop :=
  match c with
  | CSkip => Q
  | CAssign x a => fun st => Q (update st x a)
  | CSeq c1 c2 => wp c1 (wp c2 Q)
  | CIf b c1 c2 => fun st =>
      (b st = true -> wp c1 Q st) /\
      (b st = false -> wp c2 Q st)
  | CWhile b c => (* Requires invariant *) admit
  end.
```

### Pattern: Loop Invariants

```coq
Lemma while_rule (b : bool -> Prop) (c : com) (I : state -> Prop) :
  (* I is preserved by loop body when b is true *)
  (forall st, I st -> b st = true -> exists st', eval_com st c st' /\ I st') ->
  (* When loop exits, b is false *)
  (forall st, I st -> b st = false -> post_condition st) ->
  (* Then the while loop is correct *)
  hoare_triple I (CWhile b c) post_condition.
Admitted.
```

---

## MathComp Algebraic Hierarchy

Specialized patterns for MathComp's canonical structure system.

### Pattern: EqType (Equality Types)

```coq
From mathcomp Require Import all_ssreflect.

(* Define custom equality type *)
Inductive mytype := A | B | C.

Definition mytype_eq (x y : mytype) : bool :=
  match x, y with
  | A, A | B, B | C, C => true
  | _, _ => false
  end.

Lemma mytype_eqP : Equality.axiom mytype_eq.
Proof.
  move=> x y; apply: (iffP idP).
  - by case: x; case: y.
  - by move=> ->; case: y.
Qed.

Canonical mytype_eqMixin := EqMixin mytype_eqP.
Canonical mytype_eqType := Eval hnf in EqType mytype mytype_eqMixin.
```

### Pattern: Choice Types

```coq
From mathcomp Require Import all_ssreflect.

(* Use choice to get canonical element *)
Lemma choice_example (P : nat -> Prop) :
  (exists n, P n) -> {n | P n}.
Proof.
  case=> n Pn.
  by exists n.
Qed.
```

### Pattern: FinType (Finite Types)

```coq
From mathcomp Require Import all_ssreflect fintype.

(* Working with finite types *)
Lemma card_example (T : finType) (A : pred T) :
  #|[set x in A]| <= #|T|.
Proof.
  by rewrite max_card.
Qed.
```

### Pattern: BigOp (Big Operators)

```coq
From mathcomp Require Import all_ssreflect all_algebra bigop.

(* Sum over range *)
Lemma sum_example n :
  \sum_(i < n) i = n * (n - 1) %/ 2.
Proof.
  (* Prove by induction on n *)
  admit.
Admitted.

(* Product *)
Lemma prod_example n :
  \prod_(i < n.+1) (i.+1) = n`!.
Proof.
  by rewrite big_mkord -prodn_nat_const.
Qed.
```

### Pattern: Matrices

```coq
From mathcomp Require Import all_ssreflect all_algebra matrix.

Lemma matrix_mul_example (R : ringType) m n p
  (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p)) :
  (A *m B)^T = B^T *m A^T.
Proof.
  apply/matrixP=> i j.
  rewrite !mxE.
  apply: eq_bigr=> k _.
  by rewrite !mxE mulrC.
Qed.
```

---

## Domain-Specific Tactic Summary

| Domain | Key Tactics | Key Libraries |
|--------|-------------|---------------|
| **Software Foundations** | `induction`, `inversion`, `simpl` | Coq.Lists, Coq.Arith |
| **Algebra** | `ring`, `field`, typeclass resolution | Coq.setoid_ring, MathComp.algebra |
| **Analysis** | `lra`, `nra`, `auto_derive` | Coq.Reals, Coquelicot, MathComp.analysis |
| **Logic** | `tauto`, `firstorder`, `intuition` | Coq.Logic, Classical |
| **Type Theory** | `dependent destruction`, Program | Coq.Program, Equations |
| **Verification** | Hoare logic, VCs | Custom frameworks |
| **MathComp** | SSReflect tactics, views | mathcomp.* |

---

## See Also

- [tactics-reference.md](tactics-reference.md) - Complete tactics guide
- [ssreflect-patterns.md](ssreflect-patterns.md) - SSReflect details
- [stdlib-guide.md](stdlib-guide.md) - Finding domain lemmas
- [rocq-phrasebook.md](rocq-phrasebook.md) - Proof patterns

---

**Further Reading:**
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) - Inductive types, program verification
- [Mathematical Components Book](https://math-comp.github.io/mcb/) - Algebra in MathComp
- [Coquelicot Documentation](http://coquelicot.saclay.inria.fr/html/Coquelicot.Coquelicot.html) - Real analysis
- [CPDT](http://adam.chlipala.net/cpdt/) - Advanced type theory patterns
