# Domain-Specific Patterns for Rocq/Coq

This guide provides tactics, lemmas, and patterns specific to common proof domains: software foundations, algebra, analysis, logic, and type theory.

**Principle:** Each domain has its own idioms. Learn the patterns, don't reinvent the wheel.

---

## Table of Contents

1. [Logic and Set Theory](#logic-and-set-theory)
2. [Type Theory and Dependent Types](#type-theory-and-dependent-types)

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

## Domain-Specific Tactic Summary

| Domain | Key Tactics | Key Libraries |
|--------|-------------|---------------|
| **Logic** | `tauto`, `firstorder`, `intuition` | Coq.Logic, Classical |
| **Type Theory** | `dependent destruction`, Program | Coq.Program, Equations |

---

## See Also

- [tactics-reference.md](tactics-reference.md) - Complete tactics guide
- [ssreflect-patterns.md](ssreflect-patterns.md) - SSReflect details
- [stdlib-guide.md](stdlib-guide.md) - Finding domain lemmas
- [rocq-phrasebook.md](rocq-phrasebook.md) - Proof patterns
