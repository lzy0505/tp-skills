# Rocq Phrasebook: Mathematical English to Rocq/Coq

This guide translates common mathematical proof phrases into their Rocq/Coq equivalents, helping you think in natural mathematical language while writing formal proofs.

**Inspiration:** This phrasebook is inspired by [Terence Tao's Lean Phrasebook](https://docs.google.com/spreadsheets/d/1Gsn5al4hlpNc_xKoXdU6XGmMyLiX4q-LFesFVsMlANo/edit?pli=1&gid=0#gid=0) and adapted for Rocq/Coq, reorganized by proof pattern with additional context and explanations.

**Note:** This guide covers both standard Coq tactics and SSReflect/MathComp tactics (marked with "SSR:"). Choose based on your project's style.

---

## Quick Reference by Situation

### You want to...

- **Introduce assumptions**: `intros`, `move` (SSR), `case` (SSR)
- **Use hypothesis**: `exact`, `apply`, `rewrite`, `simpl in H`
- **Split goal**: `split`, `constructor`, `left`/`right`
- **Split hypothesis**: `destruct`, `inversion`, `case` (SSR)
- **Add intermediate fact**: `assert`, `have` (SSR), `pose proof`
- **Change perspective**: `enough`, `suff` (SSR), `change`
- **Prove by contradiction**: `exfalso`, classical reasoning
- **Chain equalities**: `transitivity`, `rewrite` chains
- **Simplify**: `simpl`, `auto`, `easy`, `lia`, `ring`
- **Explore options**: `Search`, `SearchPattern`, `SearchAbout`
- **Manage goals**: `2: {...}`, `all: {...}`, `swap`

**See also:** [tactics-reference.md](tactics-reference.md) for comprehensive tactic documentation.

---

## Table of Contents

- [Forward Reasoning](#forward-reasoning)
- [Backward Reasoning](#backward-reasoning)
- [Case Analysis](#case-analysis)
- [Rewriting and Simplification](#rewriting-and-simplification)
- [Equational Reasoning](#equational-reasoning)
- [Working with Quantifiers](#working-with-quantifiers)
- [Working with Connectives](#working-with-connectives)
- [Contradiction and Contrapositive](#contradiction-and-contrapositive)
- [Inequalities and Ordering](#inequalities-and-ordering)
- [Set Theory](#set-theory)
- [Extensionality](#extensionality)
- [Algebraic Reasoning](#algebraic-reasoning)
- [Goal Management](#goal-management)
- [Advanced Patterns](#advanced-patterns)

---

## Forward Reasoning

Building up facts from what you know.

### Stating Intermediate Claims

**"Observe that A holds because of reason r"**
```coq
assert (H : A) by r.
(* SSR: have H : A by r. *)
```
- Can combine with proof: `assert (H : A). { proof. }`

**"We claim that A holds. [proof]"**
```coq
assert (H : A).
{ <proof of A> }
(* SSR: have H : A. { proof. } *)
```

**"Observe that X equals Y by definition"**
```coq
assert (X = Y) by reflexivity.
(* Or simply use: reflexivity *)
```

**"From hypothesis H, applying f gives us B"**
```coq
pose proof (f H) as HB.
(* SSR: have HB := f H. *)
```

### Using Hypotheses

**"The claim follows from hypothesis H"**
```coq
assumption.
(* or: exact H *)
```

**"This follows by definition"**
```coq
reflexivity.
(* SSR: by []. *)
```

**"This follows from reason r"**
```coq
exact r.
(* Explore: Search (pattern). *)
```

### Replacing Hypotheses

**"By f, we replace hypothesis A with B"**
```coq
pose proof (f H) as H.
(* Or: generalize (f H); clear H; intro H. *)
(* SSR: move: (f H) => H. *)
```

**"We strengthen hypothesis H to a stronger claim"**
```coq
assert (stronger : B). { proof. }
clear H.
(* SSR: have stronger : B by proof; clear H. *)
```

### Discarding Hypotheses

**"Hypothesis H is no longer needed"**
```coq
clear H.
```

**"We only need hypotheses A and B going forward"**
```coq
clear - A B.
(* Keeps only A and B, clears everything else *)
```

---

## Backward Reasoning

Working from the goal backwards.

### Reducing the Goal

**"By A, it suffices to show..."**
```coq
apply A.
```

**"It suffices to show B [proof of B], then we get our goal [proof using B]"**
```coq
enough (H : B).
{ <proof of goal using H> }
<proof of B>
(* SSR: suff H : B. { proof of goal. } proof of B. *)
```

**"Suppose P holds [arguments]. In summary, P implies Q."**
```coq
assert (HPQ : P -> Q).
{ intro HP.
  <arguments reaching conclusion>
  exact HQ. }
```

**"Later we'll prove A. Assuming it for now..."**
```coq
enough (H : A).
{ <proof assuming H> }
<proof of A>
```

**"We conjecture that A holds"**
```coq
Lemma A_conj : A.
Proof. admit. Admitted.
(* Inside proofs: assert (H : A). { admit. } *)
```

### Converting Goals

**"We reduce to showing B [proof it suffices], now show B [proof of B]"**
```coq
enough B.
{ <proof original goal given B> }
<proof of B>
```

**"By definition, the goal rewrites as A'"**
```coq
change A'.
(* Also works for hypotheses: change A' in H *)
```

**"We unfold definition to see the real goal"**
```coq
unfold definition_name.
```

---

## Case Analysis

Breaking proofs into separate cases.

### Disjunction (Or)

**"Hypothesis H says A or B. We split into cases."**
```coq
destruct H as [HA | HB].
- <proof using HA>
- <proof using HB>
(* SSR: case: H => [HA | HB]; [proof1 | proof2]. *)
```

**"It suffices to prove A [to get A ∨ B]"**
```coq
left.
(* SSR: by left. *)
```

**"It suffices to prove B [to get A ∨ B]"**
```coq
right.
(* SSR: by right. *)
```

### Boolean Dichotomy

**"We split into cases depending on whether A holds."**
```coq
destruct (classic A) as [HA | HnA].
- <proof assuming HA : A>
- <proof assuming HnA : ~A>
(* Requires: Require Import Classical. *)
(* SSR: case: (boolP A) => [HA | HnA]. *)
```

**"We perform case analysis on boolean b"**
```coq
destruct b.
- <proof for b = true>
- <proof for b = false>
(* SSR: case: b => [|]; [proof_true | proof_false]. *)
```

### Inductive Types

**"We split cases on natural number n: base case n=0, step case n=m+1."**
```coq
destruct n as [| m].
- <proof for n = 0>
- <proof for n = S m, with m available>
(* SSR: case: n => [| m]; [base | step]. *)
```

**"We perform induction on n."**
```coq
induction n as [| n IHn].
- <proof of base case>
- <proof of inductive step, with IHn : P n available>
(* SSR: elim: n => [| n IHn]; [base | step]. *)
```

### Pattern Matching

**"We divide into cases n=0, n=1, and n≥2."**
```coq
destruct n as [| [| n]].
- <proof for 0>
- <proof for 1>
- <proof for S (S n) ≥ 2>
```

**"We perform case analysis with deep patterns"**
```coq
destruct H as [x [y [Hx Hy]]].
(* Equivalent to nested destructs *)
```

---

## Rewriting and Simplification

Transforming expressions using equalities.

### Basic Rewriting

**"We rewrite the goal using hypothesis H"**
```coq
rewrite H.
(* Reverse direction: rewrite <- H *)
(* Multiple rewrites: rewrite H1, H2, H3 *)
(* SSR: rewrite H. or rewrite -H (reverse) *)
```

**"We rewrite and close if it produces the goal"**
```coq
rewrite H; reflexivity.
(* SSR: by rewrite H. *)
```

**"We replace X by Y, using proof r that they're equal"**
```coq
rewrite (r : X = Y).
```

**"Applying f to both sides of H : X = Y"**
```coq
apply f_equal with (f := f) in H.
(* produces H : f X = f Y *)
(* SSR: move: (f_equal f H) => H. *)
```

**"Rewrite at position n only"**
```coq
rewrite H at n.
(* Rewrite only the n-th occurrence *)
```

**"Rewrite in hypothesis H"**
```coq
rewrite H' in H.
(* SSR: rewrite H' in H. *)
```

### Simplification

**"We simplify the goal"**
```coq
simpl.
(* Unfolds fixpoint definitions *)
(* SSR: simpl. or /= *)
```

**"We simplify using hypothesis H"**
```coq
simpl in H.
(* For simplifying with rewrite rules, use tactics like auto *)
```

**"We simplify hypothesis and goal"**
```coq
simpl in *.
```

**"We compute the result"**
```coq
compute.
(* Or for faster computation: vm_compute *)
```

**"Expanding all definitions"**
```coq
unfold definition_name.
(* Unfold specific definition *)
(* unfold definition_name in H. for hypothesis *)
```

**"We use automation to close simple goals"**
```coq
auto.
(* Or: easy. for slightly more powerful automation *)
(* Or: trivial. for very simple goals *)
```

### Field Operations

**"In a field, we simplify by clearing denominators"**
```coq
field.
(* Automatically handles field equations *)
(* Requires: Require Import Field. *)
(* Often followed by ring *)
```

**"We simplify field expressions step by step"**
```coq
field_simplify.
(* More controlled than field *)
```

---

## Equational Reasoning

Chains of equalities and inequalities.

### Calculation Chains

**"We compute: x = y (by r₁), = z (by r₂), = w (by r₃)"**
```coq
transitivity y. { apply r1. }
transitivity z. { apply r2. }
apply r3.
(* Or use rewrite chains: rewrite r1, r2, r3. *)
```

**"We chain rewrites for equality"**
```coq
rewrite H1.
rewrite H2.
rewrite H3.
reflexivity.
(* Or: rewrite H1, H2, H3; reflexivity. *)
```

**"We use setoid rewriting for custom equivalences"**
```coq
setoid_rewrite H.
(* Requires proper Setoid instances *)
```

---

## Working with Quantifiers

Universal and existential quantification.

### Universal Introduction

**"Assume A implies B. Thus suppose A holds."**
```coq
intro HA.
(* SSR: move=> HA. *)
```

**"Let x be an element of X."**
```coq
intros x Hx.
(* for goal: forall x, x ∈ X -> P x *)
(* SSR: move=> x Hx. *)
```

**"Let x be arbitrary"**
```coq
intro x.
(* SSR: move=> x. *)
```

### Universal Elimination

**"Since a ∈ X and ∀ x ∈ X, P(x) holds, we have P(a)"**
```coq
pose proof (H a Ha) as HPa.
(* Can use H a Ha directly anywhere instead of naming it *)
(* SSR: have HPa := H a Ha. *)
```

**"We specialize universal hypothesis to specific value"**
```coq
specialize (H a Ha).
(* This replaces H with H specialized to a *)
```

### Existential Introduction

**"We take x to equal a [to prove ∃ x, P x]"**
```coq
exists a.
(* SSR: exists a. *)
```

**"We construct witness and proof together"**
```coq
exists a; split.
- <proof of condition 1>
- <proof of condition 2>
```

### Existential Elimination

**"By hypothesis, there exists x satisfying A(x)"**
```coq
destruct H as [x HAx].
(* SSR: case: H => [x HAx]. *)
```

**"From hypothesis with multiple existentials"**
```coq
destruct H as [x [y [Hx Hy]]].
(* Nested pattern matching *)
```

**"Using dependent destruction for complex patterns"**
```coq
dependent destruction H.
(* For dependent types *)
```

---

## Working with Connectives

Conjunction, disjunction, and equivalence.

### Conjunction (And)

**"To prove A ∧ B, we prove each in turn."**
```coq
split.
- <proof of A>
- <proof of B>
(* Or: constructor. for any inductive type *)
(* SSR: split; [proof_A | proof_B]. *)
```

**"By hypothesis H : A ∧ B, we have both A and B"**
```coq
destruct H as [HA HB].
(* SSR: case: H => [HA HB]. *)
```
- Can also use projections: `proj1 H` and `proj2 H`
- Multiple conjuncts: `destruct H as [HA [HB [HC HD]]]`

**"To prove multiple conjuncts at once"**
```coq
repeat split.
- <proof 1>
- <proof 2>
- <proof 3>
```

### Equivalence (Iff)

**"To prove A ↔ B, we prove both directions."**
```coq
split.
- <proof of A -> B>
- <proof of B -> A>
(* SSR: split; [direction1 | direction2]. *)
```

**"We use forward direction of iff"**
```coq
apply H.
(* If H : A <-> B and goal is B, this changes goal to A *)
```

**"We use backward direction of iff"**
```coq
apply H.
(* Works bidirectionally - Coq figures it out *)
```

---

## Contradiction and Contrapositive

Proof by contradiction and contrapositive.

### Contradiction

**"We seek a contradiction"**
```coq
exfalso.
(* Changes goal to False *)
```

**"But this is absurd [given H : A and nH : ¬A]"**
```coq
exfalso. apply nH. exact H.
(* Or: contradiction. if Coq can find it *)
```

**"Given A and ¬A, this gives the required contradiction"**
```coq
contradiction.
(* Automatically finds contradicting hypotheses *)
```

**"Suppose for contradiction that A fails [to prove A]"**
```coq
destruct (classic A) as [HA | HnA].
- exact HA.
- exfalso.
  <derive contradiction from HnA>
(* Requires: Require Import Classical. *)
```

**"Suppose for contradiction that A holds [to prove ¬A]"**
```coq
intro HA.
<derive False from HA>
```

**"Classical reasoning: prove P by showing ~P leads to contradiction"**
```coq
apply NNPP. intro HnP.
<derive False from HnP>
(* Requires: Require Import Classical. *)
```

### Contrapositive

**"Taking contrapositives, to prove A -> B, show ~B -> ~A"**
```coq
intros HnB HA.
apply HnB.
<prove B from HA>
(* Or use lemma: apply contrapositive *)
```

---

## Inequalities and Ordering

Working with partial orders and inequalities.

### Basic Transitions

**"Given H : X ≤ Z, to prove X ≤ Y it suffices to show Z ≤ Y"**
```coq
apply (le_trans _ _ _ H).
(* Or: eapply le_trans. apply H. *)
```

**"Given H : X ≤ Z, to prove X < Y it suffices to show Z < Y"**
```coq
apply (le_lt_trans _ _ _ H).
```

**"Given H : Z ≤ Y, to prove X ≤ Y it suffices to show X ≤ Z"**
```coq
apply (le_trans _ _ _ _ H).
```

### Rewrites with Inequalities

**"Given H : X = Z, to prove X ≤ Y suffices to show Z ≤ Y"**
```coq
rewrite H.
```

**"Given H : Z = Y, to prove X ≤ Y suffices to show X ≤ Z"**
```coq
rewrite <- H.
```

### Antisymmetry

**"To prove x = y, show x ≤ y and y ≤ x"**
```coq
apply le_antisym.
(* Or: apply Nat.le_antisymm for natural numbers *)
```

### Algebraic Manipulations

**"To prove X ≤ Y, suffices to show X + Z ≤ Y + Z"**
```coq
apply plus_le_compat_r.
(* Many variants: plus_le_compat_l, etc. *)
```

**"To prove X ≤ Y, suffices to show X·Z ≤ Y·Z (with Z > 0)"**
```coq
apply mult_le_compat_r.
```

### Omega and Linear Arithmetic

**"This inequality follows from linear arithmetic"**
```coq
lia.
(* Linear Integer Arithmetic solver *)
(* Requires: Require Import Lia. *)
```

**"This real inequality follows from linear arithmetic"**
```coq
lra.
(* Linear Real Arithmetic solver *)
(* Requires: Require Import Lra. *)
```

**"This nonlinear arithmetic goal is provable"**
```coq
nia.
(* Nonlinear Integer Arithmetic *)
(* Requires: Require Import Nia. *)
```

---

## Set Theory

Working with sets, subsets, and set operations.

### Subset Proofs

**"To prove X ⊆ Y: let x ∈ X, show x ∈ Y"**
```coq
intros x Hx.
(* SSR: move=> x Hx. *)
```

**"To prove X = Y: show X ⊆ Y and Y ⊆ X"**
```coq
apply subset_antisym.
(* Or extensionality: apply set_ext; intro x; split *)
```

### Set Operations

**"x ∈ X ∪ Y means x ∈ X or x ∈ Y"**
```coq
(* Intro: left. (or right.) *)
(* Elim: destruct H as [HX | HY] *)
```

**"x ∈ X ∩ Y means x ∈ X and x ∈ Y"**
```coq
(* Intro: split *)
(* Elim: destruct H as [HX HY] *)
```

**"Set membership via set-builder notation"**
```coq
unfold In.
(* Then prove the property *)
```

---

## Extensionality

Proving equality by extensionality.

### Function Extensionality

**"To prove f = g, show f(x) = g(x) for all x"**
```coq
apply functional_extensionality.
intro x.
(* Now prove: f x = g x *)
(* Requires: Require Import FunctionalExtensionality. *)
```

**"Short form for function extensionality"**
```coq
extensionality x.
(* Introduces x and changes goal to f x = g x *)
```

### Propositional Extensionality

**"To prove P = Q (as Props), show P ↔ Q"**
```coq
apply propositional_extensionality.
split.
(* Requires: Require Import PropExtensionality. *)
```

### Set Extensionality

**"To prove S = T, show x ∈ S ↔ x ∈ T for all x"**
```coq
apply set_ext.
intro x.
split.
```

### Congruence

**"Given f(x) = f(y), to prove goal it suffices to show x = y"**
```coq
f_equal.
(* Applies congruence - generates equality subgoals *)
```

**"Automatic congruence for complex goals"**
```coq
congruence.
(* Powerful decision procedure for equality reasoning *)
```

---

## Algebraic Reasoning

Automatic tactics for algebra.

### Ring Theory

**"This follows from ring axioms"**
```coq
ring.
(* Requires: Require Import Ring. *)
(* Or for semirings: ring_simplify *)
```

**"Simplify ring expressions"**
```coq
ring_simplify.
(* Normalizes but doesn't close goal *)
```

### Field Theory

**"This follows from field axioms"**
```coq
field.
(* Requires: Require Import Field. *)
```

### Logical Tautologies

**"This follows by logical tautology"**
```coq
tauto.
(* Propositional tautology solver *)
```

**"This is intuitionistically valid"**
```coq
intuition.
(* Less powerful than tauto but works without classical logic *)
```

### Numerical Verification

**"Which can be verified numerically"**
```coq
compute.
(* Or: vm_compute for faster evaluation *)
(* Or: native_compute for native code compilation *)
```

---

## Goal Management

Managing multiple goals and proof structure.

### Goal Manipulation

**"We prove the second goal first"**
```coq
2: { <proof of second goal> }
<proof of first goal>
```

**"We prove goal number n"**
```coq
n: { <proof> }
```

**"We establish all these goals by the same argument"**
```coq
all: <tactics>.
(* Or with braces: all: { tactics }. *)
```

**"We try this tactic on all goals (may fail on some)"**
```coq
all: try tactic.
```

**"Focus on first goal"**
```coq
1: { <proof> }
```

### Shelving and Admitting

**"We defer this goal for later"**
```coq
shelve.
(* Returns to shelved goals with: Unshelve. *)
```

**"We admit this subgoal temporarily"**
```coq
admit.
(* Leaves proof incomplete *)
```

### Negation Manipulation

**"Pushing negation through quantifiers"**
```coq
(* Manual in Coq - no built-in push_neg *)
(* Apply de Morgan's laws manually or use custom tactics *)
```

### Symmetry

**"To prove X = Y, we rewrite as Y = X"**
```coq
symmetry.
(* Also works for other symmetric relations *)
(* SSR: apply/esym or rewrite eq_sym *)
```

---

## Advanced Patterns

More sophisticated proof techniques.

### Without Loss of Generality

**"Without loss of generality, assume P"**
```coq
(* Coq doesn't have built-in wlog *)
(* Pattern: prove lemma, then use symmetry argument *)
assert (wlog : <symmetric property>).
{ <proof of symmetry> }
destruct (classic P) as [HP | HnP].
- <proof assuming P>
- <apply symmetry via wlog>
```

### Abbreviations and Definitions

**"Let X denote the quantity Y"**
```coq
pose (X := Y).
(* Does not substitute in goal *)
```

**"We abbreviate expression Y as X"**
```coq
set (X := Y).
(* Replaces Y with X in goal *)
(* To track equality: set (X := Y) in *; remember Y as X *)
```

**"We introduce equation for substitution"**
```coq
remember Y as X eqn:HX.
(* Creates HX : X = Y and replaces Y with X *)
```

**"Make X an independent variable"**
```coq
generalize Y as X.
intro X.
```

### Automation Tactics

**"Search for lemmas matching this pattern"**
```coq
Search (pattern).
(* Example: Search (_ + _ = _ + _) *)
```

**"Search for lemmas about this constant"**
```coq
SearchAbout identifier.
(* Lists all lemmas mentioning identifier *)
```

**"Search by pattern matching"**
```coq
SearchPattern (_ <= _).
(* Finds lemmas with conclusion matching pattern *)
```

**"Try to solve goal automatically"**
```coq
auto.
(* Or: eauto for existential variables *)
(* Or: easy for more powerful automation *)
```

**"First-order automatic theorem proving"**
```coq
firstorder.
(* Solves many goals in first-order logic *)
```

### Inversion

**"We invert this hypothesis to extract information"**
```coq
inversion H.
(* Performs case analysis and injects equalities *)
(* Cleans up: inversion H; subst; clear H *)
```

**"We invert and substitute in one step"**
```coq
inversion H; subst.
```

### Conditional Expressions

**"For goal involving (if A then x else y), split cases"**
```coq
destruct A.
- <proof if A is true>
- <proof if A is false>
```

---

## SSReflect Patterns

Specialized patterns for SSReflect/MathComp style.

### Basic SSReflect Flow

**"Introduce and immediately use"**
```coq
move=> H; apply: H.
```

**"Rewrite and close"**
```coq
by rewrite H.
```

**"Case analysis with SSReflect"**
```coq
case: x => [case1 | case2].
```

**"Apply lemma in forward direction"**
```coq
apply/lemma.
(* Uses view mechanism *)
```

**"Move hypothesis to goal"**
```coq
move: H.
(* Generalizes H back into goal *)
```

### SSReflect Views

**"Apply view to hypothesis"**
```coq
move/view: H.
(* Transforms H using view lemma *)
```

**"Apply view to goal"**
```coq
apply/view.
```

### SSReflect Bookkeeping

**"Clear as we go"**
```coq
move=> {H} x.
(* Introduces x and clears H *)
```

**"Rewrite and clear"**
```coq
rewrite {}H.
(* Rewrites with H then clears it *)
```

---

## See Also

- [tactics-reference.md](tactics-reference.md) - Comprehensive tactic documentation
- [domain-patterns.md](domain-patterns.md) - Domain-specific proof patterns
- [ssreflect-patterns.md](ssreflect-patterns.md) - Detailed SSReflect guide
- [stdlib-guide.md](stdlib-guide.md) - Finding and using standard library lemmas

---

**Attribution:** This phrasebook is inspired by [Terence Tao's Lean Phrasebook](https://docs.google.com/spreadsheets/d/1Gsn5al4hlpNc_xKoXdU6XGmMyLiX4q-LFesFVsMlANo/edit?pli=1&gid=0#gid=0) and adapted for Rocq/Coq with both standard tactics and SSReflect variants.
