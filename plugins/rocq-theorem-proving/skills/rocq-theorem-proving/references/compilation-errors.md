# Common Compilation Errors in Rocq/Coq

This reference provides detailed explanations and fixes for the most common compilation errors encountered in Rocq/Coq theorem proving.

## Quick Reference Table

| Error | Cause | Fix |
|-------|-------|-----|
| **"Cannot infer..."** / **"Cannot find instance"** | Missing typeclass instance | Add `Existing Instance` or provide instance explicitly |
| **"Universe inconsistency"** | Type/Prop/Set level mismatch | Check universe levels, use `Set Universe Polymorphism` |
| **"The term ... has type ... which should be Set, Prop or Type"** | Universe level error | Fix type annotations, ensure proper sort |
| **"Not found: ..."** | Missing import or definition | Add `Require Import` or check spelling |
| **"Tactic failure"** | Tactic doesn't apply | Check goal state with `Show.`, try different tactic |
| **"Unable to unify ... with ..."** | Unification failure | Use more specific types, add type annotations |
| **"Recursive call on non-decreasing argument"** | Fixpoint termination issue | Fix structural recursion or use well-founded recursion |
| **"Non strictly positive occurrence"** | Inductive definition violated positivity | Restructure inductive type |
| **"The reference ... was not found"** | Module/section/definition not in scope | Check imports, open modules, fix paths |

## Detailed Error Explanations

### 1. Cannot Infer / Cannot Find Instance

**Full error message:**
```
Cannot infer this placeholder of type "Inhabited A".
```
or
```
Cannot find a declared instance of "DecidableEq nat".
```

**What it means:** Coq cannot automatically infer the required typeclass instance.

**Common scenarios:**
- Working with decidable equality: need `DecidableEq` instance
- Container operations: need `Inhabited` instance
- SSReflect: missing `eqType`, `choiceType` instances
- MathComp algebraic hierarchy

**Solutions:**

**Pattern 1: Provide instance explicitly**
```coq
Require Import Classical.

(* For classical reasoning *)
Existing Instance classical_choice.

(* For decidable equality *)
Program Instance nat_eq_dec : DecidableEq nat := eq_nat_dec.
```

**Pattern 2: Import standard instances**
```coq
Require Import Coq.Classes.DecidableClass.
Require Import Coq.Classes.EquivDec.

(* Now many instances available *)
```

**Pattern 3: SSReflect/MathComp canonical structures**
```coq
Require Import mathcomp.ssreflect.eqtype.

(* Structures often automatic via canonicals *)
Check nat : eqType.  (* Should work with mathcomp *)
```

**Pattern 4: Local instance declaration**
```coq
Context `{Inhabited A}.  (* Section variable *)
(* Or inside proof: *)
Variable (HA : Inhabited A).
```

**Debug with:**
```coq
Print Instances ClassName.  (* See all instances of a class *)
About identifier.            (* See type and implicit args *)
```

### 2. Universe Inconsistency

**Full error message:**
```
Universe inconsistency (cannot enforce Set <= Prop).
```
or
```
Universe inconsistency. Cannot enforce Type@{i} = Type@{j}.
```

**What it means:** Universe level constraints are violated.

**Background:**
- Coq has universe hierarchy: `Prop` < `Set` < `Type(1)` < `Type(2)` < ...
- `Prop`: logical propositions (proof-irrelevant)
- `Set`/`Type(0)`: data types
- `Type(i)`: higher universes

**Common causes:**
- Mixing `Prop` and `Type` incorrectly
- Impredicativity violations
- Circular universe dependencies

**Solutions:**

**Solution 1: Check if using right sort**
```coq
(* ❌ BAD: Trying to extract data from Prop *)
Definition bad (P : Prop) : Type := P.
(* Error: Universe inconsistency *)

(* ✅ GOOD: Keep Prop in Prop *)
Definition good (P : Prop) : Prop := P.
```

**Solution 2: Use universe polymorphism**
```coq
Set Universe Polymorphism.

Definition polymorphic@{u} (A : Type@{u}) : Type@{u} := A.
```

**Solution 3: Monomorphic when needed**
```coq
Monomorphic Definition concrete : Type := nat.
```

**Solution 4: Check universe levels**
```coq
Print Universes.  (* See universe constraints *)
Set Printing Universes.  (* Show universes explicitly *)
```

**Pattern: Correct universe usage**
```coq
(* Propositions in Prop *)
Definition is_even (n : nat) : Prop := exists m, n = 2 * m.

(* Data types in Type/Set *)
Inductive tree : Type :=
| Leaf : nat -> tree
| Node : tree -> tree -> tree.

(* Functions from Type to Type *)
Definition maybe (A : Type) : Type := option A.
```

### 3. Type Mismatch

**Full error message:**
```
The term "x" has type "nat" while it is expected to have type "Z".
```

**What it means:** Term has wrong type for context.

**Common scenarios:**
- Natural numbers vs integers vs reals
- Lists of different element types
- Function argument mismatch

**Solutions:**

**Pattern 1: Explicit injection/coercion**
```coq
Require Import ZArith.
Open Scope Z_scope.

(* Natural to integer *)
Definition n : nat := 5.
Definition z : Z := Z.of_nat n.

(* Integer to natural (partial) *)
Definition z2 : Z := 5.
Definition n2 : nat := Z.to_nat z2.
```

**Pattern 2: Use coercions**
```coq
Require Import Coq.Reals.Reals.
Open Scope R_scope.

(* Set up coercion nat -> R *)
Coercion INR : nat >-> R.

Definition example (n : nat) : R := n + 1.5.  (* n coerced *)
```

**Pattern 3: Check actual types**
```coq
Check x.           (* See type of x *)
Search (_ -> _).   (* Find conversion functions *)
```

**Pattern 4: Rewrite with equality**
```coq
(* If you have H : x = y and need y but have x *)
rewrite H.         (* Changes x to y in goal *)
rewrite <- H.      (* Changes y to x in goal *)
```

### 4. Tactic Failure

**Full error message:**
```
Tactic failure: No applicable tactic.
```
or
```
Unable to apply.
```

**What it means:** The tactic doesn't apply to current goal.

**Common scenarios:**
- `reflexivity` on non-reflexive goal
- `apply` with type mismatch
- `induction` on non-inductive type
- `destruct` on opaque definition

**Solutions:**

**Solution 1: Inspect goal state**
```coq
Show.              (* See current goal *)
Show Proof.        (* See proof term so far *)
Show Existentials. (* See unresolved evars *)
```

**Solution 2: Try related tactics**
```coq
(* If reflexivity fails *)
simpl.             (* Simplify first *)
reflexivity.

(* If apply fails *)
eapply.            (* Allow unification variables *)

(* If destruct fails *)
unfold definition. (* Unfold first *)
destruct.
```

**Solution 3: Check hypothesis type**
```coq
Check H.           (* What type does H have? *)
(* If H : P -> Q but goal is Q *)
apply H.           (* Creates subgoal P *)
```

**Pattern: Debugging tactic failures**
```coq
Proof.
  intros.
  (* Tactic fails here *)
  Show.            (* What is the goal? *)
  Check hypothesis. (* What type is hypothesis? *)
  SearchAbout goal_pattern. (* Find relevant lemmas *)
  (* Now try tactic again with better understanding *)
```

### 5. Unable to Unify

**Full error message:**
```
Unable to unify "f x" with "f y".
```
or
```
Cannot unify ... with ...
```

**What it means:** Coq cannot make two terms equal through unification.

**Common causes:**
- Opaque definitions prevent unification
- Different constructors
- Rigid unification failures

**Solutions:**

**Solution 1: Make definitions transparent**
```coq
(* If definition is opaque *)
Transparent definition_name.

(* Or define as transparent *)
Definition f x := body.  (* Transparent by default *)
```

**Solution 2: Add explicit equality**
```coq
(* Instead of relying on unification *)
assert (H : f x = f y). { proof. }
rewrite H.
```

**Solution 3: Use conversion tactics**
```coq
change (f y).      (* Change goal to convertible term *)
```

**Solution 4: Check if truly equal**
```coq
(* Try to prove equality *)
assert (x = y). { proof. }
subst.             (* Substitute if variable *)
```

### 6. Recursive Definition Errors

**Full error message:**
```
Recursive definition is: "Recursive call on non-decreasing argument".
```

**What it means:** Fixpoint doesn't decrease on specified argument.

**Background:**
- Coq requires structural recursion for termination
- Recursive calls must be on strict subterms

**Solutions:**

**Pattern 1: Fix structural recursion**
```coq
(* ❌ BAD: Not structurally decreasing *)
Fixpoint bad (n : nat) : nat :=
  bad n.  (* n doesn't decrease! *)

(* ✅ GOOD: Structurally decreasing *)
Fixpoint good (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => good n'  (* n' is strict subterm of n *)
  end.
```

**Pattern 2: Use well-founded recursion**
```coq
Require Import Coq.Program.Wf.

Program Fixpoint my_div (n m : nat) {measure n} : nat :=
  if m =? 0 then 0
  else if n <? m then 0
  else 1 + my_div (n - m) m.
Next Obligation.
  (* Prove n - m < n *)
  lia.
Defined.
```

**Pattern 3: Use Function**
```coq
Require Import Coq.Program.Wf.
From Coq Require Import FunInd Recdef.

Function ack (m n : nat) {measure (fun p => fst p + snd p) (m, n)} : nat :=
  match m with
  | 0 => S n
  | S m' => match n with
           | 0 => ack m' 1
           | S n' => ack m' (ack m n')
           end
  end.
Proof.
  (* Prove termination for each recursive call *)
  - intros. simpl. lia.
  - intros. simpl. lia.
Defined.
```

**Pattern 4: Admit termination temporarily**
```coq
Require Import Coq.Program.Wf.

Program Fixpoint complex_rec (x : X) {measure (size x)} : Y :=
  (* complex body with recursion *)
  complex_rec (reduce x).
Next Obligation.
  admit.  (* TODO: Prove termination later *)
Admitted.
```

### 7. Non-Positive Occurrence

**Full error message:**
```
Non strictly positive occurrence of "T" in "T -> T".
```

**What it means:** Inductive type definition violates positivity requirement.

**Background:**
- Inductive types must be strictly positive
- Prevents logical inconsistency
- Type variable must not appear to left of arrow

**Examples:**

**Bad example:**
```coq
(* ❌ BAD: T appears negatively *)
Inductive Bad : Type :=
| MkBad : (Bad -> nat) -> Bad.  (* Bad to left of arrow *)
```

**Good examples:**
```coq
(* ✅ GOOD: Positive occurrences only *)
Inductive Good : Type :=
| MkGood : nat -> Good
| Combine : Good -> Good -> Good.

(* ✅ GOOD: Nested positive occurrence *)
Inductive Tree : Type :=
| Leaf : nat -> Tree
| Node : list Tree -> Tree.  (* list is positive *)
```

**Solutions:**

**Solution 1: Restructure type**
```coq
(* Instead of negative occurrence *)
(* Use separate type for functions *)
Inductive FunHolder : Type :=
| Hold : (nat -> nat) -> FunHolder.

Inductive MyType : Type :=
| Wrap : FunHolder -> MyType.
```

**Solution 2: Use parameter instead of index**
```coq
(* Parameterized type (positive) *)
Inductive Container (A : Type) : Type :=
| Empty : Container A
| Store : A -> Container A -> Container A.
```

### 8. Module and Import Errors

**Full error message:**
```
The reference Foo was not found in the current environment.
```

**What it means:** Definition not in scope.

**Common causes:**
- Missing `Require Import`
- Wrong module path
- Definition in different section
- Typo in name

**Solutions:**

**Pattern 1: Import correct module**
```coq
Require Import Coq.Lists.List.
Import ListNotations.

Check 1 :: 2 :: nil.  (* Now works *)
```

**Pattern 2: Use fully qualified names**
```coq
(* Without import *)
Check Coq.Lists.List.map.

(* Or import specific module *)
Require Import Coq.Lists.List.
Check List.map.

(* Or import and open *)
Require Import Coq.Lists.List.
Import List.
Check map.
```

**Pattern 3: Search for definition**
```coq
Search "map".          (* Find definitions with "map" *)
SearchAbout list.      (* Find lemmas about lists *)
SearchPattern (?X -> ?X). (* Find by pattern *)
Locate "++".           (* Find notation definition *)
```

**Pattern 4: Check module structure**
```coq
Print Module ModuleName. (* See module contents *)
Print Namespace.          (* See what's in scope *)
```

### 9. Ill-Typed Goal State

**Full error message:**
```
The term "..." has type "..." which should be coercible to "Prop".
```

**What it means:** Goal or hypothesis has wrong sort.

**Common scenario:**
- Trying to prove a `Type` instead of `Prop`
- Confusion between data and propositions

**Solutions:**

**Solution 1: Use correct sort**
```coq
(* For theorems, use Prop *)
Lemma my_lemma : forall n : nat, n = n.  (* Returns Prop *)
Proof.
  intro n. reflexivity.
Qed.

(* For data, use Type *)
Definition my_function (n : nat) : nat := n + 1.  (* Returns Type *)
```

**Solution 2: Extract Prop from Type if needed**
```coq
(* If you have data but need proposition *)
Definition is_even (n : nat) : Prop :=  (* Prop, not bool *)
  exists m, n = 2 * m.
```

### 10. Universe Occurs Check

**Full error message:**
```
Universe inconsistency (cannot enforce u < u).
```

**What it means:** Circular universe constraint detected.

**Common scenario:**
- Self-referential type definitions
- Incorrect universe polymorphism

**Solution:**
```coq
(* Usually indicates fundamental design problem *)
(* Restructure type hierarchy *)
(* Or use explicit universe declarations *)

Set Universe Polymorphism.
Definition careful@{u v | u < v} (A : Type@{u}) : Type@{v} :=
  A -> Type@{u}.
```

---

## Error Recovery Strategies

### General Debugging Workflow

1. **Read the error message carefully**
   - Note the exact location
   - Note the expected vs actual types
   - Check line and character position

2. **Inspect the goal state**
   ```coq
   Show.              (* Current goal *)
   Show Proof.        (* Proof term built so far *)
   ```

3. **Check types of relevant terms**
   ```coq
   Check hypothesis.
   Check lemma.
   Print definition.
   ```

4. **Search for relevant lemmas**
   ```coq
   Search pattern.
   SearchAbout constructor.
   SearchPattern (_ + _ = _ + _).
   ```

5. **Simplify and try again**
   ```coq
   simpl.             (* Simplify *)
   unfold def.        (* Make transparent *)
   (* Try tactic again *)
   ```

6. **Use more specific tactics**
   ```coq
   (* Instead of auto *)
   apply specific_lemma.

   (* Instead of destruct *)
   inversion H.
   ```

7. **Add intermediate steps**
   ```coq
   (* Instead of one complex step *)
   assert (H1 : intermediate). { proof1. }
   assert (H2 : another). { proof2. }
   (* Now prove goal using H1, H2 *)
   ```

### Common Tactic Patterns for Error Recovery

**Pattern: When reflexivity fails**
```coq
simpl.             (* Reduce first *)
unfold definition. (* Expose structure *)
reflexivity.       (* Try again *)
```

**Pattern: When apply fails**
```coq
eapply lemma.      (* Allow unification vars *)
(* Fill in holes *)
```

**Pattern: When rewrite fails**
```coq
rewrite lemma.     (* Fails *)
(* Try: *)
setoid_rewrite lemma. (* If equivalence relation *)
(* Or: *)
replace (LHS) with (RHS). 2: { prove equality. }
```

**Pattern: When automation fails**
```coq
auto.              (* Fails *)
(* Try stronger automation *)
eauto.
easy.
firstorder.
(* Or domain-specific *)
lia.               (* Arithmetic *)
ring.              (* Ring equations *)
congruence.        (* Equality reasoning *)
```

---

## Prevention: Best Practices

### Type Annotations

```coq
(* Add type annotations to prevent errors *)
Definition clear (n : nat) (m : nat) : nat := n + m.

(* Instead of letting Coq infer *)
Definition unclear n m := n + m.  (* What are the types? *)
```

### Explicit Instance Declarations

```coq
(* Declare instances explicitly when needed *)
#[export] Instance nat_inhabited : Inhabited nat := {| default := 0 |}.
```

### Modular Development

```coq
(* Use sections for local scope *)
Section MyProofs.
  Variable A : Type.
  Variable P : A -> Prop.

  Lemma local_lemma : ...
  Proof. ... Qed.
End MyProofs.
```

### Import Management

```coq
(* Import in controlled way *)
Require Import Coq.Lists.List.  (* Import module *)
Import ListNotations.            (* Import notation separately *)
Local Open Scope list_scope.    (* Local to section/file *)
```

### Incremental Development

```coq
(* Build proofs incrementally *)
Lemma big_theorem : Goal.
Proof.
  (* Step 1 *)
  intros.
  (* Check: Show. *)

  (* Step 2 *)
  destruct x.
  (* Check: Show. *)

  (* Step 3 *)
  apply lemma.
  (* Check: Show. *)

  (* Continue... *)
Qed.
```

---

## See Also

- [tactics-reference.md](tactics-reference.md) - Comprehensive tactic guide
- [rocq-phrasebook.md](rocq-phrasebook.md) - Proof patterns
- [domain-patterns.md](domain-patterns.md) - Domain-specific tactics
- [Coq Reference Manual - Error Messages](https://coq.inria.fr/distrib/current/refman/practical-tools/utilities.html)