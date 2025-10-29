# Rocq/Coq Standard Library and Ecosystem Guide

This guide helps you find and use lemmas from the Coq standard library and common third-party libraries. Knowing where to look saves hours of reproof.

**Key principle:** Always search before proving. Most standard results already exist.

## Quick Search Reference

| Want to find... | Use this command |
|----------------|------------------|
| Lemmas by name substring | `Search "substring".` |
| Lemmas about identifier | `SearchAbout nat.` |
| Lemmas by conclusion pattern | `SearchPattern (_ + _ = _ + _).` |
| Where notation is defined | `Locate "++".` |
| Lemmas in specific module | `Search nat inside Coq.Arith.` |
| All lemmas using both A and B | `Search A B.` |

---

## Table of Contents

1. [Standard Library Structure](#standard-library-structure)
2. [Core Modules](#core-modules)
3. [Search Strategies](#search-strategies)
4. [Third-Party Libraries](#third-party-libraries)
5. [Common Lemma Patterns](#common-lemma-patterns)
6. [Import Strategies](#import-strategies)

---

## Standard Library Structure

The Coq standard library is organized hierarchically:

```
Coq.
├── Init.           - Loaded by default (Datatypes, Logic, Nat, etc.)
├── Bool.           - Booleans and boolean functions
├── Arith.          - Natural number arithmetic
├── ZArith.         - Integer arithmetic (Z)
├── QArith.         - Rational arithmetic (Q)
├── Reals.          - Real number arithmetic (R)
├── Lists.          - List datatype and operations
├── Vectors.        - Dependent vectors
├── Strings.        - String datatype
├── Sets.           - Set theory
├── FSets.          - Finite sets (efficient implementations)
├── MSets.          - Modular finite sets
├── Relations.      - Binary relations
├── Wellfounded.    - Well-founded recursion
├── Program.        - Program extraction and automation
├── Classes.        - Typeclasses
├── Logic.          - Classical logic, choice, etc.
└── Sorting.        - Sorting algorithms and properties
```

---

## Core Modules

### Init (Loaded Automatically)

**Path:** `Coq.Init.*`

**Always available without import:**
- `Coq.Init.Datatypes` - nat, bool, option, sum, prod, list
- `Coq.Init.Logic` - and, or, exists, eq, iff, not
- `Coq.Init.Nat` - Basic nat operations
- `Coq.Init.Peano` - Peano axioms

**Key definitions:**
```coq
Print nat.        (* 0 and S constructor *)
Print bool.       (* true and false *)
Print option.     (* Some and None *)
Print list.       (* nil and cons *)
```

### Lists (`Coq.Lists.List`)

**Import:**
```coq
Require Import Coq.Lists.List.
Import ListNotations.  (* For [1; 2; 3] notation *)
```

**Key functions:**
```coq
Search list inside Coq.Lists.List.

(* Construction *)
nil : list A
cons : A -> list A -> list A
app : list A -> list A -> list A    (* Notation: ++ *)

(* Inspection *)
length : list A -> nat
hd : A -> list A -> A               (* Head with default *)
nth : nat -> list A -> A -> A       (* Nth element with default *)

(* Higher-order *)
map : (A -> B) -> list A -> list B
fold_left : (A -> B -> A) -> list B -> A -> A
fold_right : (A -> B -> B) -> list A -> B -> B
filter : (A -> bool) -> list A -> list A
exists_ : (A -> bool) -> list A -> bool
forall_ : (A -> bool) -> list A -> bool

(* Properties *)
In : A -> list A -> Prop           (* Element membership *)
incl : list A -> list A -> Prop    (* Subset *)
NoDup : list A -> Prop             (* No duplicates *)
```

**Common lemmas:**
```coq
app_nil_l : forall l, [] ++ l = l
app_nil_r : forall l, l ++ [] = l
app_assoc : forall l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)
map_map : forall f g l, map f (map g l) = map (f ∘ g) l
length_app : forall l1 l2, length (l1 ++ l2) = length l1 + length l2
in_app_iff : forall x l1 l2, In x (l1 ++ l2) <-> In x l1 \/ In x l2
```

### Natural Numbers (`Coq.Arith`)

**Import:**
```coq
Require Import Coq.Arith.Arith.
```

**Submodules:**
- `Coq.Arith.PeanoNat` - Main nat module
- `Coq.Arith.Plus` - Addition lemmas
- `Coq.Arith.Mult` - Multiplication lemmas
- `Coq.Arith.Minus` - Subtraction (monus)
- `Coq.Arith.Le` - Less-than-or-equal
- `Coq.Arith.Lt` - Strictly less-than
- `Coq.Arith.Compare_dec` - Decidable comparisons

**Common lemmas:**
```coq
(* Addition *)
Nat.add_0_l : forall n, 0 + n = n
Nat.add_0_r : forall n, n + 0 = n
Nat.add_comm : forall n m, n + m = m + n
Nat.add_assoc : forall n m p, (n + m) + p = n + (m + p)
Nat.add_succ_r : forall n m, n + S m = S (n + m)

(* Multiplication *)
Nat.mul_0_l : forall n, 0 * n = 0
Nat.mul_0_r : forall n, n * 0 = 0
Nat.mul_1_l : forall n, 1 * n = n
Nat.mul_1_r : forall n, n * 1 = n
Nat.mul_comm : forall n m, n * m = m * n
Nat.mul_assoc : forall n m p, (n * m) * p = n * (m * p)

(* Order *)
Nat.le_refl : forall n, n <= n
Nat.le_trans : forall n m p, n <= m -> m <= p -> n <= p
Nat.le_antisymm : forall n m, n <= m -> m <= n -> n = m
Nat.lt_irrefl : forall n, ~ n < n
Nat.lt_trans : forall n m p, n < m -> m < p -> n < p
```

### Integers (`Coq.ZArith.ZArith`)

**Import:**
```coq
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.
```

**Constructors:**
```coq
Z.of_nat : nat -> Z
Z.to_nat : Z -> nat
Z.pos : positive -> Z     (* Positive integers *)
Z.neg : positive -> Z     (* Negative integers *)
Z0 : Z                    (* Zero *)
```

**Common lemmas:**
```coq
Z.add_comm : forall n m : Z, n + m = m + n
Z.add_0_l : forall n : Z, 0 + n = n
Z.mul_comm : forall n m : Z, n * m = m * n
Z.mul_1_l : forall n : Z, 1 * n = n
Z.opp_involutive : forall n : Z, - - n = n
Z.sub_diag : forall n : Z, n - n = 0
```

### Reals (`Coq.Reals.Reals`)

**Import:**
```coq
Require Import Coq.Reals.Reals.
Open Scope R_scope.
```

**Note:** Real numbers axiomatized, complete ordered field.

**Common lemmas:**
```coq
Rplus_comm : forall r1 r2, r1 + r2 = r2 + r1
Rplus_0_l : forall r, 0 + r = r
Rmult_comm : forall r1 r2, r1 * r2 = r2 * r1
Rmult_1_l : forall r, 1 * r = r
Ropp_involutive : forall r, - - r = r
Rinv_l : forall r, r <> 0 -> / r * r = 1
```

**Automation:**
```coq
Require Import Lra.  (* Linear real arithmetic *)
Goal forall x y : R, x + y = y + x.
Proof. intros. lra. Qed.
```

### Booleans (`Coq.Bool.Bool`)

**Import:**
```coq
Require Import Coq.Bool.Bool.
```

**Functions:**
```coq
negb : bool -> bool
andb : bool -> bool -> bool     (* && *)
orb : bool -> bool -> bool      (* || *)
eqb : bool -> bool -> bool

(* Comparison *)
Nat.eqb : nat -> nat -> bool
Nat.leb : nat -> nat -> bool    (* <= *)
Nat.ltb : nat -> nat -> bool    (* < *)
```

**Reflection lemmas** (connect bool and Prop):
```coq
andb_true_iff : forall b1 b2, b1 && b2 = true <-> b1 = true /\ b2 = true
orb_true_iff : forall b1 b2, b1 || b2 = true <-> b1 = true \/ b2 = true
Nat.eqb_eq : forall n m, Nat.eqb n m = true <-> n = m
Nat.leb_le : forall n m, Nat.leb n m = true <-> n <= m
```

### Relations (`Coq.Relations.Relation_Definitions`)

**Import:**
```coq
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
```

**Properties:**
```coq
reflexive : forall A R, (forall x : A, R x x)
symmetric : forall A R, (forall x y : A, R x y -> R y x)
transitive : forall A R, (forall x y z : A, R x y -> R y z -> R x z)
antisymmetric : forall A R, (forall x y : A, R x y -> R y x -> x = y)
```

**Closure operators:**
```coq
clos_refl_trans : (A -> A -> Prop) -> A -> A -> Prop
clos_trans : (A -> A -> Prop) -> A -> A -> Prop
```

### Sets and Maps

**Finite sets (efficient):**
```coq
Require Import Coq.MSets.MSetInterface.
Require Import Coq.MSets.MSetWeakList.  (* List implementation *)
```

**Finite maps:**
```coq
Require Import Coq.FSets.FMapInterface.
Require Import Coq.FSets.FMapWeakList.  (* List implementation *)
```

---

## Search Strategies

### Basic Search Commands

**1. Search by substring:**
```coq
Search "comm".          (* Finds lemmas with "comm" in name *)
Search "assoc".         (* Finds associativity lemmas *)
```

**2. Search by identifier:**
```coq
SearchAbout nat.        (* All lemmas about nat *)
SearchAbout list.       (* All lemmas about lists *)
SearchAbout "++".       (* Lemmas using ++ notation *)
```

**3. Search by pattern:**
```coq
SearchPattern (_ + _ = _ + _).           (* Addition equations *)
SearchPattern (forall n : nat, _ <= _).  (* Nat inequalities *)
SearchPattern (_ ++ _ = _).              (* List append equations *)
```

**4. Search in specific module:**
```coq
Search nat inside Coq.Arith.
Search list inside Coq.Lists.
```

**5. Locate notation:**
```coq
Locate "++".            (* app : list A -> list A -> list A *)
Locate "<=".            (* le : nat -> nat -> Prop *)
Locate "::".            (* cons : A -> list A -> list A *)
```

### Advanced Search Strategies

**Combine searches:**
```coq
Search nat mult.        (* Lemmas mentioning both nat and mult *)
Search (_ * 0).         (* Multiplication by zero *)
Search (_ + 0) (_ = _). (* Addition by zero equations *)
```

**Search head constant:**
```coq
SearchHead le.          (* Lemmas concluding with le *)
SearchHead eq.          (* Equality lemmas *)
```

**Search rewrite candidate:**
```coq
SearchRewrite (_ + 0).  (* Lemmas that could rewrite _ + 0 *)
SearchRewrite (_ ++ []).
```

**Search by type:**
```coq
Search (nat -> nat -> nat).     (* Binary nat functions *)
Search (list ?A -> nat).        (* Functions from lists to nat *)
```

### Systematic Search Workflow

**Example: Proving `(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)`**

1. **Start with pattern search:**
   ```coq
   SearchPattern (_ ++ _ = _).
   ```

2. **Narrow down to append:**
   ```coq
   Search "app" "assoc".
   (* Finds: app_assoc *)
   ```

3. **Check the lemma:**
   ```coq
   Check app_assoc.
   (* app_assoc : forall (A : Type) (l m n : list A),
        (l ++ m) ++ n = l ++ (m ++ n) *)
   ```

4. **Apply it:**
   ```coq
   apply app_assoc.
   ```

---

## Third-Party Libraries

### Mathematical Components (MathComp)

**What:** Comprehensive library for mathematics (algebra, analysis, etc.)

**Style:** SSReflect tactics, bool reflection, canonical structures

**Import:**
```coq
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
```

**Key modules:**
- `ssreflect` - SSReflect tactics and boolean reflection
- `ssrnat` - Natural numbers (MathComp style)
- `seq` - Sequences (lists)
- `fintype` - Finite types
- `bigop` - Big operators (sum, product)
- `ssralg` - Algebraic hierarchy
- `ssrnum` - Numeric structures

**Documentation:** https://math-comp.github.io/

### Coquelicot (Real Analysis)

**What:** User-friendly real analysis library

**Import:**
```coq
Require Import Coquelicot.Coquelicot.
```

**Features:**
- Limits, continuity, differentiability
- Power series
- Better real number automation

**Documentation:** http://coquelicot.saclay.inria.fr/

### ExtLib (Extended Library)

**What:** Modern Coq library with monads, functors, etc.

**Import:**
```coq
From ExtLib Require Import *
```

**Features:**
- Monad type classes
- Functor, Applicative
- Data structures (maps, tries)

### Equations (Dependent Pattern Matching)

**What:** Improved definition mechanism

**Import:**
```coq
From Equations Require Import Equations.
```

**Use:** Better dependent pattern matching and well-founded recursion

### Stdpp (Standard Library++)

**What:** Modern alternative/extension to stdlib

**Import:**
```coq
From stdpp Require Import base.
```

**Features:**
- Better type classes
- Modern data structures
- Efficient maps and sets

---

## Common Lemma Patterns

### Equality Lemmas

**Identity:**
```coq
Search (?x = ?x).       (* Reflexivity *)
Search (?x + 0).        (* Right identity *)
Search (0 + ?x).        (* Left identity *)
Search (?x * 1).
Search (1 * ?x).
```

**Associativity:**
```coq
Search "assoc".
Search ((_ + _) + _).
Search ((_ * _) * _).
Search ((_ ++ _) ++ _).
```

**Commutativity:**
```coq
Search "comm".
Search (?x + ?y = ?y + ?x).
Search (?x * ?y = ?y * ?x).
```

### Order Lemmas

**Reflexivity, transitivity, antisymmetry:**
```coq
SearchAbout le.
Search (?x <= ?x).              (* Reflexivity *)
Search (?x <= ?y -> ?y <= ?z).  (* Transitivity *)
Search (?x <= ?y -> ?y <= ?x).  (* Antisymmetry *)
```

**Comparisons:**
```coq
Search (?x < ?y -> ?x <= ?y).
Search (?x <= ?y -> ?y <= ?z -> ?x <= ?z).
```

### List Lemmas

**Structure:**
```coq
Search ([] ++ ?l).       (* Left identity *)
Search (?l ++ []).       (* Right identity *)
Search (length (_ ++ _)).
Search (length (map _ _)).
```

**Membership:**
```coq
Search (In _ (_ ++ _)).
Search (In _ (map _ _)).
```

**Higher-order:**
```coq
Search (map _ (map _ _)).
Search (map _ (_ ++ _)).
Search (fold_left _ (_ ++ _)).
```

---

## Import Strategies

### Minimal Imports

```coq
(* Only import what you need *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
```

### Scoped Imports

```coq
(* Open scope locally *)
Local Open Scope list_scope.
Local Open Scope nat_scope.

(* Or in section *)
Section MySection.
  Open Scope Z_scope.
  (* Z notation active here *)
End MySection.
```

### Controlled Notation

```coq
(* Import module but not notation *)
Require Import Coq.Lists.List.
(* Don't do: Import ListNotations. *)

(* Use qualified names *)
Definition my_list := cons 1 (cons 2 nil).

(* Or import notation later when needed *)
```

### Dealing with Conflicts

```coq
(* If two modules define same name *)
Require Import Module1.
Require Import Module2.

(* Use qualified names *)
Module1.function.
Module2.function.

(* Or rename on import *)
Require Import Module1 as M1.
Require Import Module2 as M2.
```

---

## Library Organization Tips

### Project Structure

```coq
(* Create your own modules *)
(* File: MyProject/Util.v *)
Section Utilities.
  (* Helper definitions and lemmas *)
End Utilities.

(* File: MyProject/Main.v *)
Require Import MyProject.Util.
(* Use utilities *)
```

### Building Lemma Libraries

```coq
(* Collect domain-specific lemmas *)
Section AlgebraicLemmas.
  Context {A : Type}.
  Context {op : A -> A -> A}.
  Context {e : A}.

  Hypothesis assoc : forall x y z, op (op x y) z = op x (op y z).
  Hypothesis ident : forall x, op e x = x /\ op x e = x.

  (* Derive lemmas *)
  Lemma ident_unique : (* ... *).
  (* ... *)
End AlgebraicLemmas.
```

---

## Decision Tree: Finding Lemmas

```
What do you need?
├─ About standard type (nat, list, bool)
│  └─ Search in Coq.Init, Coq.Arith, Coq.Lists, Coq.Bool
│     ├─ SearchAbout nat
│     ├─ SearchPattern (_ + _)
│     └─ Search "lemma_name_part"
│
├─ About integers/rationals/reals
│  └─ Search in Coq.ZArith, Coq.QArith, Coq.Reals
│     └─ Open appropriate scope first
│
├─ About relations/orders
│  └─ Search in Coq.Relations, Coq.Setoids
│     └─ SearchPattern (reflexive _)
│
├─ Algebraic property
│  └─ Try MathComp if available
│     └─ From mathcomp Require Import ssralg
│
├─ Analysis/reals
│  └─ Try Coquelicot if available
│     └─ Require Import Coquelicot.Coquelicot
│
└─ Can't find anything
   ├─ Check if using right terms (synonym search)
   ├─ Try broader search: SearchAbout topic
   ├─ Check documentation/tutorials
   └─ Consider: maybe you need to prove it!
```

---

## Common "Not Found" Issues

**1. Wrong module:**
```coq
(* Looking for List.map but didn't import *)
Require Import Coq.Lists.List.
```

**2. Wrong scope:**
```coq
(* Looking for Z operations but in nat scope *)
Open Scope Z_scope.
```

**3. Wrong library:**
```coq
(* Standard library doesn't have advanced algebra *)
(* Need MathComp *)
From mathcomp Require Import ssralg.
```

**4. Lemma doesn't exist:**
```coq
(* Sometimes you really do need to prove it yourself *)
Lemma my_custom_property : (* ... *).
```

---

## See Also

- [rocq-phrasebook.md](rocq-phrasebook.md) - Proof patterns
- [tactics-reference.md](tactics-reference.md) - Tactic guide
- [ssreflect-patterns.md](ssreflect-patterns.md) - MathComp/SSReflect guide
- [Coq Standard Library Documentation](https://coq.inria.fr/distrib/current/stdlib/)
- [MathComp Book](https://math-comp.github.io/mcb/)

---

**Further Reading:**
- [Coq'Art](https://www.labri.fr/perso/casteran/CoqArt/) - Comprehensive Coq book
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) - Learning Coq from scratch
- [CPDT](http://adam.chlipala.net/cpdt/) - Certified Programming with Dependent Types
