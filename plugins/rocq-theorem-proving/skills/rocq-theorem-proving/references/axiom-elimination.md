# Axiom Elimination: Removing Custom Axioms

## Overview

This guide provides systematic strategies for identifying and eliminating custom axioms from Rocq/Coq proofs.

**Core principle:** Axioms are technical debt. Every custom axiom weakens your development and should be eliminated or justified.

**Goal:** Zero custom axioms. Use only standard axioms (Classical logic, choice) when necessary.

---

## Table of Contents

1. [Understanding Axioms](#understanding-axioms)
2. [Finding Axioms](#finding-axioms)
3. [Standard vs Custom Axioms](#standard-vs-custom-axioms)
4. [Elimination Strategies](#elimination-strategies)
5. [When Axioms Are Acceptable](#when-axioms-are-acceptable)
6. [Verification](#verification)

---

## Understanding Axioms

### What is an Axiom?

An axiom is an unproven statement assumed to be true.

```coq
(* Axiom declaration *)
Axiom my_assumption : forall n : nat, P n.

(* Can now use without proof *)
Lemma example : P 5.
Proof.
  apply my_assumption.
Qed.
```

**Problem:** No guarantee `my_assumption` is actually true!

### Axioms vs Admits

| Aspect | Axiom | Admit/Admitted |
|--------|-------|----------------|
| Has proof structure? | No | Partial |
| Intent | Foundational assumption | Incomplete work |
| Visibility | Explicit declaration | Inside proof |
| Fix | Prove or justify | Complete proof |

### Why Eliminate Axioms?

**1. Soundness risk**
```coq
Axiom absurd : False.  (* Oops! Now can prove anything *)

Lemma anything : 1 = 2.
Proof.
  exfalso.
  apply absurd.
Qed.
```

**2. Opacity**
- Can't reduce/compute through axioms
- Black box in proofs
- Hides actual reasoning

**3. Portability**
- Non-standard axioms not accepted everywhere
- Can't extract to executable code
- May conflict with other axioms

---

## Finding Axioms

### Find All Axioms in a Theorem

```coq
(* Check what axioms a theorem depends on *)
Lemma my_theorem : P.
Proof. (* ... *) Qed.

Print Assumptions my_theorem.
```

**Output examples:**

**Good (no axioms):**
```
Closed under the global context
```

**Has standard axioms:**
```
Axioms:
functional_extensionality_dep : ...
classical_choice : ...
```

**Has custom axioms (BAD):**
```
Axioms:
my_custom_axiom : forall n, P n
```

### Find All Axioms in File

**Manual search:**
```bash
grep "^Axiom " file.v
grep "^Parameter " file.v  # Parameters are like axioms
```

**Check each theorem:**
```coq
(* For each theorem *)
Print Assumptions theorem1.
Print Assumptions theorem2.
Print Assumptions theorem3.
```

### Find All Custom Axioms in Project

```bash
# Find axiom declarations
find . -name "*.v" -exec grep -Hn "^Axiom \|^Parameter " {} \;

# For each file, check major theorems
for file in *.v; do
  echo "=== $file ==="
  # Extract theorem names
  grep "^Lemma \|^Theorem \|^Proposition " $file
done

# Then manually check each with Print Assumptions
```

---

## Standard vs Custom Axioms

### Standard Axioms (Generally Acceptable)

These are well-understood and safe to use:

**1. Functional Extensionality**
```coq
Require Import FunctionalExtensionality.

(* Axiom: Functions equal if equal at all points *)
Check functional_extensionality.
(* : forall f g : A -> B, (forall x, f x = g x) -> f = g *)
```
- Widely accepted
- Needed for function equality
- Compatible with Coq

**2. Propositional Extensionality**
```coq
Require Import PropExtensionality.

(* Axiom: Props equal if logically equivalent *)
Check propositional_extensionality.
(* : forall P Q : Prop, (P <-> Q) -> P = Q *)
```
- For classical reasoning about Props
- Weaker than proof irrelevance

**3. Classical Logic**
```coq
Require Import Classical.

Check classic.
(* : forall P : Prop, P \/ ~ P *)
(* Excluded middle *)

Check NNPP.
(* : forall P : Prop, ~ ~ P -> P *)
(* Double negation elimination *)
```
- Well-understood
- Needed for classical reasoning
- Incompatible with constructive extraction

**4. Axiom of Choice**
```coq
Require Import ClassicalChoice.

Check choice.
(* : forall (A B : Type) (R : A -> B -> Prop),
       (forall x : A, exists y : B, R x y) ->
       exists f : A -> B, forall x : A, R x (f x) *)
```
- Standard in classical mathematics
- Needed for some constructions
- Various forms available

**5. Proof Irrelevance**
```coq
Require Import ProofIrrelevance.

Check proof_irrelevance.
(* : forall (P : Prop) (p1 p2 : P), p1 = p2 *)
```
- All proofs of same Prop are equal
- Useful for working with subtypes
- Accepted in most contexts

### Custom Axioms (Must Justify or Eliminate)

**Any axiom you declare yourself:**

```coq
(* Custom axioms - need elimination strategy *)
Axiom my_lemma : forall n, n + 0 = n.  (* Should be proven! *)
Axiom todo : complex_statement.         (* Incomplete work *)
Parameter external_fact : P.            (* External assumption *)
```

---

## Elimination Strategies

### Strategy 1: Prove It

**Best solution:** Replace axiom with actual proof.

```coq
(* Before *)
Axiom add_comm : forall n m, n + m = m + n.

(* After - search found it *)
Lemma add_comm : forall n m, n + m = m + n.
Proof. apply Nat.add_comm. Qed.

(* Or prove it yourself *)
Lemma add_comm_custom : forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite IHn'. rewrite Nat.add_succ_r. reflexivity.
Qed.
```

**Process:**
1. Try searching for existing lemma (see [admit-filling.md](admit-filling.md))
2. Try automation (`lia`, `ring`, `auto`)
3. If neither works, prove manually
4. Replace `Axiom` with `Lemma ... Proof ... Qed`

### Strategy 2: Weaken to Standard Axiom

**If axiom is consequence of standard axiom, import standard one.**

```coq
(* Before - custom axiom *)
Axiom excluded_middle : forall P : Prop, P \/ ~P.

(* After - use standard Classical *)
Require Import Classical.
(* Now have 'classic : forall P : Prop, P \/ ~P' *)

(* Replace uses *)
Lemma example (P : Prop) : P \/ ~P.
Proof. apply classic. Qed.  (* Use standard axiom *)
```

### Strategy 3: Make Constructive

**Avoid classical axiom by constructive proof.**

```coq
(* Before - uses excluded middle *)
Lemma decidable_nat_eq : forall n m : nat, n = m \/ n <> m.
Proof.
  intros n m.
  apply classic.  (* Classical axiom! *)
Qed.

(* After - constructive *)
Require Import Arith.

Lemma decidable_nat_eq : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n m.
  apply Nat.eq_dec.  (* Decidable, no axiom *)
Qed.
```

**Change type:**
- `P \/ ~P` (classical) → `{P} + {~P}` (decidable, constructive)
- Use decidable types when possible

### Strategy 4: Pass as Parameter

**If truly external assumption, make it explicit parameter.**

```coq
(* Before - hidden axiom *)
Axiom oracle : nat -> bool.  (* External decision procedure *)

Lemma using_oracle : forall n, oracle n = true -> P n.
Proof. (* ... *) Qed.

(* After - explicit parameter *)
Section WithOracle.
  Variable oracle : nat -> bool.

  Lemma using_oracle : forall n, oracle n = true -> P n.
  Proof. (* ... *) Qed.

End WithOracle.

(* Now oracle is explicit assumption in type *)
Check using_oracle.
(* : forall oracle : nat -> bool, forall n, oracle n = true -> P n *)
```

**Benefits:**
- Makes assumption explicit
- Users know they need to provide oracle
- No hidden axiom

### Strategy 5: Restrict Scope

**If axiom needed only locally, use Section.**

```coq
(* Before - global axiom *)
Axiom local_fact : P.

Lemma using_fact : Q.
Proof.
  apply local_fact.
  (* ... *)
Qed.

(* After - section variable *)
Section LocalProofs.
  Hypothesis local_fact : P.  (* Or: Variable *)

  Lemma using_fact : Q.
  Proof.
    apply local_fact.
    (* ... *)
  Qed.

End LocalProofs.

(* Now local_fact is parameter, not axiom *)
Check using_fact.
(* : P -> Q *)  (* Explicit dependency! *)
```

---

## Common Axiom Patterns and Fixes

### Pattern 1: "Will Prove Later"

```coq
(* ❌ BAD *)
Axiom helper_lemma : intermediate_result.

Lemma main_theorem : final_result.
Proof.
  apply helper_lemma.
  (* ... *)
Qed.

(* ✅ GOOD *)
Lemma helper_lemma : intermediate_result.
Proof.
  admit.  (* Explicit incomplete *)
Admitted.

Lemma main_theorem : final_result.
Proof.
  apply helper_lemma.
  (* ... *)
Qed.

(* Then fill helper_lemma later *)
```

**Fix:** Use `Admitted` for incomplete work, not `Axiom`.

### Pattern 2: "Should Be in Library"

```coq
(* ❌ BAD *)
Axiom list_app_assoc : forall A (l1 l2 l3 : list A),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).

(* ✅ GOOD - it IS in library! *)
Require Import Coq.Lists.List.

Lemma list_app_assoc : forall A (l1 l2 l3 : list A),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. intros. apply app_assoc. Qed.
```

**Fix:** Search thoroughly before declaring axiom.

### Pattern 3: Classical Logic

```coq
(* ❌ BAD - custom *)
Axiom excluded_middle : forall P, P \/ ~P.

(* ✅ GOOD - standard *)
Require Import Classical.
(* Use 'classic' instead *)
```

**Fix:** Use standard Classical library.

### Pattern 4: Function Extensionality

```coq
(* ❌ BAD - custom *)
Axiom my_ext : forall f g : nat -> nat,
  (forall n, f n = g n) -> f = g.

(* ✅ GOOD - standard *)
Require Import FunctionalExtensionality.

Lemma my_ext : forall f g : nat -> nat,
  (forall n, f n = g n) -> f = g.
Proof.
  intros f g H.
  apply functional_extensionality.
  exact H.
Qed.
```

**Fix:** Use standard FunctionalExtensionality.

### Pattern 5: External Decidable

```coq
(* ❌ BAD - undecidable claimed decidable *)
Axiom halts : (nat -> nat) -> bool.  (* Halting problem! *)

(* ✅ GOOD - make assumption explicit *)
Section WithDecidability.
  Variable decidable_property : (nat -> nat) -> bool.

  Hypothesis decidable_correct :
    forall f, decidable_property f = true <-> halts_properly f.

  (* Theorems using the assumption *)

End WithDecidability.
```

**Fix:** Make undecidable assumptions explicit parameters.

---

## When Axioms Are Acceptable

### Acceptable Cases

**1. Standard foundational axioms**
```coq
Require Import Classical.          (* Excluded middle *)
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
```
- Well-understood
- Widely accepted
- Necessary for certain developments

**2. Explicitly approved by user**
```coq
(* USER APPROVED: Using oracle for performance *)
(* ELIMINATION STRATEGY: Can be made constructive but would be 100x slower *)
Axiom fast_oracle : nat -> bool.
```
- Documented justification
- Explicit approval
- Clear elimination strategy (even if not pursued)

**3. Interface to unverified code**
```coq
(* External library interface *)
Parameter ml_random : unit -> nat.
Extract Constant ml_random => "Random.int".
```
- Extraction target
- Clear boundary between verified and unverified
- Documented

### Never Acceptable

**1. Undocumented axioms**
```coq
(* ❌ BAD - why does this exist? *)
Axiom mysterious : forall n, P n.
```

**2. Provable statements**
```coq
(* ❌ BAD - this is Nat.add_comm! *)
Axiom add_comm : forall n m, n + m = m + n.
```

**3. Inconsistent axioms**
```coq
(* ❌ BAD - contradictory! *)
Axiom false : False.  (* Never! *)
```

---

## Verification

### Check Theorem Dependencies

```coq
Lemma my_theorem : P.
Proof. (* ... *) Qed.

(* Check all assumptions *)
Print Assumptions my_theorem.
```

**Interpret output:**

```
(* ✅ BEST - no axioms *)
Closed under the global context

(* ✅ ACCEPTABLE - standard axioms only *)
Axioms:
functional_extensionality_dep : ...

(* ❌ BAD - custom axioms *)
Axioms:
my_custom_fact : ...
functional_extensionality_dep : ...

(* ❌ VERY BAD - admits *)
Axioms:
my_custom_fact : ...
my_theorem.proof_admitted : ...  (* From 'admit' or 'Admitted' *)
```

### Check Entire File

```bash
# Create script: check_axioms.sh
#!/bin/bash

FILE=$1

# Extract all theorem names
THEOREMS=$(grep "^Lemma \|^Theorem \|^Proposition " "$FILE" | \
           sed 's/^[^[:space:]]* \([^[:space:]]*\).*/\1/')

# For each, check assumptions
for thm in $THEOREMS; do
  echo "=== $thm ==="
  echo "Print Assumptions $thm." | coqtop -load-vernac-source "$FILE" -q 2>/dev/null | \
    grep -A 5 "Axioms:"
done
```

### Continuous Integration

```yaml
# In CI config
- name: Check for custom axioms
  run: |
    # Fail if any custom axioms found
    ./scripts/check_axioms.sh src/*.v
```

---

## Elimination Workflow

### Step 1: Inventory

```bash
# Find all axiom declarations
grep -rn "^Axiom \|^Parameter " --include="*.v" src/

# For each theorem
coqtop -q
> Require Import MyFile.
> Print Assumptions my_theorem.
```

### Step 2: Classify

**For each axiom:**
- Is it standard (Classical, FunExt, etc.)?
- Is it custom?
- Who uses it?

### Step 3: Eliminate

**Priority order:**
1. ⭐⭐⭐⭐⭐ Provable statements (search + prove)
2. ⭐⭐⭐⭐ Consequences of standard axioms (import standard)
3. ⭐⭐⭐ Can be made constructive (change type)
4. ⭐⭐ Need as parameters (make explicit)
5. ⭐ Truly foundational (document + justify)

### Step 4: Verify

After each elimination:
```bash
dune build  # or: coqc file.v

# Verify axiom count decreasing
grep -c "^Axiom " file.v

# Check theorems still build
Print Assumptions main_theorem.
```

### Step 5: Document

```coq
(* If axiom remains, document *)

(** * Foundational Axioms

    This development uses the following non-standard axioms:

    - [oracle_decides]: External decision procedure for halting
      - Justification: Interface to unverified ML code
      - Elimination strategy: Could be made constructive but 100x slower
      - Approved: 2025-01-15
*)

Axiom oracle_decides : program -> bool.
```

---

## See Also

- [admit-filling.md](admit-filling.md) - Completing incomplete proofs
- [stdlib-guide.md](stdlib-guide.md) - Finding existing lemmas
- [compilation-errors.md](compilation-errors.md) - Fixing proofs

---

**Philosophy:** Every axiom is a claim without proof. In formal verification, our job is to *prove* things, not assume them. Axioms are intellectual debt - sometimes necessary, but always needing justification.

**Goal:** Zero custom axioms. Standard foundational axioms only when needed and documented.
