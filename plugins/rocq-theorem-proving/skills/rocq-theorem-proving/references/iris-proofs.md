# Iris Separation Logic: Proof Patterns

**Iris is a higher-order concurrent separation logic framework for reasoning about concurrent and higher-order imperative programs.**

This guide covers essential patterns, tactics, and techniques for writing correct Iris proofs in Coq/Rocq.

**Key insight:** Iris extends separation logic with **invariants**, **ghost state**, and **modal operators** to reason about concurrent programs compositionally. Master the proof mode tactics and understand resource ownership to write effective proofs.

---

## Table of Contents

1. [Core Concepts](#core-concepts)
2. [Import Organization](#import-organization)
3. [Resource Algebras and Ghost State](#resource-algebras-and-ghost-state)
4. [Equalities and Entailments](#equalities-and-entailments)
5. [Proof Mode Tactics](#proof-mode-tactics)
6. [HeapLang Verification](#heaplang-verification)
7. [Common Patterns](#common-patterns)
8. [Handling Modalities](#handling-modalities)
9. [Invariant Management](#invariant-management)
10. [Style Guide](#style-guide)
11. [Common Pitfalls](#common-pitfalls)
12. [Complete Examples](#complete-examples)

---

## Core Concepts

### Separation Logic Basics

**Key operators:**
- `P ∗ Q` - Separating conjunction (resources combined)
- `P -∗ Q` - Magic wand (implication that consumes resources)
- `P ∨ Q` - Disjunction
- `P ∧ Q` - Conjunction
- `⌜φ⌝` - Pure assertion (embed Coq propositions)

**Resource ownership:**
- Spatial hypotheses: Can only be used once (consumed)
- Persistent/Intuitionistic hypotheses: Can be used multiple times (prefixed with `#`)

**Example:**
```coq
(* Spatial: l ↦ v - Exclusive ownership of location l with value v *)
(* Persistent: #l ↦□ v - Persistent read-only ownership *)
```

### Modal Operators

**Update modality `|==> P`:**
- Allows ghost state updates
- Eliminates with `iMod`

**Fancy update `|={E1,E2}=> P`:**
- Updates with mask management (controls which invariants are open)
- `E1` = invariants available before
- `E2` = invariants available after

**Later modality `▷ P`:**
- Step-indexing for recursive predicates
- Eliminates with `iNext`

**Persistence modality `□ P`:**
- Makes assertions persistent
- Eliminates with `iModIntro`

---

## Import Organization

**Critical:** Order imports from most distant to most local. This prevents later imports from shadowing earlier declarations.

**Recommended order:**
```coq
From Coq Require Import ...                    (* 1. Coq standard library *)
From stdpp Require Import ...                  (* 2. stdpp (std++) *)
From iris.algebra Require Import ...           (* 3. Resource algebras *)
From iris.bi Require Import ...                (* 4. Bunched implications *)
From iris.proofmode Require Import ...         (* 5. Proof mode *)
From iris.base_logic Require Import ...        (* 6. Base logic *)
From iris.program_logic Require Import ...     (* 7. Program logic *)
From iris.heap_lang Require Import ...         (* 8. HeapLang *)
```

**Why this matters:**
- Later imports take precedence over earlier ones
- Ensures relevant notations and instances are prioritized correctly
- Prevents unexpected shadowing of tactics or notations

---

## Resource Algebras and Ghost State

### What are Resource Algebras?

Resource Algebras (RAs) are the mathematical foundation of Iris's ghost state. They provide a way to track **logical resources** that don't exist at runtime but are essential for proofs.

**Key properties of RAs:**
- **Composition (`·`)**: Combine resources
- **Unit (`ε`)**: Empty resource
- **Validity (`✓`)**: Valid resource states
- **Core (`core`)**: Extract persistent part

### Common Resource Algebras

#### 1. Exclusive Resource (`exclR A`)

**Purpose:** Exactly one owner at a time (like unique ownership).

**Example:**
```coq
(* Only one thread can own this resource *)
own γ (Excl v)

(* Combining two exclusive resources is invalid *)
Excl v · Excl w  (* Invalid! *)
```

**Use cases:**
- Unique tokens
- Linear resources
- Exclusive access rights

#### 2. Authoritative Resource (`authR A`)

**Purpose:** One authoritative owner, many fragment owners.

**Pattern:** `● a` (authoritative) and `◯ a` (fragment)

**Key property:** Fragments must be included in authoritative element.

**Example:**
```coq
(* Authoritative owner has full state *)
own γ (● n)

(* Fragment owner has partial knowledge *)
own γ (◯ m)

(* Fragment must agree: m ≤ n *)
own γ (● n) -∗ own γ (◯ m) -∗ ⌜m ≤ n⌝
```

**Use cases:**
- Monotone counters
- Authoritative state with distributed views
- Ownership tracking

**Example: Monotone Counter**
```coq
Definition counter_inv (γ : gname) (l : loc) : iProp Σ :=
  ∃ (n : nat), l ↦ #n ∗ own γ (●E n).

(* Thread has fragment *)
own γ (◯E m) -∗
(* When incrementing counter *)
counter_inv γ l -∗
(* Fragment can be updated *)
|==> counter_inv γ l ∗ own γ (◯E (m + 1)).
```

#### 3. Agreement Resource (`agreeR A`)

**Purpose:** Multiple parties agree on a value.

**Property:** Can combine if values agree, invalid otherwise.

**Example:**
```coq
(* Two parties with agreement *)
own γ (to_agree v) ∗ own γ (to_agree w) -∗ ⌜v = w⌝

(* Once set, cannot change *)
```

**Use cases:**
- Immutable shared values
- Read-only shared state
- Consensus

#### 4. Fractional Resource (`fracR`)

**Purpose:** Split ownership into fractions (like fractional permissions).

**Pattern:** `q · r` where `q, r ∈ (0, 1]`

**Example:**
```coq
(* Full ownership *)
own γ (1%Qp)

(* Split into halves *)
own γ (1%Qp) ==∗ own γ (1/2%Qp) ∗ own γ (1/2%Qp)

(* Recombine *)
own γ (1/2%Qp) ∗ own γ (1/2%Qp) ==∗ own γ (1%Qp)
```

**Use cases:**
- Fractional heap permissions
- Reader-writer patterns
- Temporary ownership transfer

#### 5. One-Shot Resource (`one_shotR`)

**Purpose:** Resource that transitions from "pending" to "shot" exactly once.

**Definition:** `csumR (exclR unitO) (agreeR A)`

**States:**
- `Cinl (Excl ())` - Pending (not shot yet)
- `Cinr (to_agree v)` - Shot with value `v`

**Example:**
```coq
(* Initially pending *)
own γ (Cinl (Excl ()))

(* Shoot with value v *)
own γ (Cinl (Excl ())) ==∗ own γ (Cinr (to_agree v))

(* Once shot, cannot change *)
own γ (Cinr (to_agree v)) ∗ own γ (Cinr (to_agree w)) -∗ ⌜v = w⌝
```

**Use cases:**
- Single-assignment variables
- Initialization protocols
- Future/promise patterns

### Resource Algebra Combinators

**Building complex RAs from simple ones:**

| Combinator | Notation | Purpose |
|------------|----------|---------|
| Product | `prodR A B` | Pair of resources |
| Sum | `csumR A B` | Either A or B |
| Option | `optionR A` | Optional resource |
| List | `listR A` | List of resources |
| Map | `gmapR K V` | Finite map |
| Function | `A -d> B` | Discrete function space |

**Example: Combining RAs**
```coq
(* one_shotR is defined using combinators *)
Definition one_shotR (A : ofe) : cmra :=
  csumR (exclR unitO) (agreeR A).

(* Product for multiple ghost names *)
Definition stateR := prodR (authR natO) (agreeR valO).
```

### Ghost State Management

#### Allocating Ghost State

**Pattern:**
```coq
iMod (own_alloc (● initial_value)) as (γ) "Hγ".
```

**Example:**
```coq
(* Allocate authoritative counter *)
iMod (own_alloc (●E 0)) as (γ) "Hγ_auth".
{ apply auth_both_valid_discrete. split; done. }

(* Now have: Hγ_auth : own γ (●E 0) *)
```

#### Updating Ghost State

**Pattern:**
```coq
iMod (own_update with "Hγ") as "Hγ".
{ apply update_rule. }
```

**Example: Update authoritative state**
```coq
(* Have: own γ (●E n) *)
iMod (own_update with "Hγ_auth") as "Hγ_auth".
{ apply auth_update_alloc, (op_local_update_discrete _ _ 1). }
(* Now: own γ (●E (n + 1)) *)
```

#### Combining Ghost State

**Pattern with `own_update_2`:**
```coq
iMod (own_update_2 with "Hγ_auth Hγ_frag") as "[Hγ_auth Hγ_frag]".
{ apply update_rule_2. }
```

**Example: Authoritative + Fragment**
```coq
(* Have: own γ (●E n), own γ (◯E m) *)
iMod (own_update_2 with "Hγ_auth Hγ_frag") as "[Hγ_auth Hγ_frag]".
{ apply auth_update_alloc, (op_local_update_discrete _ _ 1). }
(* Now both incremented *)
```

### Library Design with Ghost State

#### Type Class Structure

**For libraries requiring ghost state:**

```coq
(* 1. Define the resource algebra *)
Class myLibG Σ := MyLibG {
  myLib_inG :> inG Σ myLibR;
  myLib_name : gname;
}.

(* 2. Define the functor list *)
Definition myLibΣ : gFunctors := #[GFunctor myLibR].

(* 3. Prove subG instance *)
Instance subG_myLibΣ {Σ} : subG myLibΣ Σ → myLibGpreS Σ.
```

**Singleton enforcement:**

Libraries with global state (like heap) use **singleton** typeclasses to ensure exactly one instance:

```coq
(* Pre-state: for initialization *)
Class heapGpreS Σ := HeapGpreS {
  heap_preG_inG :> inG Σ heapR;
}.

(* Singleton state: includes gname *)
Class heapGS Σ := HeapGS {
  heap_inG :> inG Σ heapR;
  heap_name : gname;
}.
```

**Why singleton?** "Two instances might have different gnames, so ↦ based on these two distinct instances would be incompatible."

#### Initialization Pattern

```coq
Lemma heap_init `{!heapGpreS Σ} :
  ⊢ |==> ∃ _ : heapGS Σ, heap_interp ∅.
Proof.
  iMod (own_alloc (● ∅)) as (γ) "Hγ".
  { apply auth_auth_valid. done. }
  iModIntro.
  iExists (HeapGS _ _ γ).
  done.
Qed.
```

### Naming Conventions for RAs

| Suffix | Meaning | Example |
|--------|---------|---------|
| `R` | Resource Algebra | `exclR`, `authR` |
| `O` | OFE (ordered functor) | `natO`, `valO` |
| `UR` | Unital RA | `gmapUR` |
| `G` | Ghost state typeclass | `heapGS` |
| `Σ` | Functor list | `heapΣ` |
| `GpreS` | Pre-state typeclass | `heapGpreS` |

---

## Equalities and Entailments

Understanding the different notions of equality and entailment in Iris is **crucial** for writing correct proofs.

### Hierarchy of Equalities

```
Coq Level (Metalogic)
├─ Leibniz Equality (=)          [Strongest]
└─ Setoid Equality (≡)

OFE Level
├─ Distance (≡{n}≡)
└─ Non-expansiveness

Iris Level (Inside Logic)
├─ Internal Equality ((a ≡ b)%I)
├─ Bi-entailment (P ⊣⊢ Q)         [Weakest for propositions]
└─ Entailment (P ⊢ Q)
```

### 1. Leibniz Equality (`=`)

**Coq's standard propositional equality.**

**Level:** Metalogic (Coq)

**Usage:**
```coq
(* Use for Coq types and values *)
forall (n m : nat), n = m → ...

(* In pure assertions *)
⌜x = y⌝
```

**Properties:**
- Strongest form of equality
- Requires syntactic/definitional equivalence
- Can be rewritten with Coq's `rewrite`

### 2. Setoid Equality (`≡` / `equiv`)

**Defined by `Equiv A` typeclass with `Equivalence` proof.**

**Level:** Metalogic (Coq)

**Usage:**
```coq
(* For types with custom equivalence *)
f ≡ g  (* Functions equal pointwise *)

(* Lists with setoid elements *)
xs ≡ ys
```

**Properties:**
- More flexible than Leibniz
- Allows extensional equality
- Some types are "Leibniz types" where `≡` coincides with `=`

**When `≡` = `=`:**
```coq
Class LeibnizEquiv A `{Equiv A} := leibniz_equiv : ∀ x y, x ≡ y → x = y.

(* For these types, can convert between ≡ and = *)
```

### 3. OFE Distance (`≡{n}≡` / `dist n`)

**Measures "how equal" values are up to step-index `n`.**

**Level:** OFE (Ordered Family of Equivalences)

**Usage:**
```coq
(* Distance n *)
x ≡{n}≡ y

(* Limit: equivalent at all indices *)
x ≡ y  ≡  ∀ n, x ≡{n}≡ y
```

**Properties:**
- Used for step-indexed logic
- Non-expansive functions preserve distance
- Later modality increases distance

**Non-expansiveness:**
```coq
(* f is non-expansive *)
NonExpansive f := ∀ n x y, x ≡{n}≡ y → f x ≡{n}≡ f y

(* Example: successor is non-expansive *)
Instance S_ne : NonExpansive S.
```

### 4. Internal Equality (`(a ≡ b)%I`)

**Equality inside the Iris logic.**

**Level:** Inside `iProp`

**Usage:**
```coq
(* In separation logic assertions *)
l ↦ v ∗ ⌜v ≡ #0⌝        (* Wrong! Use = for pure *)
l ↦ v ∗ (v ≡ #0)%I       (* Correct: internal equality *)

(* For propositions *)
(P ≡ Q)%I                (* P and Q are equal propositions *)
```

**Interpretation:** "Interpreted using OFE distance at the current step-index."

**Properties:**
- Stronger than bi-entailment for propositions
- `(a ≡ b)%I` means equality regardless of resources
- Can't be directly proven; use entailments

**Relationship to bi-entailment:**
```coq
(* For propositions *)
(P ≡ Q)%I  →  P ⊣⊢ Q    (* Internal eq implies bi-entailment *)
(* But NOT the converse! *)
```

### 5. Entailment (`P ⊢ Q`)

**Iris's implication at the metalevel.**

**Level:** Metalogic (Coq `Prop`)

**Meaning:** "For all resources and step-indices, if P holds then Q holds."

**Usage:**
```coq
(* Proving lemmas *)
Lemma my_lemma P Q :
  P ⊢ Q.
Proof.
  iIntros "HP".
  (* ... *)
Qed.

(* Not the same as magic wand! *)
P ⊢ Q    (* Metalevel entailment *)
(P -∗ Q)%I    (* Object-level wand *)
```

**Properties:**
- A Coq `Prop`, not an `iProp`
- Can be proven with proof mode tactics
- Transitive, reflexive

**Relationship to wand:**
```coq
(* Wand can be internalized *)
(P -∗ Q)%I  ⊣⊢  □(P -∗ Q)%I

(* Entailment at metalevel *)
P ⊢ Q  ↔  (True ⊢ P -∗ Q)
```

### 6. Bi-entailment (`P ⊣⊢ Q`)

**Mutual entailment: both directions hold.**

**Level:** Metalogic (Coq)

**Definition:** `P ⊣⊢ Q  :≡  (P ⊢ Q) ∧ (Q ⊢ P)`

**Usage:**
```coq
(* Proving equivalence of propositions *)
Lemma equiv_example P Q :
  P ⊣⊢ Q.
Proof.
  iSplit.
  - (* P ⊢ Q *)
  - (* Q ⊢ P *)
Qed.

(* Bi-entailment is setoid equality *)
P ≡ Q  ↔  P ⊣⊢ Q    (* For propositions *)
```

**Properties:**
- Equivalence relation
- Weaker than internal equality
- Can rewrite under bi-entailment with `iRewrite`

**Key insight:** "Q1 ≡ Q2 means that Q1 and Q2 are equivalent independently of the available resources."

### Comparison Table

| Equality | Level | Notation | Strength | Use Case |
|----------|-------|----------|----------|----------|
| Leibniz | Coq | `=` | Strongest | Coq values |
| Setoid | Coq | `≡` | Strong | Extensional equality |
| Distance | OFE | `≡{n}≡` | Indexed | Step-indexing |
| Internal | Iris | `(a ≡ b)%I` | Strong | Logic-level equality |
| Bi-entailment | Meta | `⊣⊢` | Weak | Proposition equivalence |
| Entailment | Meta | `⊢` | One-way | Implication |

### Rewriting Guidelines

**What you can rewrite:**

```coq
(* Leibniz equality in Coq context *)
rewrite H.                   (* Coq's rewrite *)

(* Setoid equality *)
setoid_rewrite H.

(* Internal equality in Iris *)
iRewrite "H".                (* Iris rewrite *)

(* Under bi-entailment *)
iRewrite equiv_lemma.
```

**Example: Different rewrites**
```coq
Lemma rewrite_example (x y : nat) :
  x = y →                    (* Leibniz *)
  ⌜x = y⌝ -∗                 (* Pure assertion *)
  (x ≡ y)%I.                 (* Internal equality *)
Proof.
  intros Heq.
  iIntros "%".
  (* Can use Heq for rewriting in Iris *)
  iPureIntro.
  apply Heq.
Qed.
```

### Common Mistakes

**Mistake 1: Using wrong equality**
```coq
(* ❌ BAD: Internal equality for pure facts *)
l ↦ v ∗ (v ≡ #0)%I

(* ✅ GOOD: Pure assertion *)
l ↦ v ∗ ⌜v = #0⌝
```

**Mistake 2: Confusing wand and entailment**
```coq
(* ❌ BAD: Using wand in lemma statement *)
Lemma bad P Q : (P -∗ Q)%I.  (* This is an iProp, not provable! *)

(* ✅ GOOD: Using entailment *)
Lemma good P Q : P ⊢ Q.      (* This is a Prop, provable *)
```

**Mistake 3: Expecting bi-entailment = internal equality**
```coq
(* These are NOT equivalent! *)
P ⊣⊢ Q    (* Weaker: equal given any resources *)
(P ≡ Q)%I (* Stronger: equal regardless of resources *)
```

---

## Proof Mode Tactics

### Introduction Patterns

**Basic patterns:**
- `"H"` - Name hypothesis H
- `"?"` - Generate fresh name
- `"_"` - Discard hypothesis
- `"%"` - Move pure fact to Coq context
- `"#"` - Move to persistent context
- `"[H1 H2]"` - Destruct conjunction
- `"[H1|H2]"` - Destruct disjunction

**Example:**
```coq
iIntros (x) "H".           (* Introduce Coq variable x and hypothesis H *)
iIntros "%".               (* Introduce pure proposition to Coq context *)
iIntros "#H".              (* Introduce persistent hypothesis *)
iIntros "[H1 H2]".         (* Destruct conjunction *)
iIntros "[H1|H2]".         (* Destruct disjunction - creates two subgoals *)
```

### Context Management

#### `iIntros` - Introduce hypotheses

**Syntax:** `iIntros (coq_vars) "ipat1 ipat2 ..."`

**Examples:**
```coq
(* Basic introduction *)
iIntros "H".                    (* Introduce spatial hypothesis H *)
iIntros "#H".                   (* Introduce persistent hypothesis H *)
iIntros (n m) "H1 H2".          (* Introduce Coq vars n, m and hypotheses H1, H2 *)

(* Pattern matching *)
iIntros "[H1 H2]".              (* Split conjunction: P ∗ Q *)
iIntros "[H1|H2]".              (* Split disjunction: P ∨ Q *)
iIntros (x) "H".                (* Introduce ∃x. P *)

(* Pure facts *)
iIntros "% H".                  (* Move pure premise to Coq context, keep H *)
iIntros (x %) "H".              (* Introduce ∃x. ⌜φ⌝ ∗ P *)
```

#### `iDestruct` - Destruct hypotheses

**Syntax:** `iDestruct "H" as "ipat"`

**Examples:**
```coq
(* Split conjunction *)
iDestruct "H" as "[H1 H2]".     (* H : P ∗ Q → H1 : P, H2 : Q *)

(* Split disjunction *)
iDestruct "H" as "[H1|H2]".     (* H : P ∨ Q → two subgoals *)

(* Extract existential *)
iDestruct "H" as (x) "H".       (* H : ∃x. P → introduces x, H : P *)

(* Extract pure *)
iDestruct "H" as %Hφ.           (* H : ⌜φ⌝ → Hφ : φ in Coq context *)
```

#### `iFrame` - Cancel matching hypotheses

**Most powerful tactic for separation logic!**

**Syntax:** `iFrame` or `iFrame "H1 H2"` or `iFrame (#)` or `iFrame (∗)`

**Examples:**
```coq
(* Automatic framing *)
(* Goal: l ↦ v ∗ P *)
(* Context: Hl : l ↦ v, HP : P *)
iFrame.                         (* Solves goal by framing both *)

(* Selective framing *)
iFrame "Hl".                    (* Goal: l ↦ v ∗ P → Goal: P *)
iFrame "Hl HP".                 (* Frame multiple hypotheses *)

(* Frame all intuitionistic *)
iFrame "#".                     (* Frames all persistent hypotheses *)

(* Frame all spatial *)
iFrame "∗".                     (* Frames all spatial hypotheses *)
```

#### `iSplit` - Split conjunctions

```coq
(* Goal: P ∗ Q *)
iSplit.                         (* Creates two subgoals: P and Q *)

(* Goal: P ∧ Q *)
iSplitL.                        (* Split, keeping spatial hyps on left *)
iSplitR.                        (* Split, keeping spatial hyps on right *)
iSplitL "H1 H2".                (* Keep H1, H2 for left subgoal *)
iSplitR "H3".                   (* Keep H3 for right subgoal *)
```

#### `iCombine` - Combine hypotheses

```coq
(* Combine separating conjunction *)
iCombine "H1 H2" as "H".        (* H1 : P, H2 : Q → H : P ∗ Q *)

(* Combine gives ownership *)
iCombine "Hl1 Hl2" as "Hl".     (* Combine heap points-to *)
```

### Applying Lemmas

#### `iApply` - Apply lemmas backward

**Syntax:** `iApply "H"` or `iApply lemma_name`

**Examples:**
```coq
(* Apply wand *)
(* Context: Hwand : P -∗ Q *)
(* Goal: Q *)
iApply "Hwand".                 (* New goal: P *)

(* Apply lemma *)
iApply wp_alloc.                (* Apply weakest precondition lemma *)
```

#### `iSpecialize` - Specialize hypotheses

**Syntax:** `iSpecialize ("H" with "H1 H2")`

**Examples:**
```coq
(* Specialize wand *)
(* Context: Hwand : P -∗ Q, HP : P *)
iSpecialize ("Hwand" with "HP"). (* Hwand : Q *)

(* Specialize with framing *)
iSpecialize ("Hwand" with "[$HP $HQ]").

(* Specialize with pure facts *)
iSpecialize ("H" $! x).         (* Instantiate ∀x. P with x *)
```

### Existentials and Pure Facts

```coq
(* Introduce existential *)
(* Goal: ∃x. P *)
iExists x.                      (* Provide witness x *)

(* Introduce pure *)
(* Goal: ⌜φ⌝ *)
iPureIntro.                     (* Move to Coq context, prove φ *)

(* Extract pure from context *)
iDestruct "H" as %Hpure.        (* H : ⌜φ⌝ → Hpure : φ *)
```

### Löb Induction

**For recursive proofs and coinductive reasoning:**

```coq
(* Goal involves recursive predicate or later *)
iLöb as "IH".                   (* Introduces induction hypothesis *)

(* Common pattern: recursive functions *)
iLöb as "IH" forall (x).        (* Generalize over x *)
```

**Example:**
```coq
Lemma wp_repeat (f : val) (n : nat) :
  {{{ True }}} repeat f #n {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  iLöb as "IH" forall (n).      (* Induction on repeat *)
  wp_rec. wp_pures.
  destruct n; wp_pures.
  - by iApply "HΦ".             (* Base case *)
  - wp_apply ("IH").            (* Inductive step *)
    iIntros "_". by iApply "HΦ".
Qed.
```

---

## HeapLang Verification

### Weakest Precondition Notation

**Basic WP:** `{{{ P }}} e {{{ v, RET v; Q }}}`

Means: "If precondition P holds, then executing expression e will return value v satisfying postcondition Q."

**With binders:** `{{{ P }}} e {{{ x y, RET v; Q }}}`

Postcondition can bind variables from the result.

### HeapLang Tactics

#### Pure Computation

**`wp_pures`** - Execute multiple pure steps

```coq
(* Automatically performs: β-reduction, let-binding, arithmetic, etc. *)
wp_pures.

(* Individual pure steps *)
wp_rec.                         (* Beta-reduce recursive function *)
wp_lam.                         (* Beta-reduce lambda *)
wp_let.                         (* Reduce let-binding *)
wp_if.                          (* Reduce if-then-else *)
wp_case.                        (* Pattern matching *)
```

#### Heap Operations

**`wp_alloc`** - Allocate memory

```coq
(* Goal: WP (ref v) {{ Φ }} *)
wp_alloc l as "Hl".            (* Introduces l ↦ v as "Hl" *)
```

**`wp_load`** - Load from memory

```coq
(* Context: Hl : l ↦ v *)
(* Goal: WP (!#l) {{ Φ }} *)
wp_load.                       (* Reduce to WP v {{ Φ }}, keeps Hl *)
```

**`wp_store`** - Store to memory

```coq
(* Context: Hl : l ↦ v *)
(* Goal: WP (#l <- w) {{ Φ }} *)
wp_store.                      (* Updates Hl to l ↦ w *)
```

**`wp_cmpxchg_suc`/`wp_cmpxchg_fail`** - Compare-and-exchange

```coq
(* Context: Hl : l ↦ v *)
(* Goal: WP (CmpXchg #l v w) {{ Φ }} *)
wp_cmpxchg_suc.               (* Success: updates to l ↦ w *)
(* or *)
wp_cmpxchg_fail.              (* Failure: keeps l ↦ v *)
```

**`wp_faa`** - Fetch-and-add

```coq
(* Context: Hl : l ↦ #n *)
(* Goal: WP (FAA #l #m) {{ Φ }} *)
wp_faa.                       (* Updates Hl to l ↦ #(n+m) *)
```

#### Advanced WP Tactics

**`wp_bind`** - Focus on subexpression

**Critical for opening invariants!**

```coq
(* Goal: WP (e1 + e2) {{ Φ }} *)
wp_bind (e1 + _)%E.           (* Focus on e1, defer e2 *)
(* Now can open invariants for e1 *)
```

**`wp_apply`** - Apply specification lemma

```coq
(* Apply a specification *)
wp_apply (spec_func with "Hpre").
iIntros (v) "Hpost".          (* Handle postcondition *)
```

**`wp_smart_apply`** - Apply with automatic binding

```coq
wp_smart_apply spec_func.     (* Automatically handles wp_bind *)
```

### HeapLang Notation

**Scopes:**
- `%E` - Expression scope
- `%V` - Value scope

**Common constructs:**
```coq
#n                            (* Integer literal *)
#true, #false                 (* Boolean literals *)
#()                           (* Unit value *)
#l                            (* Location literal *)

(e1 + e2)%E                   (* Addition *)
(if: e then e1 else e2)%E     (* Conditional *)
(rec: f x := e)%E             (* Recursive function *)
(λ: x, e)%V                   (* Lambda value *)
(ref e)%E                     (* Allocation *)
(!#l)%E                       (* Dereference *)
(#l <- e)%E                   (* Assignment *)
(Fork e)%E                    (* Thread spawn *)
```

---

## Common Patterns

### Pattern 1: Basic Memory Reasoning

**Allocate, store, load:**

```coq
Lemma example_alloc_store_load :
  {{{ True }}}
    let: "l" := ref #0 in
    "l" <- #42 ;;
    !"l"
  {{{ RET #42; True }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_alloc l as "Hl".          (* l ↦ #0 *)
  wp_pures.
  wp_store.                    (* l ↦ #42 *)
  wp_load.                     (* Load 42 *)
  by iApply "HΦ".
Qed.
```

### Pattern 2: Framing Resources

**Use `iFrame` to discharge separating conjunctions:**

```coq
Lemma framing_example (l : loc) (v : val) :
  l ↦ v -∗ l ↦ v ∗ ⌜v = #0⌝ ∨ ⌜v ≠ #0⌝.
Proof.
  iIntros "Hl".
  iFrame "Hl".                 (* Frames l ↦ v *)
  (* Goal: ⌜v = #0⌝ ∨ ⌜v ≠ #0⌝ *)
  destruct (decide (v = #0)); auto.
Qed.
```

### Pattern 3: Using Wands

**Magic wands consume resources:**

```coq
Lemma wand_example P Q :
  P -∗ (P -∗ Q) -∗ Q.
Proof.
  iIntros "HP Hwand".
  iApply ("Hwand" with "HP"). (* Apply wand with resource *)
Qed.
```

### Pattern 4: Persistent Facts

**Mark persistent hypotheses with `#`:**

```coq
Lemma persistent_example (P : iProp Σ) `{!Persistent P} :
  P -∗ P ∗ P.
Proof.
  iIntros "#HP".              (* Mark as persistent *)
  iSplit; iFrame "#".         (* Can use multiple times *)
Qed.
```

### Pattern 5: Combining and Splitting

```coq
Lemma combine_split (P Q R : iProp Σ) :
  P -∗ Q -∗ R -∗ (P ∗ Q) ∗ R.
Proof.
  iIntros "HP HQ HR".
  iSplitL "HP HQ".            (* Split, keep HP HQ for left *)
  - iFrame.                   (* Frames P ∗ Q *)
  - iFrame.                   (* Frames R *)
Qed.
```

---

## Handling Modalities

### Update Modality `|==> P`

**Eliminate with `iMod`:**

```coq
Lemma mod_intro P :
  P -∗ |==> P.
Proof.
  iIntros "HP".
  iModIntro.                  (* Introduce update modality *)
  iFrame.
Qed.

Lemma mod_elim P Q :
  (|==> P) -∗ (P -∗ |==> Q) -∗ |==> Q.
Proof.
  iIntros "HP Hwand".
  iMod "HP".                  (* Eliminate update modality *)
  iApply "Hwand".
  iFrame.
Qed.
```

### Fancy Update `|={E1,E2}=> P`

**Handles mask management for invariants:**

```coq
(* Weakening masks *)
Lemma fupd_weaken E1 E2 P :
  E2 ⊆ E1 →
  (|={E2}=> P) -∗ |={E1}=> P.
Proof.
  iIntros (HE) "HP".
  iMod (fupd_mask_subseteq E2) as "Hclose".
  - apply HE.
  iMod "HP".
  iMod "Hclose" as "_".
  by iModIntro.
Qed.
```

**Common pattern: mask mismatch**

**Problem:** Goal has `|={E,_}=>` but need to apply lemma with `|={E',_}=>` where `E' ⊆ E`.

**Solution:**
```coq
(* Weaken mask before applying *)
iMod (fupd_mask_subseteq E') as "Hclose".
(* Apply lemma *)
iMod "Hclose" as "_".
```

### Later Modality `▷ P`

**Eliminate with `iNext`:**

```coq
Lemma later_example P :
  ▷ P -∗ ▷ P.
Proof.
  iIntros "HP".
  iNext.                      (* Strip ▷ from context and goal *)
  iFrame.
Qed.
```

**Common with Löb induction:**
```coq
iLöb as "IH".                 (* IH : ▷ goal *)
iNext.                        (* Strip ▷ to use IH *)
```

---

## Invariant Management

### Opening Invariants

**Basic pattern:**

```coq
iInv "N" as (x) "[HP Hclose]".
(* Invariant opened: use HP *)
(* Must close before returning: use Hclose *)
iMod ("Hclose" with "HP").
```

**With `wp_bind` for atomic operations:**

```coq
(* Goal: WP (e1 + e2) {{ Φ }} where e1 needs invariant *)
wp_bind (e1)%E.               (* Focus on e1 *)
iInv "N" as (x) "HP".         (* Open invariant *)
(* Verify e1 is atomic *)
wp_load.                      (* Atomic operation *)
iModIntro.                    (* Close invariant *)
iSplitL "HP".                 (* Restore invariant *)
{ (* Show invariant restored */ }
(* Continue with e2 *)
```

### Allocating Invariants

```coq
iMod (inv_alloc N _ P with "HP") as "#Hinv".
```

**Naming convention:** Invariant namespaces use `nroot .@ "name"`.

---

## Style Guide

### Formatting

**Spacing:**
```coq
(* ✅ GOOD: Spaces around colons in binders *)
forall (x : nat) (l : loc), ...

(* ❌ BAD: No spaces *)
forall (x:nat) (l:loc), ...
```

**Unicode:**
```coq
(* ✅ GOOD: Use Unicode *)
∀ x, x ≤ y → P x

(* ❌ BAD: ASCII *)
forall x, x <= y -> P x
```

**Proof structure:**
```coq
(* ✅ GOOD: Short proofs on one line *)
Proof. reflexivity. Qed.

(* ✅ GOOD: Multi-line with 2-space indent *)
Proof.
  iIntros "H".
  iApply "H".
Qed.
```

### Naming Conventions

**Variables:**
- Lowercase letters: values, expressions, states (`e`, `v`, `σ`)
- Capital letters: types, sets, propositions (`P`, `Q`, `E`)
- Greek letters: mathematical objects (`γ` for ghost names, `Φ` for postconditions)

**Hypotheses:**
```coq
"Hl"                          (* Heap points-to: l ↦ v *)
"Hinv"                        (* Invariant *)
"HP", "HQ"                    (* Propositions P, Q *)
"Hφ"                          (* Pure fact φ *)
"IH"                          (* Induction hypothesis *)
"HΦ"                          (* Postcondition *)
```

**Lemma names:**
```coq
wp_alloc                      (* WP lemma for alloc *)
spec_function_name            (* Specification *)
function_name_spec            (* Alternative *)
_ctx                          (* Persistent facts *)
_interp                       (* Interpretation functions *)
```

### Tactic Style

**Pattern matching:**
```coq
(* ✅ GOOD: Always mark disjuncts *)
iIntros "[H1|H2]".

(* ❌ BAD: Unmarked disjunct *)
iIntros "[H1|]".              (* Shows which branch is which *)
```

**Selective framing:**
```coq
(* ✅ GOOD: Explicit about what stays *)
iSplitL "H1 H2".
- (* Left goal gets H1, H2 *)
- (* Right goal gets rest *)

(* Or use iSplitR for right *)
iSplitR "H3".
```

**Type class assumptions:**
```coq
(* ✅ GOOD: Order matters *)
Context `{!heapGS Σ}.         (* subG assumption implicit *)

(* ❌ BAD: Wrong order can cause search divergence *)
```

---

## Common Pitfalls

### 1. Forgetting to Mark Persistent Hypotheses

**Problem:**
```coq
iIntros "HP".                 (* Spatial hypothesis *)
iSplit.
- iFrame "HP".                (* Consumes HP *)
- iFrame "HP".                (* ERROR: HP already consumed *)
```

**Solution:**
```coq
iIntros "#HP".                (* Persistent hypothesis *)
iSplit; iFrame "#".           (* Can use multiple times *)
```

### 2. Mask Mismatches

**Problem:**
```coq
(* Goal: |={E}=> P *)
(* Lemma: |={E'}=> P where E' ⊂ E *)
iMod lemma.                   (* ERROR: Mask mismatch *)
```

**Solution:**
```coq
iMod (fupd_mask_subseteq E') as "Hclose".
iMod lemma.
iMod "Hclose" as "_".
```

### 3. Forgetting `wp_bind` for Invariants

**Problem:**
```coq
(* Goal: WP (e1 + e2) {{ Φ }} *)
iInv "N".                     (* ERROR: e1 + e2 not atomic *)
```

**Solution:**
```coq
wp_bind (e1)%E.               (* Focus on atomic e1 *)
iInv "N".                     (* Now can open *)
```

### 4. Not Closing Invariants

**Problem:**
```coq
iInv "N" as "HP".
wp_load.
(* ERROR: Forgot to close invariant *)
```

**Solution:**
```coq
iInv "N" as (x) "[HP Hclose]".
wp_load.
iMod ("Hclose" with "HP").   (* Close invariant *)
iModIntro.
```

### 5. Using Consumed Resources

**Problem:**
```coq
iIntros "HP HQ".
iApply ("HP" with "HQ").      (* Consumes HQ *)
iFrame "HQ".                  (* ERROR: HQ already used *)
```

**Solution:** Track what each tactic consumes. Use `iFrame` before consuming, or duplicate persistent hypotheses.

### 6. Wrong Scope for Löb Induction

**Problem:**
```coq
iIntros (n) "HP".
wp_pures.
iLöb as "IH".                 (* ERROR: n not generalized *)
```

**Solution:**
```coq
iIntros (n) "HP".
iLöb as "IH" forall (n).      (* Generalize n *)
wp_pures.
```

---

## Complete Examples

### Example 1: Counter with Lock

```coq
Definition counter_inv (γ : gname) (l : loc) : iProp Σ :=
  ∃ (n : nat), l ↦ #n ∗ own γ (●E n).

Lemma wp_counter_incr γ l :
  {{{ inv counterN (counter_inv γ l) ∗ own γ (◯E 1) }}}
    FAA #l #1
  {{{ (n : nat), RET #n; own γ (◯E 1) }}}.
Proof.
  iIntros (Φ) "[#Hinv Hγ] HΦ".
  wp_bind (FAA _ _)%E.        (* Atomic operation *)
  iInv counterN as (n) "[>Hl Hγ_auth]".
  wp_faa.                     (* Fetch-and-add *)

  (* Update ghost state *)
  iMod (own_update_2 with "Hγ_auth Hγ") as "[Hγ_auth Hγ]".
  { apply auth_update_alloc, (op_local_update_discrete _ _ 1). }

  iModIntro.
  iSplitL "Hl Hγ_auth".
  { (* Restore invariant *)
    iNext. iExists (n + 1).
    replace (n + 1)%nat with (S n) by lia.
    iFrame.
  }
  by iApply "HΦ".
Qed.
```

### Example 2: Recursive List Sum

```coq
Fixpoint is_list (hd : val) (xs : list nat) : iProp Σ :=
  match xs with
  | [] => ⌜hd = NONEV⌝
  | x :: xs' => ∃ (l : loc) (tl : val),
      ⌜hd = SOMEV #l⌝ ∗ l ↦ (#x, tl) ∗ is_list tl xs'
  end.

Lemma wp_sum (hd : val) (xs : list nat) :
  {{{ is_list hd xs }}}
    sum hd
  {{{ RET #(sum_list xs); is_list hd xs }}}.
Proof.
  iIntros (Φ) "Hlist HΦ".
  iLöb as "IH" forall (hd xs).  (* Induction on list *)
  wp_rec. wp_pures.

  destruct xs as [|x xs'].
  - (* Base case: empty list *)
    iDestruct "Hlist" as %->.
    wp_pures. by iApply "HΦ".

  - (* Inductive case: x :: xs' *)
    iDestruct "Hlist" as (l tl ->) "[Hl Htail]".
    wp_pures.
    wp_load.                  (* Load (x, tl) *)
    wp_pures.

    (* Recursive call *)
    wp_apply ("IH" with "Htail").
    iIntros "Htail".
    wp_pures.

    iApply "HΦ".
    iExists l, tl.
    by iFrame.
Qed.
```

### Example 3: Parallel Increment

```coq
Lemma wp_par_incr (l : loc) (v : Z) :
  {{{ l ↦ #v }}}
    (#l <- #(v + 1)) ||| (#l <- #(v + 1))
  {{{ RET (#(), #()); ∃ v', l ↦ #v' ∗ ⌜v < v' ≤ v + 2⌝ }}}.
Proof.
  iIntros (Φ) "Hl HΦ".

  (* Need invariant for concurrent access *)
  iMod (inv_alloc parN _ (∃ v', l ↦ #v' ∗ ⌜v ≤ v'⌝)%I
         with "[Hl]") as "#Hinv".
  { iNext. iExists v. iFrame. by iPureIntro. }

  (* Fork *)
  wp_apply (wp_par with "[HΦ] []").

  - (* Thread 1 *)
    wp_bind (#l <- _)%E.
    iInv parN as (v1) "[>Hl %Hv1]".
    wp_store.
    iModIntro.
    iSplitL "Hl".
    { iNext. iExists (v1 + 1). iFrame. iPureIntro. lia. }
    done.

  - (* Thread 2 - similar *)
    wp_bind (#l <- _)%E.
    iInv parN as (v2) "[>Hl %Hv2]".
    wp_store.
    iModIntro.
    iSplitL "Hl".
    { iNext. iExists (v2 + 1). iFrame. iPureIntro. lia. }
    done.

  - (* Join *)
    iIntros (? ?) "[_ _]".
    iInv parN as (v') "[Hl %Hv']".
    iModIntro.
    iApply "HΦ".
    iExists v'. iFrame.
    iPureIntro. lia.
Qed.
```

---

## Quick Reference Card

### Essential Tactics

| Tactic | Purpose | Example |
|--------|---------|---------|
| `iIntros "H"` | Introduce hypothesis | `iIntros (x) "#H"` |
| `iDestruct "H" as "ipat"` | Destruct hypothesis | `iDestruct "H" as "[H1 H2]"` |
| `iFrame` | Cancel matching resources | `iFrame "Hl HP"` |
| `iSplitL "H1"` | Split, keep H1 left | `iSplitL "H1 H2"` |
| `iApply "H"` | Apply wand/lemma | `iApply ("H" with "HP")` |
| `iSpecialize` | Specialize hypothesis | `iSpecialize ("H" with "HP")` |
| `iExists x` | Introduce existential | `iExists 42` |
| `iPureIntro` | Move pure goal to Coq | `iPureIntro; lia` |
| `iMod "H"` | Eliminate modality | `iMod "H" as "HP"` |
| `iModIntro` | Introduce modality | `iModIntro; iFrame` |
| `iNext` | Handle later | `iNext; iFrame` |
| `iLöb as "IH"` | Löb induction | `iLöb as "IH" forall (n)` |
| `iInv "N"` | Open invariant | `iInv "N" as "HP"` |

### HeapLang WP Tactics

| Tactic | Purpose | Result |
|--------|---------|--------|
| `wp_pures` | Execute pure steps | Multiple reductions |
| `wp_alloc l as "Hl"` | Allocate | `Hl : l ↦ v` |
| `wp_load` | Load | Keeps points-to |
| `wp_store` | Store | Updates points-to |
| `wp_cmpxchg_suc` | CAS success | Updates points-to |
| `wp_faa` | Fetch-and-add | Updates points-to |
| `wp_bind (e)%E` | Focus subexpr | For invariants |
| `wp_apply spec` | Apply spec lemma | With binding |

### Introduction Patterns

| Pattern | Meaning | Example |
|---------|---------|---------|
| `"H"` | Name hypothesis H | `iIntros "H"` |
| `"#H"` | Persistent H | `iIntros "#H"` |
| `"%"` | Pure to Coq | `iIntros "%"` |
| `"_"` | Discard | `iIntros "_"` |
| `"[H1 H2]"` | Split conjunction | `iIntros "[H1 H2]"` |
| `"[H1\|H2]"` | Split disjunction | `iIntros "[H1\|H2]"` |
| `(x)` | Intro Coq var | `iIntros (x)` |

---

## Further Resources

**Official Documentation:**
- [Iris Project](https://iris-project.org/)
- [Iris Tutorial](https://iris-project.org/tutorial-material.html)
- [HeapLang Documentation](https://gitlab.mpi-sws.org/iris/iris/-/blob/master/docs/heap_lang.md)

**Papers:**
- "Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning" (POPL 2015)
- "Iris from the Ground Up" (JFP 2018)

**Examples:**
- Iris examples directory: `iris/tests` and `iris-examples`
- Case studies in concurrent separation logic

---

**Remember:**
1. Use `iFrame` liberally - it's your best friend
2. Mark persistent hypotheses with `#`
3. Always `wp_bind` before opening invariants
4. Track resource ownership carefully
5. Use `iLöb` for recursive proofs
6. Handle masks explicitly with `fupd_mask_subseteq`
