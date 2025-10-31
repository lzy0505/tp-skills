# Admit Filling: Completing Incomplete Proofs

## Overview

This guide provides systematic strategies for completing proofs marked with `admit`, `admit.`, or `Admitted`.

**Core principle:** Search first, prove second. Most results exist in stdlib or MathComp.

**Success rate:** 60-90% of admits can be filled by finding existing lemmas. Remaining 10-40% require actual proof work.

---

## Table of Contents

1. [Understanding Admits](#understanding-admits)
2. [The 4-Phase Filling Strategy](#the-4-phase-filling-strategy)
3. [Search Strategies](#search-strategies)
4. [Common Admit Patterns](#common-admit-patterns)
5. [Domain-Specific Tactics](#domain-specific-tactics)
6. [When Admits Are Acceptable](#when-admits-are-acceptable)
7. [Tooling and Automation](#tooling-and-automation)

---

## Understanding Admits

### Types of Admits in Rocq/Coq

**1. Tactic Mode Admit**
```coq
Lemma example : P.
Proof.
  intros.
  admit.  (* Incomplete tactic proof *)
Qed.
```
- Used within proof
- Leaves subgoal unproven
- File still compiles
- Goal: replace with actual tactics

**2. Admitted Theorem**
```coq
Lemma example : P.
Proof.
  intros.
  (* partial proof *)
Admitted.  (* Instead of Qed *)
```
- Entire proof incomplete
- Declared but not proven
- Can be used in other proofs (dangerous!)
- Goal: complete proof and change to `Qed` or `Defined`

**3. Axiom (Worst Case)**
```coq
Axiom example : P.  (* No proof at all *)
```
- No proof whatsoever
- Should be avoided unless fundamental
- Goal: eliminate or prove

### Admit vs Axiom

|  | `admit`/`Admitted` | `Axiom` |
|--|-------------------|---------|
| Has proof structure? | Partial | None |
| Shows in `Print Assumptions` | Yes | Yes |
| Can be completed | Yes | Must reprove |
| Acceptable? | Temporarily | Rarely |

---

## The 4-Phase Filling Strategy

### Phase 1: Search for Existing Lemmas (60-90% success)

**Before proving anything, search thoroughly.**

```coq
(* Goal: n + 0 = n *)

(* Try pattern search *)
SearchPattern (_ + 0 = _).
(* Found: Nat.add_0_r : forall n : nat, n + 0 = n *)

(* Apply it *)
apply Nat.add_0_r.  (* Done! *)
```

**Search commands:**
```coq
Search "substring".           (* By name *)
SearchAbout nat.              (* About type *)
SearchPattern (_ + _ = _).    (* By pattern *)
Search nat "comm".            (* Combine *)
```

**Hit rate:** 60-90% for standard results

### Phase 2: Try Automation (20-30% of remaining)

**Decision procedures often solve goals directly.**

```coq
(* Linear arithmetic *)
Lemma auto_example n m : n < m -> n + 1 <= m.
Proof.
  intro H.
  admit.  (* Before *)
Admitted.

(* After - try lia *)
Lemma auto_example n m : n < m -> n + 1 <= m.
Proof.
  intro H.
  lia.  (* Solves automatically! *)
Qed.
```

**Try these tactics:**
- `lia` - linear integer arithmetic
- `ring` - ring equations
- `field` - field equations
- `congruence` - equality reasoning
- `easy` / `auto` - simple goals
- `tauto` / `firstorder` - propositional logic

### Phase 3: Decompose and Recurse (60-80% of remaining)

**Break goal into simpler subgoals.**

```coq
Lemma example n : exists m, m > n.
Proof.
  admit.  (* Stuck *)
Admitted.

(* After - decompose *)
Lemma example n : exists m, m > n.
Proof.
  exists (S n).     (* Provide witness *)
  (* Goal now: S n > n *)
  apply Nat.lt_succ_diag_r.  (* Search found it *)
Qed.
```

**Decomposition tactics:**
- `exists t` - provide witness
- `split` - split conjunction/iff
- `left` / `right` - choose disjunct
- `intros` - introduce assumptions
- `destruct` / `case` - case analysis
- `induction` / `elim` - induction

### Phase 4: Actual Proof Work (10-20% of remaining)

**When nothing else works, prove it.**

```coq
Lemma custom : forall n, my_predicate n.
Proof.
  (* No existing lemma found *)
  (* Automation doesn't work *)
  (* Time to prove it *)
  induction n as [| n' IHn'].
  - (* Base case *)
    (* Prove for 0 *)
  - (* Inductive case *)
    (* Use IHn' to prove for S n' *)
Qed.
```

---

## Search Strategies

### Strategy 1: Pattern Search

**Most effective for finding existing results.**

```coq
(* Want to prove: forall n m, n + m = m + n *)

(* Search by pattern *)
SearchPattern (_ + _ = _ + _).
(* Finds: Nat.add_comm, Z.add_comm, etc. *)

(* Refine search *)
SearchPattern (nat -> nat -> _).
Search "comm" "add".
```

### Strategy 2: Type-Directed Search

**Search by what you're working with.**

```coq
(* Working with lists *)
SearchAbout list.
Search list "map".
SearchPattern (map _ (_ ++ _)).

(* Working with nat *)
SearchAbout nat.
Search nat inside Coq.Arith.
```

### Strategy 3: Conclusion Search

**Search by what you want to prove.**

```coq
(* Want to conclude: _ <= _ *)
SearchHead le.

(* Want equality *)
SearchHead eq.

(* Want rewrite pattern *)
SearchRewrite (_ + 0).
```

### Strategy 4: Module Exploration

**Know where things live.**

```coq
(* Lists *)
Require Import Coq.Lists.List.
Search list inside Coq.Lists.

(* Arithmetic *)
Require Import Coq.Arith.Arith.
Search nat inside Coq.Arith.

(* MathComp *)
From mathcomp Require Import all_ssreflect.
Search _ inside seq.
```

---

## Common Admit Patterns

### Pattern 1: Trivial by Existing Lemma

```coq
(* Before *)
Lemma example : forall l, l ++ [] = l.
Proof.
  intro l.
  admit.
Admitted.

(* After - search found it *)
Lemma example : forall l, l ++ [] = l.
Proof.
  intro l.
  apply app_nil_r.  (* From Coq.Lists.List *)
Qed.
```

**Fix:** Search → Apply

### Pattern 2: Solvable by Automation

```coq
(* Before *)
Lemma example : forall n m k, n + (m + k) = (n + m) + k.
Proof.
  intros.
  admit.
Admitted.

(* After - ring solves it *)
Require Import Ring.
Lemma example : forall n m k, n + (m + k) = (n + m) + k.
Proof.
  intros.
  ring.
Qed.
```

**Fix:** Try automation tactics

### Pattern 3: Missing Witness

```coq
(* Before *)
Lemma example : exists n, n > 5.
Proof.
  admit.
Admitted.

(* After - provide witness *)
Lemma example : exists n, n > 5.
Proof.
  exists 6.
  lia.
Qed.
```

**Fix:** Provide existential witness

### Pattern 4: Need Case Analysis

```coq
(* Before *)
Lemma example : forall n, n = 0 \/ n > 0.
Proof.
  intro n.
  admit.
Admitted.

(* After - case analysis *)
Lemma example : forall n, n = 0 \/ n > 0.
Proof.
  intro n.
  destruct n as [| n'].
  - left. reflexivity.
  - right. apply Nat.lt_0_succ.
Qed.
```

**Fix:** Destruct on key variable

### Pattern 5: Needs Induction

```coq
(* Before *)
Lemma example : forall n, n + 0 = n.
Proof.
  intro n.
  admit.  (* Can't solve without induction *)
Admitted.

(* After - induction *)
Lemma example : forall n, n + 0 = n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.
```

**Fix:** Induction on appropriate variable

### Pattern 6: Wrong Approach

```coq
(* Before - trying to prove impossible direction *)
Lemma wrong : forall n m, n + m = 0 -> n = 0.
Proof.
  intros n m H.
  (* Stuck because also need m = 0 *)
  admit.
Admitted.

(* After - fix statement *)
Lemma right : forall n m, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  destruct n, m; try discriminate.
  split; reflexivity.
Qed.
```

**Fix:** Reconsider problem statement

---

## Domain-Specific Tactics

### For Arithmetic Goals

```coq
(* Try in order *)
lia.        (* Linear integer arithmetic *)
ring.       (* Ring equations *)
field.      (* Field equations, handles division *)
nia.        (* Nonlinear integer arithmetic *)
```

### For List Goals

```coq
(* Common patterns *)
simpl.                  (* Reduce cons/nil *)
rewrite app_assoc.      (* Associativity *)
rewrite app_nil_r.      (* Right identity *)
rewrite map_map.        (* Map fusion *)
rewrite in_app_iff.     (* Membership in append *)
induction l.            (* Induction on list *)
```

### For Boolean Goals

```coq
(* Computation *)
compute.
vm_compute.

(* Reflection (MathComp) *)
From mathcomp Require Import ssrbool.
move/eqP.       (* bool eq to Prop eq *)
apply/andP.     (* split and *)
```

### For Equality Goals

```coq
reflexivity.     (* Definitional equality *)
f_equal.         (* Congruence *)
congruence.      (* Decision procedure *)
ring.            (* Ring equality *)
```

### For Logical Goals

```coq
tauto.           (* Propositional tautology *)
firstorder.      (* First-order logic *)
intuition.       (* Intuitionistic *)
easy.            (* Simple goals *)
```

---

## When Admits Are Acceptable

### Acceptable (Temporary)

**1. Active development**
```coq
(* STRATEGY: Prove helper_lemma_1 first, then use here *)
Lemma main_theorem : P.
Proof.
  (* Will use helper_lemma_1 when complete *)
  admit.
Admitted.
```
- Clear strategy documented
- Dependencies identified
- Plan for elimination

**2. Scaffolding**
```coq
(* TODO: This should follow from general_result once proven *)
Lemma special_case : forall n, P n.
Proof. admit. Admitted.

Lemma general_result : forall n m, P n /\ Q m.
Proof. (* Main proof here *) Qed.

(* Now can eliminate special_case *)
Lemma special_case : forall n, P n.
Proof. intro. apply general_result. Qed.
```

**3. Placeholder for refactoring**
```coq
(* Old proof broken by refactoring, will fix *)
Lemma needs_update : old_statement.
Proof. admit. Admitted.  (* TODO: Update for new definitions *)
```

### Never Acceptable

**1. "Should be in library"**
```coq
(* ❌ BAD *)
Lemma obvious : n + m = m + n.
Proof. admit. Admitted.  (* "Obviously in stdlib" - but where? *)

(* ✅ GOOD - actually find it *)
Lemma obvious : n + m = m + n.
Proof. apply Nat.add_comm. Qed.
```

**2. "Will prove later" without plan**
```coq
(* ❌ BAD *)
Lemma vague : complicated_property.
Proof. admit. Admitted.  (* No plan! *)

(* ✅ GOOD *)
Lemma vague : complicated_property.
(* STRATEGY:
   1. Prove by induction on n
   2. Base case: use base_lemma
   3. Step case: needs intermediate_result (prove separately)
   Dependencies: base_lemma (exists), intermediate_result (TODO)
*)
Proof. admit. Admitted.
```

**3. Hiding incomplete work**
```coq
(* ❌ BAD *)
Lemma incomplete : final_result.
Proof.
  (* 50 lines of partial proof *)
  admit.  (* Stuck but claiming "done" *)
Admitted.

(* ✅ GOOD *)
Lemma step1 : intermediate_result1.
Proof. (* ... *) Qed.

Lemma step2 : intermediate_result2.
Proof. admit. Admitted.  (* Clearly incomplete *)

Lemma final_result : final_result.
Proof.
  apply step1, step2.  (* Shows dependencies *)
Qed.
```

---

## Systematic Filling Workflow

### Step 1: Inventory

```coq
(* Find all admits in file *)
$ grep -n "admit\|Admitted" file.v

(* List them with context *)
Lemma foo : P.
Proof. admit. Admitted.          (* Line 42 *)

Lemma bar : Q.
Proof. intros. admit. Qed.       (* Line 87 *)
```

### Step 2: Prioritize

**Priority order:**
1. ⭐⭐⭐⭐⭐ Lemmas with `admit` as only tactic (likely findable)
2. ⭐⭐⭐⭐ Small admits in otherwise complete proofs
3. ⭐⭐⭐ Admits blocking other proofs
4. ⭐⭐ Large incomplete proofs
5. ⭐ Fundamental axioms (may need to stay)

### Step 3: Attack Each Admit

For each admit:
1. **Read goal carefully** - What exactly needs proving?
2. **Search** - Does it exist already?
3. **Try automation** - Can tactics solve it?
4. **Decompose** - Can you break it down?
5. **Prove** - If all else fails, prove it

### Step 4: Verify

```bash
# After each fill
dune build  # or: coqc file.v

# Verify admit count decreasing
grep -c "admit\|Admitted" file.v

# Check assumptions
Print Assumptions theorem_name.
# Goal: "Closed under the global context"
```

### Step 5: Commit

```bash
# Commit each filled admit separately
git add file.v
git commit -m "proof: complete lemma foo using stdlib result"

# Or batch if many trivial fills
git commit -m "proof: fill 5 admits with stdlib lemmas"
```

---

## Tooling and Automation

### Manual Verification

```coq
(* After removing admit, check it compiles *)
Lemma foo : P.
Proof.
  (* filled proof *)
Qed.

(* Verify no axioms *)
Print Assumptions foo.
(* Should show: "Closed under the global context" *)
```

### Search Scripts

```bash
# Find all admits
grep -rn "admit" --include="*.v" .

# Find admitted theorems
grep -rn "Admitted\." --include="*.v" .

# Count admits per file
for f in *.v; do
  echo "$f: $(grep -c 'admit' $f)"
done
```

### Progress Tracking

```bash
# Before filling session
BEFORE=$(grep -c "admit\|Admitted" file.v)

# After session
AFTER=$(grep -c "admit\|Admitted" file.v)

# Calculate reduction
echo "Filled: $((BEFORE - AFTER)) admits"
```

---

## Decision Tree: Filling Strategy

```
Look at admit
├─ Goal is trivial (=, <=, arithmetic)?
│  ├─ Try automation (lia, ring, auto, easy)
│  └─ If fails, search
│
├─ Goal mentions standard types (list, nat, bool)?
│  ├─ Search stdlib first
│  └─ Check MathComp if using SSReflect
│
├─ Goal is existential?
│  ├─ Can you guess witness?
│  │  ├─ Yes → provide it, recurse on subgoal
│  │  └─ No → destruct/induction to find pattern
│
├─ Goal is disjunction?
│  └─ Try case analysis (destruct key variable)
│
├─ Goal is universal?
│  └─ Need induction? Or just intro + recurse?
│
└─ Complex goal?
   ├─ Break into lemmas
   ├─ Prove each separately
   └─ Combine
```

---

## Common Mistakes

### Mistake 1: Not Searching Thoroughly

```coq
(* ❌ BAD *)
Lemma add_comm : forall n m, n + m = m + n.
Proof.
  (* Tries to prove by induction *)
  induction n; admit.  (* Gets stuck *)
Admitted.

(* ✅ GOOD *)
SearchPattern (_ + _ = _ + _).
(* Found: Nat.add_comm *)
Lemma add_comm : forall n m, n + m = m + n.
Proof. exact Nat.add_comm. Qed.
```

### Mistake 2: Using Wrong Automation

```coq
(* ❌ BAD *)
Lemma example : forall n, n + 1 > n.
Proof.
  intro n.
  ring.  (* Wrong! ring is for equations *)
Admitted.

(* ✅ GOOD *)
Lemma example : forall n, n + 1 > n.
Proof.
  intro n.
  lia.  (* lia handles inequalities *)
Qed.
```

### Mistake 3: Not Decomposing

```coq
(* ❌ BAD *)
Lemma example : forall n m, P n /\ Q m.
Proof.
  intros.
  admit.  (* Stuck on conjunction *)
Admitted.

(* ✅ GOOD *)
Lemma example : forall n m, P n /\ Q m.
Proof.
  intros n m.
  split.
  - (* Prove P n *) admit.
  - (* Prove Q m *) admit.
Admitted.
(* Now two smaller admits to fill *)
```

---

## See Also

- [stdlib-guide.md](stdlib-guide.md) - Finding existing lemmas
- [tactics-reference.md](tactics-reference.md) - All tactics for filling
- [domain-patterns.md](domain-patterns.md) - Domain-specific strategies
- [axiom-elimination.md](axiom-elimination.md) - Eliminating axioms
- [compilation-errors.md](compilation-errors.md) - Fixing broken proofs

---

**Philosophy:** Every admit is an opportunity to learn. Either you discover a useful library lemma, learn a new automation tactic, or genuinely understand the mathematics by proving it yourself. Embrace the process!
