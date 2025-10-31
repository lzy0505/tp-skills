---
description: Guided workflow for filling a Rocq/Coq admit with tactics and lemma search
allowed-tools: Bash(bash:*)
---

# Guided Admit Filling

Interactive workflow for filling incomplete proofs (admits) using stdlib/MathComp search, tactic suggestions, and multi-candidate testing.

## Workflow

### 1. Locate Admit

**If admit not specified:**
```
Which admit would you like to fill?

Options:
1. Current cursor position (if in .v file)
2. Show all admits in current file
3. Specify file and line number

Choose: (1/2/3)
```

**If user specifies location:**
```
Reading admit at [file]:[line]...
```

### 2. Understand Context

**Extract proof context:**

a) **Read surrounding code:**
```coq
(* Context around [file]:[line] *)

Lemma [lemma_name] [parameters] : [goal_type].
Proof.
  [previous tactics...]
  admit.  (* ← We're filling this *)
  [following tactics if any...]
```

b) **Identify goal structure:**
```
Analyzing admit...

Goal type: [goal_type]
Category: [equality/forall/exists/implication/conjunction/etc]
Complexity: [simple/medium/complex]
```

c) **If using coq-lsp, check goal state:**
```
Current goal state (from LSP or Show.):
  ⊢ [actual goal]

Hypotheses available:
  H1 : [type]
  H2 : [type]
  ...
```

### 3. Suggest Tactics

**Based on goal structure:**

a) **Present suggestions:**
```
Suggested tactics for this goal:

Primary approach: [main tactic]
Reason: [why this tactic fits]

Alternatives:
1. [alternative_tactic_1] - [when to use]
2. [alternative_tactic_2] - [when to use]
3. [alternative_tactic_3] - [when to use]

Recommended starting point:
[suggested initial tactic sequence]
```

**Common patterns:**

| Goal Pattern | Suggested Tactics (Standard Coq) | Suggested Tactics (SSReflect) | Reason |
|--------------|----------------------------------|-------------------------------|---------|
| `⊢ a = b` | `reflexivity`, `ring`, `field` | `by []`, `by apply: lemma` | Equality goals |
| `⊢ ∀ x, P x` | `intro x` | `move=> x` | Universal quantifier |
| `⊢ ∃ x, P x` | `exists [term]` | `exists [term]` | Existential proof |
| `⊢ A → B` | `intro H` | `move=> H` | Implication |
| `⊢ A ∧ B` | `split` | `split` | Conjunction |
| `⊢ A ∨ B` | `left`/`right` | `left`/`right` | Disjunction |
| `⊢ a ≤ b` | `lia`, `lra` | `by []` (MathComp) | Inequality |
| `⊢ list equality` | `simpl; reflexivity` | `by []` | List operations |

### 4. Search for Required Lemmas

**Based on goal and context:**

a) **Identify needed lemmas:**
```
To prove: [goal]
You likely need:
1. [lemma_type_1] (e.g., "list append property")
2. [lemma_type_2] (e.g., "arithmetic inequality")

Searching stdlib/MathComp...
```

b) **Run searches:**
```coq
(* Search by pattern *)
SearchPattern (_ + _ = _ + _).

(* Search by name *)
Search "comm" "add".

(* Search about topic *)
SearchAbout list.

(* Search in specific module *)
Search nat inside Coq.Arith.
```

c) **Present findings:**
```
Found relevant lemmas:

1. [lemma_name_1]
   Type: [signature]
   From: [module_path]
   Usage: [how_to_apply]

2. [lemma_name_2]
   Type: [signature]
   From: [module_path]
   Usage: [how_to_apply]

Add imports? (yes/pick-specific/search-more)
```

### 5. Generate Proof Candidates

**Create 2-3 approaches:**

**Candidate A: Direct application**
```coq
(* Strategy: Apply found lemmas directly *)
apply lemma_1.
(* Or: exact (lemma_1 args). *)
```

**Candidate B: Tactic-based**
```coq
(* Strategy: Step-by-step tactics *)
intro x.
assert (H1 : intermediate). { apply lemma_1. }
rewrite H1.
apply lemma_2.
```

**Candidate C: Automation-first**
```coq
(* Strategy: Let automation handle it *)
lia.
(* or: ring. *)
(* or: auto. *)
(* or: easy. *)
```

**SSReflect alternative:**
```coq
(* Strategy: SSReflect style *)
move=> x.
have H1 := lemma_1 x.
by rewrite H1; apply: lemma_2.
```

**Present candidates:**
```
Generated 3 proof approaches:

Candidate A (direct, 1 line):
  Pros: Shortest, most concise
  Cons: May fail if types don't align perfectly
  Code: [show candidate A]

Candidate B (tactics, 4 lines):
  Pros: Most likely to work, clear steps
  Cons: Longer, may need tweaking
  Code: [show candidate B]

Candidate C (automation, 1 line):
  Pros: Shortest if it works
  Cons: May fail, hard to debug if it does
  Code: [show candidate C]

Which to try first? (A/B/C/all-sequential)
```

### 6. Test Candidates

**Sequential testing:**

```
Testing Candidate A...
[Apply edit to file]
[Run: dune build or coqc file.v]

Result: [success/failure]
[If failure: show error and offer to try next]
```

**Report results:**
```
Test Results:
✓ Candidate A: SUCCESS (compiles)

Verification: dune build ✓

Recommendation: Use Candidate A (working solution)

Apply Candidate A? (yes/try-B-anyway/tweak-first)
```

**If candidate fails:**
```
✗ Candidate A: FAILED
Error: [error message]

Analysis: [explain error]

Try Candidate B? (yes/fix-A/search-different-lemmas)
```

### 7. Apply Working Solution

**If candidate succeeds:**

a) **Show the change:**
```
✅ Proof compiles!

Changes to [file]:[line]:

- admit.
+ [working_proof_code]

Verification: dune build ✓

Apply this change? (yes/tweak-first/no)
```

b) **If user wants to tweak:**
```
What would you like to change?
- Simplify (try shorter version)
- Add comments (explain steps)
- Use different lemma
- Convert to SSReflect style
- Custom edit

Choose: (simplify/comment/lemma/ssreflect/custom)
```

c) **Commit the change:**
```
Applied proof at [file]:[line]

Summary:
- Admit eliminated: ✓
- Proof type: [direct/tactics/automation]
- Length: [N] lines
- Imports added: [M] (if any)
- Compiled: ✓

Ready to commit? Use Print Assumptions [lemma] to verify no axioms.
```

### 8. Handle Failures

**If all candidates fail:**
```
❌ None of the generated candidates worked.

Analysis of failures:
Candidate A: [error_type] - [brief explanation]
Candidate B: [error_type] - [brief explanation]
Candidate C: [error_type] - [brief explanation]

Common issue: [identify pattern in failures]

Next steps:
1. Search for different lemmas (current ones may not fit)
2. Try different tactic approach
3. Break admit into smaller sub-admits
4. Consult compilation-errors.md for this error type
5. Ask for help (Coq Discourse, StackOverflow)

Which approach? (1/2/3/4/5/give-up-for-now)
```

**If breaking into sub-admits:**
```
I'll help you structure this proof with intermediate admits:

(* Strategy: Break [big_goal] into steps *)
assert (step1 : [subgoal_1]). { admit. }
assert (step2 : [subgoal_2]). { admit. }
apply step1, step2.

This creates 2 smaller admits that may be easier to tackle individually.

Apply this structure? (yes/adjust/no)
```

## Common Admit Types

### Type 1: "Forgot to search stdlib"

**Symptom:** Goal looks like it should exist
```coq
⊢ forall l, l ++ [] = l
```

**Solution:** `SearchPattern (_ ++ [])` finds `app_nil_r`
**Outcome:** Apply lemma, done!

### Type 2: "Just needs right tactic"

**Symptom:** Goal is obviously true
```coq
⊢ n + 0 = n
```

**Solution:** Try `reflexivity` or `lia`
**Outcome:** One-line proof

### Type 3: "Missing intermediate step"

**Symptom:** Gap between hypotheses and goal
```coq
Have: H : P x
Need: ⊢ Q x
```

**Solution:** Add `assert (intermediate : P x -> Q x). { apply lemma. }`
**Outcome:** Two-step proof

### Type 4: "Complex structural proof"

**Symptom:** Needs induction, cases, or extensive calculation
```coq
⊢ forall n : nat, P n
```

**Solution:** Use induction template
**Outcome:** Structured multi-line proof with base and step cases

### Type 5: "Actually needs new lemma"

**Symptom:** Truly novel result, stdlib doesn't have it
```coq
⊢ [your_domain_specific_result]
```

**Solution:** Prove as separate lemma, then use it here
**Outcome:** Extract to helper lemma, fill both

### Type 6: "MathComp/SSReflect specific"

**Symptom:** Using MathComp types and need canonical instances
```coq
⊢ equality on eqType
```

**Solution:** Use reflection views (`move/eqP`) or search MathComp lemmas
**Outcome:** SSReflect-style proof

## Best Practices

✅ **Do:**
- Always try stdlib/MathComp search first (60-90% hit rate)
- Test candidates before choosing
- Use automation tactics (lia, ring, auto) when applicable
- Add comments to complex proofs
- Verify with dune build before moving on
- Use coq-lsp for real-time feedback

❌ **Don't:**
- Skip the library search (it's usually there!)
- Apply candidate without testing
- Give up after first failure
- Fill admit without understanding the proof
- Forget to add necessary imports
- Use `Admitted` when you meant `Qed`

## Error Recovery

**Type mismatch:**
```
Error: The term "[term]" has type "[type_A]"
       while it is expected to have type "[type_B]"

Analysis: [identify mismatch reason]
Fix: [suggest coercion/conversion/different lemma]

Examples:
- nat vs Z: use Z.of_nat
- Need coercion: use INR for nat -> R
- Different types: check lemma signature
```

**Tactic failure:**
```
Error: Tactic failure: [tactic] does not apply

Analysis: Tactic doesn't match goal structure
Fix:
1. Check goal with Show.
2. Try simpler tactic or transform goal first
3. Use unfold or simpl to expose structure

Common: 'ring' only works on ring equations, 'lia' on linear arithmetic
```

**Import missing:**
```
Error: The reference [lemma_name] was not found

Analysis: Lemma exists but import missing
Fix: Adding Require Import [detected_module_path]

How to find: Search "[lemma_name]" or use Locate.
```

**Universe inconsistency:**
```
Error: Universe inconsistency

Analysis: Mixing Prop/Set/Type incorrectly
Fix: Check if definition should be in right universe
See compilation-errors.md section on universes
```

## Build System Integration

**With dune:**
```bash
# Test single file
coqc file.v

# Test full project
dune build

# Watch mode (rebuild on change)
dune build --watch
```

**With coq_makefile:**
```bash
make file.vo
```

**With CoqIDE:**
- Step through proof interactively
- See goal state at each step
- Test tactics before committing

## Related References

- [admit-filling.md](../skills/rocq-theorem-proving/references/admit-filling.md) - Complete admit-filling strategies
- [tactics-reference.md](../skills/rocq-theorem-proving/references/tactics-reference.md) - Complete tactic catalog
- [stdlib-guide.md](../skills/rocq-theorem-proving/references/stdlib-guide.md) - Search strategies
- [compilation-errors.md](../skills/rocq-theorem-proving/references/compilation-errors.md) - Error debugging
- [SKILL.md](../skills/rocq-theorem-proving/SKILL.md) - General workflow

## Automation Opportunities

**When to use automation:**
- Linear arithmetic: `lia`
- Ring equations: `ring`
- Field equations: `field`
- Equality reasoning: `congruence`
- Simple goals: `easy`, `auto`
- Propositional logic: `tauto`, `intuition`
- First-order logic: `firstorder`

**Example workflow:**
```coq
Lemma example n m : n + m = m + n.
Proof.
  (* Try automation first *)
  ring.  (* Success! *)
Qed.

Lemma example2 n m : n < m -> n + 1 <= m.
Proof.
  intro H.
  lia.  (* Success! *)
Qed.
```

## SSReflect-Specific Patterns

**Common SSReflect admit fills:**

```coq
(* Pattern 1: Boolean reflection *)
Lemma example (b1 b2 : bool) : b1 && b2 -> b1.
Proof.
  move/andP => [H1 H2].  (* Split and *)
  exact H1.
Qed.

(* Pattern 2: View application *)
Lemma example (n m : nat) : (n == m) -> n = m.
Proof.
  move/eqP.  (* View: bool eq to Prop eq *)
  by [].
Qed.

(* Pattern 3: Compact closing *)
Lemma example n : n + 0 = n.
Proof.
  by rewrite addn0.  (* Rewrite and close *)
Qed.
```

## Tips for Success

1. **Search first** - 60-90% of admits can be filled with existing lemmas
2. **Try automation** - lia, ring, auto solve many goals
3. **Decompose** - Break complex goals into smaller pieces
4. **Use LSP** - Real-time feedback catches errors immediately
5. **Read errors** - Error messages guide you to the fix
6. **Consult references** - tactics-reference.md and stdlib-guide.md are your friends
7. **Test incrementally** - Verify each candidate before moving on
8. **Document strategy** - Add comments for non-obvious proofs
