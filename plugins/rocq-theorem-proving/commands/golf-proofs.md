---
description: Interactively optimize Rocq/Coq proofs by shortening length without sacrificing readability
allowed-tools: Bash(bash:*)
---

# Interactive Proof Optimization

Apply systematic proof-golfing patterns to optimize Rocq/Coq proofs after compilation.

## Workflow

Follow this systematic process to achieve 20-40% size reduction while maintaining readability:

### 1. Verify File is Ready

**Before starting, confirm:**
- File compiles successfully (`dune build` or `coqc file.v`)
- No uncommitted changes (or user is okay with edits)
- Not actively being worked on (avoid conflicts)

**Ask user:**
```
Ready to optimize [file]? This will:
- Find optimization patterns
- Apply changes interactively with your approval
- Test each change with compilation

Continue? (yes/no)
```

### 2. Find Optimization Patterns

**Manually search for common patterns:**

```bash
# Pattern 1: Unnecessary auto
grep -n "auto\." [file.v]

# Pattern 2: simpl; reflexivity (redundant simpl)
grep -B1 "reflexivity" [file.v] | grep "simpl"

# Pattern 3: intro; exact
grep -A1 "intro " [file.v] | grep "exact"

# Pattern 4: Single-use assertions
grep -n "assert.*{" [file.v]

# Pattern 5: SSReflect: move=> without combining
grep -n "move=>" [file.v]
```

**If 0 patterns found:**
```
✅ No obvious optimization opportunities found in [file].
This means either:
- File is already well-optimized
- Patterns are marginal (not worth the effort)
- Codebase has reached saturation

Recommendation: Move on to other files or declare victory!
```

**If patterns found:**
Show summary and proceed to next step.

### 3. Categorize by Priority

**Group patterns by potential impact:**

| Pattern | Savings | Priority | Effort |
|---------|---------|----------|--------|
| `auto` → specific tactic | Variable | ⭐⭐⭐⭐⭐ | Low |
| `intros; exact` → term | 60-80% | ⭐⭐⭐⭐⭐ | Low |
| `simpl; reflexivity` → `reflexivity` | 50% | ⭐⭐⭐⭐⭐ | Zero |
| Single-use assert inline | 40-60% | ⭐⭐⭐⭐ | Medium |
| SSReflect combinations | 50% | ⭐⭐⭐⭐ | Low |
| Tactic sequences → automation | 50-80% | ⭐⭐⭐ | Medium |

**Focus strategy:**
```
Found patterns in these categories:
- [X] instant wins (zero risk, immediate benefit)
- [Y] high-value (test first, likely works)
- [Z] marginal (small gains, not worth it)

Recommendation: Focus on instant wins first for best ROI.
Tackle instant wins? (yes/no/show-all)
```

### 4. Apply Optimizations

**For each pattern:**

a) **Show user the before/after:**
```
Pattern: [pattern_type] at line [N]
Estimated savings: [X] lines, [Y]% reduction

BEFORE:
[show 5-10 lines of current code]

PROPOSED CHANGE:
[show optimized version]

Risk: [zero/low/medium]
Rationale: [why this optimization is valid]

Apply this optimization? (yes/no/skip-remaining)
```

b) **If user says yes:**
- Apply the edit
- Run `dune build` or `coqc file.v` to verify
- If build fails: revert and report error
- If build succeeds: move to next pattern

c) **Track cumulative savings:**
```
Applied [N] optimizations so far:
- Lines saved: [X]
- Reduction: [Y]%
- All changes verified: ✓
```

### 5. Test Each Change Immediately

**Critical: Test after each optimization:**

```bash
# For dune projects
dune build

# For single files
coqc [file.v]

# For coq_makefile projects
make [target.vo]
```

**If compilation fails:**
```
❌ Compilation failed after optimization at line [N]

Error: [show error message]

Action: Reverting change and continuing with next pattern.
This optimization needs manual investigation.

[Show revert diff]

Continue with next pattern? (yes/no/stop)
```

**If compilation succeeds:**
```
✓ Optimization verified! File still compiles.

Savings: [X] lines ([Y] tokens estimated)
Remaining patterns: [N]

Continue? (yes/no)
```

### 6. Common Optimization Patterns

Based on proof-golfing.md reference:

**Pattern 1: Remove Unnecessary `auto`**
```coq
(* Before *)
Proof.
  intros n m H.
  auto.
Qed.

(* After *)
Proof.
  intros n m H.
  assumption.  (* or: exact H *)
Qed.
```
**Risk:** Zero (if build passes)
**Savings:** Compilation speed, clarity

**Pattern 2: `intros; exact` → Direct Term**
```coq
(* Before *)
Lemma example : forall n m, n + m = m + n.
Proof.
  intros n m.
  exact (Nat.add_comm n m).
Qed.

(* After *)
Lemma example : forall n m, n + m = m + n.
Proof. exact Nat.add_comm. Qed.
```
**Risk:** Low
**Savings:** 60-80%

**Pattern 3: `simpl; reflexivity` → `reflexivity`**
```coq
(* Before *)
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.

(* After *)
Proof.
  intro n.
  reflexivity.  (* Simplifies automatically *)
Qed.
```
**Risk:** Zero
**Savings:** 50%

**Pattern 4: Single-Use Assert Inline**
```coq
(* Before *)
Proof.
  intro H.
  assert (Htemp : intermediate). { lia. }
  apply Htemp.
Qed.

(* After - if intermediate is simple *)
Proof.
  intro H.
  lia.
Qed.
```
**Risk:** Low (verify assert used only once)
**Savings:** 40-60%

**Pattern 5: SSReflect Combinations**
```coq
(* Before *)
Proof.
  move=> x.
  simpl.
  (* ... *)

(* After *)
Proof.
  move=> /= x.  (* Combine intro and simpl *)
  (* ... *)
```
**Risk:** Zero
**Savings:** 50%

**Pattern 6: Rewrite and Clear (SSReflect)**
```coq
(* Before *)
rewrite H.
clear H.

(* After *)
rewrite {}H.  (* Rewrite and clear *)
```
**Risk:** Zero
**Savings:** 50%

**Pattern 7: Tactic Sequences → Automation**
```coq
(* Before *)
Proof.
  intros.
  apply le_S.
  apply le_n.
Qed.

(* After *)
Proof.
  lia.
Qed.
```
**Risk:** Medium (verify automation handles it)
**Savings:** 50-80%

### 7. Readability Check

**For each optimization, consider:**

```
Readability impact:
- Does this make the proof harder to understand?
- Is the semantic meaning lost?
- Would you understand this in 6 months?

If answer to any is "yes", consider SKIPPING this optimization.

Example of bad optimization:
  Before: assert (key_insight : ...). { complex_proof }
  After: (inlined 20-line proof)
  Problem: Lost the semantic name "key_insight"

Proceed with this optimization? (yes/no/tweak-first)
```

### 8. Check for Saturation

**After each batch of 5-10 optimizations:**

**Saturation signs:**
- Success rate drops below 30%
- Time per optimization exceeds 10 minutes
- Debating trivial 1-line savings
- Breaking proof modularity

**If saturation detected:**
```
🏁 Saturation point reached!

Statistics:
- Optimizations applied: [N]
- Lines saved: [X]
- Reduction: ~[Y]%
- Time invested: ~[Z] minutes

Remaining patterns are marginal (low ROI).
Recommendation: Declare victory and move on!

Continue optimizing anyway? (yes/no)
```

### 9. Final Verification

**After all optimizations:**

```bash
# Full compilation check
dune build

# Verify no axioms introduced
coqtop -q
> Require Import YourFile.
> Print Assumptions main_theorem.
```

**Report results:**
```
✅ Proof optimization complete!

Final Statistics:
- Patterns found: [total]
- Patterns applied: [applied] ([success_rate]%)
- Lines saved: [lines]
- Reduction: [percent]%
- Time invested: ~[minutes] minutes

File compiles successfully: ✓
No new axioms introduced: ✓

Ready to commit these changes!
```

## Safety Guidelines

### When to SKIP Optimization

**Skip if ANY of these:**
- ❌ Assert used ≥2 times (inlining increases size)
- ❌ Semantic naming aids understanding
- ❌ Proof structure documents reasoning
- ❌ Would create deeply nested terms
- ❌ Maintainability cost > space savings
- ❌ Compilation fails after change

### Verification Checklist

Before committing optimizations:
- [ ] File compiles (`dune build` or `coqc`)
- [ ] No new axioms (Print Assumptions)
- [ ] Proof is still understandable
- [ ] No regression in build time
- [ ] Git diff looks reasonable

## Domain-Specific Patterns

### SSReflect-Specific

**Combine operations:**
```coq
move=> {H} x.         (* Intro x, clear H *)
rewrite {}H.          (* Rewrite and clear *)
case: x => //.        (* Case and close trivial *)
by rewrite H.         (* Rewrite and close *)
```

**Compact closing:**
```coq
(* Before *)
move=> H.
apply: H.
reflexivity.

(* After *)
by move=> H; apply: H.
```

### Standard Coq

**Use `now`:**
```coq
(* Before *)
apply lemma.
auto.

(* After *)
now apply lemma.
```

**Chain tactics:**
```coq
(* Before *)
intro H.
destruct H as [H1 H2].
apply H1.

(* After *)
intros [H1 H2]; apply H1.
```

## Error Handling

**If optimization breaks compilation:**
```
❌ Compilation error after optimization

Error message:
[show error]

Analysis:
[explain why optimization failed]

Action:
- Reverting change
- Marking pattern for manual review
- Continuing with next pattern

Pattern saved to: [file].golf-review.txt
```

**If uncertain about safety:**
```
⚠️ Uncertain about this optimization

Pattern: [description]
Risk: Medium (not verified safe)

Options:
1. Skip (safety first)
2. Try and revert if fails
3. Manual review

Choose: (1/2/3)
```

## Tools and Automation

**Manual pattern detection:**
```bash
# Find potential optimizations
grep -n "Pattern" file.v

# Count line reduction potential
wc -l file.v  # Before
# Apply optimizations
wc -l file.v  # After
```

**Automated testing:**
```bash
# Test after each change
dune build --watch  # Continuous building

# Or test each change
for opt in optimizations; do
  apply_opt $opt
  dune build || revert_opt $opt
done
```

## Best Practices

✅ **Do:**
- Test after EACH optimization
- Focus on high-priority patterns
- Stop at saturation
- Preserve readability
- Commit incrementally

❌ **Don't:**
- Batch untested changes
- Continue past saturation
- Sacrifice readability for tiny gains
- Break proof structure
- Forget to verify compilation

## Related Commands

- `/build-rocq` - Quick build verification
- `/fill-admit` - Complete admits first

## References

- [proof-golfing.md](../skills/rocq-theorem-proving/references/proof-golfing.md) - Complete pattern catalog with examples
- [tactics-reference.md](../skills/rocq-theorem-proving/references/tactics-reference.md) - Alternative tactics
- [ssreflect-patterns.md](../skills/rocq-theorem-proving/references/ssreflect-patterns.md) - SSReflect optimizations

---

**Philosophy:** Proof golfing is about making code clearer and more maintainable, not just smaller. The best optimization is one that makes the proof easier to understand while being shorter. When in doubt, choose readability.
