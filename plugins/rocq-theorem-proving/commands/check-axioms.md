---
description: Verify axiom hygiene in Rocq/Coq proofs and identify non-standard axiom usage
allowed-tools: Bash(bash:*)
---

# Axiom Hygiene Verification

Check which axioms your Rocq/Coq theorems and lemmas depend on, highlighting non-standard or custom axioms that may need elimination strategies.

## Overview

This command uses `Print Assumptions` to verify that your proofs only rely on acceptable axioms. In Coq/Rocq:

**Standard/Acceptable Axioms:**
- `functional_extensionality` - Two functions equal if equal pointwise
- `proof_irrelevance` - All proofs of same proposition are equal
- Classical logic axioms (`classic`, `excluded_middle_informative`)
- `propositional_extensionality` - Equivalent propositions are equal

**Custom Axioms** (should be eliminated or justified):
- User-declared axioms
- `proof_admitted` - From `Admitted` proofs
- Domain-specific axioms without justification

---

## Workflow

### 1. Determine Scope

**Ask user if not obvious:**
```
Check axioms for:
1. Current file only
2. Current directory (recursive)
3. Specific file or directory
4. Entire project

Which scope? (1/2/3/4)
```

**Scope examples:**
- Single file: `theories/Main.v`
- Directory: `src/theorems/`
- Entire project: `.` (current directory)

### 2. Run Check

**Execute check_axioms.sh script:**

```bash
# For single file
${ROCQ_PLUGIN_ROOT}/scripts/check_axioms.sh theories/Main.v

# For directory
${ROCQ_PLUGIN_ROOT}/scripts/check_axioms.sh src/theorems/

# Verbose mode (show all axioms)
${ROCQ_PLUGIN_ROOT}/scripts/check_axioms.sh src/ --verbose

# Entire project
${ROCQ_PLUGIN_ROOT}/scripts/check_axioms.sh .
```

**Show progress:**
```
Checking axioms in: src/theorems/
Found 42 declarations in 8 files

Analyzing...
```

### 3. Report Results

**If no custom axioms found:**
```
✅ All declarations use only standard axioms or are constructive

Standard axioms (acceptable):
  • functional_extensionality (function extensionality)
  • proof_irrelevance (proof irrelevance)
  • classic / excluded_middle_informative (classical logic)
  • propositional_extensionality (propositional extensionality)

Note: Any 'Admitted' proofs introduce 'proof_admitted' axiom
```

**If custom axioms found:**
```
⚠ Found 3 uses of non-standard axioms

⚠ main_theorem (theories/Main.v) uses non-standard axiom: my_custom_axiom
⚠ helper_lemma (theories/Helper.v) uses non-standard axiom: my_custom_axiom
⚠ incomplete_proof (theories/Draft.v) uses non-standard axiom: proof_admitted

Custom axioms used:
  • my_custom_axiom
  • proof_admitted

Standard axioms (acceptable):
  • functional_extensionality (function extensionality)
  • proof_irrelevance (proof irrelevance)
  • classic / excluded_middle_informative (classical logic)
  • propositional_extensionality (propositional extensionality)

Note: Any 'Admitted' proofs introduce 'proof_admitted' axiom
Tip: Use axiom-elimination.md for removing custom axioms
```

### 4. Analyze Custom Axioms

**For each custom axiom found, provide guidance:**

**Type 1: proof_admitted (from Admitted)**
```
⚠ Found proof_admitted axiom

Cause: Incomplete proofs (Admitted instead of Qed)

Locations:
  • incomplete_proof (theories/Draft.v)

Action: Complete the proof using /fill-admit command

This is high priority - admitted proofs make your theorem
meaningless as it assumes what needs to be proven.
```

**Type 2: User-declared axiom**
```
⚠ Found user-declared axiom: my_custom_axiom

This axiom was declared with 'Axiom' or 'Parameter'.

Locations using this axiom:
  • main_theorem (theories/Main.v)
  • helper_lemma (theories/Helper.v)

Options:
1. Prove it - Turn axiom into theorem with proof
2. Justify it - Document why this axiom is necessary
3. Eliminate it - Find alternative approach

See axiom-elimination.md for strategies.

Check where axiom is declared:
  grep -r "Axiom my_custom_axiom" .
  grep -r "Parameter my_custom_axiom" .
```

**Type 3: Standard axiom from wrong import**
```
⚠ Found unexpected standard axiom usage

If you see axioms you didn't expect (like Classical.choice
when you thought your proof was constructive), this means:

1. Your proof implicitly uses classical logic
2. One of your dependencies uses classical logic
3. An import brings in classical axioms

To investigate:
  Print Assumptions <theorem_name>.

This will show the dependency chain.

Options:
  • Accept it (classical logic is fine for many purposes)
  • Make proof constructive (remove Classical imports)
  • Split into constructive core + classical wrapper
```

### 5. Provide Elimination Strategies

**If custom axioms found, suggest strategies:**

```
Custom axiom elimination strategies:

For proof_admitted:
  Priority: CRITICAL
  1. Use /fill-admit command on incomplete proof
  2. Search stdlib for existing lemmas
  3. Break into smaller admits if complex

For custom axioms:
  Priority: HIGH

  Strategy 1: Prove it
    • Check if axiom is actually provable
    • May need additional standard axioms
    • Example: Some axioms in Analysis need Classical

  Strategy 2: Strengthen to constructive version
    • Remove existence → provide algorithm
    • Example: "exists x, P x" → "find_x : {x | P x}"

  Strategy 3: Make it a parameter
    • If axiom is domain-specific assumption
    • Pass as parameter to theorems that need it
    • Example: Axiom measure_exists → Variable measure

  Strategy 4: Use standard library version
    • Check if Coq stdlib has equivalent
    • Search MathComp for algebraic structures
    • Example: Custom field axioms → use MathComp fieldType

See axiom-elimination.md for detailed patterns.

Apply elimination strategy? (yes/show-file/manual-review)
```

### 6. Offer to Fix Admits

**If proof_admitted found, offer to fill them:**

```
Found 2 incomplete proofs (Admitted):
1. incomplete_proof (theories/Draft.v:42)
2. helper_lemma (theories/Helper.v:103)

Would you like to fill these admits?
1. Fill all interactively
2. Choose which ones to fill
3. Skip for now (commit will fail)

Choose: (1/2/3)
```

**If user chooses to fill:**
```
Starting with incomplete_proof at theories/Draft.v:42

[Use /fill-admit workflow]
```

### 7. Offer to Document Axioms

**If user-declared axioms found and justified:**

```
You have 1 custom axiom in use: my_custom_axiom

If this axiom is necessary (e.g., domain-specific assumption),
document its justification:

Create: docs/axioms.md

# Axiom Justification

## my_custom_axiom

**Declaration:** theories/Axioms.v:10

**Statement:**
  Axiom my_custom_axiom : forall x, P x -> Q x.

**Justification:**
  This axiom represents the physical assumption that...
  [Explain why this cannot be proven within Coq]

**Used by:**
  • main_theorem (theories/Main.v)
  • helper_lemma (theories/Helper.v)

**Verification:**
  External verification performed via...

Create documentation? (yes/no/edit-manually)
```

---

## Common Axiom Issues

### Issue 1: Unexpected Classical Usage

**Symptom:**
```
⚠ constructive_theorem uses axiom: classic
```

**Cause:** Proof uses classical logic implicitly

**Debug:**
```coq
Print Assumptions constructive_theorem.
(* Shows dependency chain *)
```

**Fix:**
```
1. Check imports - remove Classical.* imports
2. Replace classical tactics:
   • classic → constructive case analysis
   • tauto → manual proof
   • classical_right/left → explicit construction
3. Use SSReflect booleans instead of Prop
```

### Issue 2: Admitted Proof

**Symptom:**
```
⚠ theorem uses axiom: proof_admitted
```

**Cause:** Proof ends with `Admitted` instead of `Qed`

**Fix:**
```
1. Complete the proof with /fill-admit
2. If temporarily incomplete, document:
   Admitted. (* TODO: Finish proof of X property *)
3. Never commit with Admitted in main results
```

### Issue 3: Custom Axiom in Library Code

**Symptom:**
```
⚠ dependency_theorem uses axiom: my_axiom
```

**Cause:** Axiom comes from imported library

**Debug:**
```coq
Require Import SuspiciousLibrary.
Print Assumptions dependency_theorem.
(* Shows my_axiom from SuspiciousLibrary *)
```

**Fix:**
```
1. Check library documentation for axiom justification
2. Consider alternative library without axioms
3. Report to library maintainers if axiom seems provable
```

### Issue 4: Extensionality Axioms

**Symptom:**
```
⚠ Uses functional_extensionality
```

**Assessment:** This is usually fine!

**Context:**
- Standard in modern Coq
- Required for reasoning about functions
- Accepted by most proof standards

**Action:** Usually no action needed unless:
- You need strict constructiveness
- Target requires axiom-free proofs
- Proof assistants without this axiom

---

## Integration with Git Hooks

**Pre-commit hook:**

```bash
#!/bin/bash
# .git/hooks/pre-commit

echo "Checking axiom hygiene..."

if ! /path/to/check_axioms.sh .; then
  echo "❌ Custom axioms detected!"
  echo "Fix with /check-axioms command or override with --no-verify"
  exit 1
fi

echo "✅ Axiom check passed"
```

**To install hook:**
```bash
# Create pre-commit hook
cat > .git/hooks/pre-commit << 'EOF'
#!/bin/bash
if [ -f "${ROCQ_PLUGIN_ROOT}/scripts/check_axioms.sh" ]; then
  "${ROCQ_PLUGIN_ROOT}/scripts/check_axioms.sh" .
fi
EOF

chmod +x .git/hooks/pre-commit
```

---

## Advanced Usage

### Whitelist Custom Axioms

**If you have justified custom axioms:**

Create `.axiom-whitelist`:
```
# Project-specific axioms (justified in docs/axioms.md)
my_domain_axiom
physics_assumption
measurement_axiom
```

**Modify check_axioms.sh:**
```bash
# Add to STANDARD_AXIOMS array from whitelist file
if [[ -f ".axiom-whitelist" ]]; then
  while IFS= read -r axiom; do
    [[ "$axiom" =~ ^# ]] && continue  # Skip comments
    STANDARD_AXIOMS+=("$axiom")
  done < .axiom-whitelist
fi
```

### Check Specific Theorems Only

**Manual check in Coq:**
```coq
Require Import MyTheories.Main.

Print Assumptions main_theorem.
(* Shows: Closed under the global context *)
(* Or: Axioms: functional_extensionality *)

Print Assumptions helper_lemma.
```

### Compare Axiom Usage Across Branches

**Check axiom changes:**
```bash
# Current branch
./check_axioms.sh . > axioms_current.txt

# Main branch
git stash
git checkout main
./check_axioms.sh . > axioms_main.txt
git checkout -

# Compare
diff axioms_main.txt axioms_current.txt
```

---

## Best Practices

✅ **Do:**
- Check axioms before committing
- Document justified custom axioms
- Complete admitted proofs before merging
- Use standard library axioms when needed
- Accept functional_extensionality (it's standard)

❌ **Don't:**
- Commit with `proof_admitted` (incomplete proofs)
- Declare axioms without documentation
- Use classical logic unintentionally
- Ignore axiom warnings
- Assume "axiom-free" means "better" always

---

## Axiom Philosophy

**Constructive vs Classical:**
- Constructive: No axioms (or minimal: extensionality)
- Classical: Accepts LEM, choice, proof irrelevance
- Pragmatic: Use what you need, document it

**When axioms are OK:**
- Standard library axioms (functional_extensionality, etc.)
- Classical logic for classical mathematics
- Proof irrelevance for practical reasoning
- Domain axioms (documented and justified)

**When axioms are NOT OK:**
- Admitted proofs (proof_admitted)
- Provable statements declared as axioms
- Undocumented custom axioms
- Axioms that contradict constructiveness claims

---

## Related Commands

- `/fill-admit` - Complete admitted proofs
- `/build-rocq` - Verify project compiles (including axiom checks)

## References

- [axiom-elimination.md](../skills/rocq-theorem-proving/references/axiom-elimination.md) - Strategies for removing axioms
- [compilation-errors.md](../skills/rocq-theorem-proving/references/compilation-errors.md) - Fix axiom-related errors
- Coq Reference Manual: Chapter on Axioms
- MathComp Book: Section on Constructive Mathematics

---

**Philosophy:** Axioms aren't inherently bad, but they should be intentional, documented, and justified. The goal is axiom *hygiene*, not axiom *elimination*. Use this command to ensure you know what assumptions your proofs make.
