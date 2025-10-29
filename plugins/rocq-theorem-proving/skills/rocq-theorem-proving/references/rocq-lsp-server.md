# Rocq LSP Server: Fast Interactive Development

## Overview

This guide covers setting up and using **coq-lsp**, the Language Server Protocol implementation for Rocq/Coq, which provides:

- **Instant feedback** on proof state (< 1s vs 30s+ for full rebuild)
- **Real-time diagnostics** as you type
- **Go-to-definition** and hover information
- **Interactive proof development** with immediate goal display

**Speed improvement:** 30-100x faster feedback compared to manual compilation.

---

## Table of Contents

1. [Basic Usage](#basic-usage)
2. [Interactive Proof Development](#interactive-proof-development)
3. [Performance Tips](#performance-tips)
4. [Advanced Features](#advanced-features)
5. [Troubleshooting](#troubleshooting)
6. [Best Practice](#best-practice)

---

## Basic Usage

### Real-Time Feedback

As you type, coq-lsp:
- **Checks syntax** immediately
- **Type-checks** incrementally
- **Shows errors** inline
- **Displays goals** at cursor

**Example workflow:**
```coq
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  (* Place cursor here - see goal in hover/panel *)
  (* Goal: n + m = m + n *)
```

### Proof State Inspection

**Hover over any line** to see:
- Current proof state
- Goal to prove
- Available hypotheses
- Type information

**Panel view** (if supported):
- Live goal display
- Updates as cursor moves
- Shows all subgoals

### Incremental Checking

coq-lsp checks **up to cursor position**:
- Only processes visible proofs
- Skips unchecked parts
- Updates on save or request

**Configuration:**
```json
{
  "coq-lsp.check_only_on_request": true  // Manual check
  // or
  "coq-lsp.check_only_on_request": false  // Auto check
}
```

---

## Interactive Proof Development

### Workflow with LSP

**1. Write theorem statement**
```coq
Lemma example : forall n, n + 0 = n.
Proof.
  (* LSP shows: Need to prove forall n, n + 0 = n *)
```

**2. Step through tactics**
```coq
Proof.
  intro n.
  (* Hover here: Context: n : nat ⊢ n + 0 = n *)
```

**3. Try tactics and see results immediately**
```coq
  simpl.
  (* Goal unchanged because n + 0 doesn't reduce *)

  induction n.
  (* Two subgoals appear immediately *)
  - (* Goal: 0 + 0 = 0 *)
  - (* Goal: S n + 0 = S n, IHn : n + 0 = n *)
```

**4. Complete proof with instant feedback**
```coq
  - reflexivity.  (* First goal closes ✓ *)
  - simpl. rewrite IHn. reflexivity.  (* Second closes ✓ *)
Qed.  (* All goals solved ✓ *)
```

### Exploratory Proving

**Try tactics without committing:**
```coq
Proof.
  intro n.
  (* Try: *)  destruct n.  (* See what subgoals *)
  (* Don't like it? Undo (Ctrl+Z) and try: *)
  induction n.  (* Different subgoals *)
  (* Instant feedback on both approaches *)
```

### Parallel Development

**Multiple files:**
- Each file checked independently
- Changes propagate through imports
- No need to rebuild entire project

**Example:**
- Edit `Helper.v`
- Save
- `Main.v` using `Helper` updates automatically
- See errors in `Main.v` immediately

---

## Performance Tips

### Optimize for LSP

**1. Modular development**
```coq
(* Split large files into modules *)
(* helper.v *)
Lemma helper : P.
Proof. (* ... *) Qed.

(* main.v *)
Require Import helper.
Lemma main : Q.
Proof. apply helper. (* ... *) Qed.
```

**2. Use Sections**
```coq
Section FastChecking.
  (* Local context *)
  Variable A : Type.

  Lemma local1 : P1.
  Lemma local2 : P2.
  (* LSP only rechecks this section on changes *)
End FastChecking.
```

**3. Incremental mode**
```json
{
  "coq-lsp.check_only_on_request": true
}
```
- Check only when requested (Ctrl+Shift+Enter or save)
- Faster for large files
- Good for working on specific lemmas

### Reduce Recomputation

**1. Cache-friendly structure**
- Put stable lemmas first
- Experimental code at end
- LSP caches earlier results

**2. Minimize global state**
```coq
(* ❌ BAD - global state changes *)
Notation "x + y" := (my_add x y) (at level 50).
(* Forces recheck of entire file *)

(* ✅ GOOD - local scope *)
Section MyNotation.
  Notation "x + y" := (my_add x y) (at level 50).
  (* ... *)
End MyNotation.
```

**3. Avoid expensive tactics early**
```coq
(* If a proof is slow, mark it for later *)
Lemma expensive : P.
Proof using.  (* 'using' clause helps caching *)
  (* ... expensive proof ... *)
Qed.
```

---

## Advanced Features

### Go-to-Definition

**Click (or F12) on identifier** to jump to definition:
- Works for lemmas, tactics, notations
- Across files (if in project)
- Shows definition in hover

**Example:**
```coq
apply Nat.add_comm.
(* F12 on 'add_comm' → jumps to stdlib definition *)
```

### Find References

**Find all uses of definition:**
- Right-click → "Find References"
- Shows all locations using identifier
- Good for refactoring

### Hover Information

**Hover over:**
- **Lemma name**: See type and statement
- **Tactic**: See current goal state
- **Identifier**: See type
- **Notation**: See expansion

### Auto-completion

**Type prefix and get suggestions:**
```coq
apply Nat.ad
(* Autocomplete suggests:
   - Nat.add
   - Nat.add_comm
   - Nat.add_assoc
   - ... *)
```

**Context-aware:**
- Suggests tactics in proof mode
- Suggests lemmas matching goal type
- Filters by imports

---

## Troubleshooting

### LSP Not Starting

**Check:**
1. Is `coq-lsp` installed?
   ```bash
   which coq-lsp
   ```

2. Is extension enabled in editor?
   ```bash
   code --list-extensions | grep coq
   ```

3. Check LSP logs:
   - VSCode: Output panel → "Coq LSP"
   - Emacs: `*lsp-log*` buffer

4. Verify project structure:
   - Need `_CoqProject` file?
   - Correct paths in project file?

### Slow Performance

**Solutions:**

1. **Enable incremental mode:**
   ```json
   {"coq-lsp.check_only_on_request": true}
   ```

2. **Split large files:**
   - LSP faster on smaller files
   - < 1000 lines ideal

3. **Check expensive tactics:**
   - `auto` with large databases
   - Deeply nested `intuition`
   - Complex `simpl`

4. **Clear cache:**
   ```bash
   rm -rf .coq-lsp-cache
   ```

### Incorrect Diagnostics

**If LSP shows wrong errors:**

1. **Restart LSP:**
   - VSCode: Reload window (Ctrl+R)
   - Emacs: `M-x lsp-workspace-restart`

2. **Check file saved:**
   - Unsaved changes not always reflected

3. **Verify imports:**
   - Missing `Require Import`?
   - Wrong module path?

4. **Rebuild project:**
   ```bash
   dune clean && dune build
   ```

### LSP vs Compilation Mismatch

**LSP says OK but compilation fails:**

1. **Version mismatch:**
   ```bash
   coqc --version
   coq-lsp --version
   # Should match!
   ```

2. **Different flags:**
   - LSP may use different options
   - Check `_CoqProject` file
   - Ensure LSP reads it

3. **Opaque definitions:**
   - LSP may not see through `Opaque`
   - Compilation does

**Compilation OK but LSP shows errors:**

1. **Stale cache:**
   - Clear LSP cache
   - Restart editor

2. **Import order:**
   - LSP processes differently
   - May need explicit imports

---

## Best Practices

### Development Workflow

**1. Use LSP for development:**
```coq
(* Write proof with LSP feedback *)
Lemma foo : P.
Proof.
  (* Interactive development with instant feedback *)
Qed.
```

**2. Compile before committing:**
```bash
# LSP OK, but still compile to verify
dune build

# Commit only after compilation succeeds
git commit -m "proof: complete lemma foo"
```

**3. Use both LSP and compilation:**
- LSP: fast feedback during development
- Compilation: verification before commit

### Project Structure

**Enable LSP project-wide:**

**Create `_CoqProject`:**
```
-R src MyProject
-arg -w -arg -notation-overridden

src/Helper.v
src/Main.v
```

**LSP will:**
- Use these settings
- Understand module structure
- Provide cross-file features

---

## See Also

- [tactics-reference.md](tactics-reference.md) - Use LSP to try tactics
- [admit-filling.md](admit-filling.md) - Fill admits with LSP feedback
- [compilation-errors.md](compilation-errors.md) - Debug with LSP hints
- [coq-lsp GitHub](https://github.com/ejgallego/coq-lsp)
- [VsCoq Documentation](https://github.com/coq-community/vscoq)

---

**Philosophy:** LSP transforms Coq development from "compile and pray" to "see what you're doing". The instant feedback loop accelerates learning, reduces errors, and makes proof development feel interactive rather than batch-oriented.

**Recommendation:** Always use LSP for development. It's 30x faster and catches errors immediately. The days of waiting for full project compilation are over.
