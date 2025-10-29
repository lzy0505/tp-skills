---
description: Build Rocq/Coq project and provide formatted error analysis
---

# Build and Error Analysis

Quick build verification with formatted error reporting and fix suggestions.

## Workflow

### 1. Determine Scope

**Ask if not obvious from context:**
```
Build:
1. Current file only
2. All changed files (git diff)
3. Entire project
4. Specific file/target

Which scope? (1/2/3/4)
```

### 2. Run Build

**For full project (Dune):**
```bash
dune build
```

**For single file:**
```bash
coqc [file.v]
```

**For specific target:**
```bash
dune build [target]
```

**Show progress:**
```
Building Rocq project...
This may take a minute for first build.

[If slow]:
Tip: Use incremental compilation and split large files
```

### 3. Report Results

**If build succeeds:**
```
✅ BUILD SUCCESSFUL

All files compiled without errors!

Files built: [N]
Build time: [X]s
Warnings: [Y] (if any)

[If warnings exist]:
⚠️ [Y] warnings detected (build succeeded but see below)

Next steps:
- Run Print Assumptions on main theorems to check axiom hygiene
- Consider optimizing proofs (see proof-golfing.md)
- Commit your changes!
```

**If build fails:**
```
❌ BUILD FAILED

Errors detected: [N] error(s) in [M] file(s)

I'll analyze each error and suggest fixes...
```

### 4. Analyze Errors

**Group errors by type:**

```
Error Summary:

Type Mismatch: [N] errors
  - [file]:[line] - [brief description]
  - [file]:[line] - [brief description]

Cannot Infer / Typeclass Resolution: [M] errors
  - [file]:[line] - [brief description]

Universe Inconsistency: [K] errors
  - [file]:[line] - [brief description]

Not Found / Unknown Identifier: [O] errors
  - [file]:[line] - [brief description]

Tactic Failure: [P] errors
  - [file]:[line] - [brief description]

Other: [Q] errors
  - [file]:[line] - [brief description]
```

### 5. Provide Fix Suggestions

**For each error, offer specific guidance:**

**Type Mismatch:**
```
Error at [file]:[line]

The term "[term]" has type "[type_A]"
while it is expected to have type "[type_B]".

Analysis:
[Identify issue: coercion needed / wrong lemma / incorrect argument order]

Suggested fixes:
1. [specific fix with code]
2. [alternative approach]
3. [general guidance]

Which error to fix first? (this-one/next/show-all)
```

**Cannot Infer Typeclass Instance:**
```
Error at [file]:[line]

Cannot infer this placeholder of type "[instance_type]".
(or: Cannot find instance of "[instance_type]")

Analysis:
[Check if instance exists / needs explicit declaration / wrong type structure]

Common causes:
1. Missing import (search: "Instance [instance_type]")
2. Need explicit declaration: Existing Instance ...
3. Need to provide instance in proof context
4. Type structure mismatch (check your types)

Suggested fix:
[specific code to add]

Reference: See compilation-errors.md section on typeclass resolution

Apply fix? (yes/search-for-instance/read-docs)
```

**Universe Inconsistency:**
```
Error at [file]:[line]

Universe inconsistency (cannot enforce [constraint]).

Analysis:
[Check Prop/Set/Type levels / polymorphism needed]

Common causes:
1. Mixing Prop and Type incorrectly
2. Circular universe dependency
3. Need universe polymorphism

Suggested fixes:
1. Check if definition should be in Prop or Type
2. Use Set Universe Polymorphism
3. Make definition monomorphic

Reference: See compilation-errors.md section on universes

Try fix? (yes/explain-more/show-context)
```

**Not Found / Unknown Identifier:**
```
Error at [file]:[line]

The reference [name] was not found in the current environment.

Analysis:
[Typo / missing import / not in scope / needs qualification]

Likely cause: Missing import

Searching stdlib/MathComp for '[name]'...

Found in: [module_path]

Add import? (yes/no/search-more)
```

**Tactic Failure:**
```
Error at [file]:[line]

Tactic failure: [tactic_name]
[error message]

Analysis:
[Why tactic doesn't apply / goal mismatch / hypothesis issue]

Suggested fixes:
1. Check goal state with Show.
2. Try alternative tactic: [suggestion]
3. Simplify or unfold definitions first

Current goal: [goal if available]

Try alternative? (yes/show-goal/read-tactics-ref)
```

### 6. Interactive Error Fixing

**Offer to fix errors interactively:**

```
Would you like me to:
1. Fix errors one by one (interactive)
2. Show all errors and let you decide
3. Generate error report for later

Choose: (1/2/3)
```

**If option 1 (interactive):**
```
Error 1 of [N]: [file]:[line]

[Show error details and suggestions]

Fix this error? (yes/skip/explain-more/stop)
```

**After each fix:**
```
Applied fix at [file]:[line]

Rebuilding to verify...

[Run dune build or coqc]

[If successful]:
✓ Fix verified! Error eliminated.

Remaining errors: [N-1]
Continue? (yes/no)

[If new errors]:
⚠️ Fix created new error:
[Show new error]

Revert? (yes/try-different-fix)
```

### 7. Track Progress

**For multiple-error sessions:**
```
Error Fixing Progress:

Original errors: [N]
Fixed: [M]
Remaining: [K]
New (from fixes): [O]

Success rate: [M/(M+K) * 100]%
Time invested: ~[X] minutes

Current error: [description]

Keep going? (yes/take-break/commit-progress)
```

## Common Error Patterns

### Pattern 1: Import Chain Issues

```
Error: The reference List.map was not found

Cause: Missing import
Fix: Require Import Coq.Lists.List.

Prevention: Use Search to find module paths
```

### Pattern 2: Typeclass Instance Missing

```
Error: Cannot infer this placeholder of type "Inhabited A"

Cause: Instance exists but Coq can't infer it
Fix: Add explicit declaration
  Existing Instance A_inhabited.
  (* Or in proof: *)
  Context `{Inhabited A}.

Reference: See compilation-errors.md for instance management
```

### Pattern 3: Coercion Confusion

```
Error: The term "n" has type "nat"
       while it is expected to have type "Z"

Cause: Natural number used where integer expected
Fix: Add conversion: Z.of_nat n
     (Or for reals: INR n)

Common: Arithmetic expressions mixing types
```

### Pattern 4: Universe Inconsistency

```
Error: Universe inconsistency (cannot enforce Set <= Prop)

Cause: Trying to extract data from Prop
Fix: Check if definition should be in Type not Prop
     Or use proper universe levels

Example: See compilation-errors.md universe section
```

### Pattern 5: Scope and Namespace Issues

```
Error: The reference map was not found

Cause: Not in scope
Fix: Either:
  1. Use qualified name: List.map
  2. Import and open: Require Import Coq.Lists.List.
                      Import ListNotations.

Choice: Prefer qualified names for clarity
```

### Pattern 6: Tactic Doesn't Apply

```
Error: Unable to apply [tactic]

Cause: Goal doesn't match tactic's pattern
Fix: Check goal with Show., try simpler tactic,
     or transform goal first (unfold, simpl, etc.)

Debug: See tactics-reference.md for tactic patterns
```

## Integration with Other Tools

**With compilation-errors.md:**
```
For detailed error explanation, see:
[link to specific section in compilation-errors.md]

Common patterns:
- Typeclass resolution: Section 1
- Universe issues: Section 2
- Type mismatches: Section 3
- Tactic failures: Section 4
```

**With coq-lsp:**
```
If using coq-lsp, get real-time diagnostics:

- Exact error locations
- Error severity levels
- Hover for quick fixes
- Incremental checking

See rocq-lsp-server.md for setup
```

## Build Performance Tips

**First build slow:**
```
First build taking [X] minutes...

This is normal! Subsequent builds will be faster (~[Y]s).

What's happening:
- Building all dependencies (stdlib, MathComp, etc.)
- Creating compiled .vo files
- Processing imports

Tip: Let it finish once, then builds are incremental.
```

**Subsequent builds slow:**
```
Build taking longer than expected...

Possible causes:
1. Changed core file (rebuilds many dependents)
2. Import chain issues
3. Large proof file
4. Expensive tactics (auto with large databases, etc.)

Solutions:
- Split large files
- Optimize tactics (replace auto with specific tactics)
- Check import structure
```

**Dune-specific tips:**
```
# Parallel builds (faster)
dune build -j4

# Watch mode (rebuild on change)
dune build --watch

# Clean and rebuild
dune clean && dune build

# Build specific target
dune build @install
```

## Error Handling

**If dune not found:**
```
❌ 'dune' command not found

You may not be in a Dune project directory.

Expected structure:
  dune-project
  dune (in subdirectories)
  *.v files

Current directory: [pwd]

Alternative: Use coqc directly for single files
  coqc file.v

Are you in the right directory? (yes/cd-to-project/use-coqc)
```

**If _CoqProject present (alternative build system):**
```
Found _CoqProject file.

This project uses coq_makefile build system.

Build commands:
  coq_makefile -f _CoqProject -o Makefile
  make

Use this instead? (yes/no/try-dune-anyway)
```

**If version mismatch:**
```
⚠️ Rocq/Coq version mismatch

Project expects: Rocq x.y.z
You have: Coq a.b.c

This may cause build errors or incompatibilities.

Fix: Install correct version
  opam switch create project-name ocaml-base-compiler.x.y.z
  opam install coq.x.y.z

Install correct version? (yes/no/ignore)
```

**If out of memory:**
```
❌ Build failed: Out of memory

Your proof files may be too large or using expensive tactics.

Solutions:
1. Break large proofs into smaller lemmas
2. Replace expensive tactics (auto, intuition) with specific ones
3. Increase available memory
4. Build with single job: dune build -j1

Try building with -j1? (yes/no/optimize-tactics)
```

## Best Practices

✅ **Do:**
- Build frequently (after each small change)
- Fix errors as they appear (don't accumulate)
- Read error messages carefully
- Use references (compilation-errors.md) for patterns
- Commit after successful builds
- Use coq-lsp for real-time feedback

❌ **Don't:**
- Ignore warnings (they may indicate real issues)
- Accumulate many errors before fixing
- Skip understanding errors (leads to cargo-cult fixes)
- Forget to rebuild after fixes
- Commit without building
- Use admits as "TODO" markers without documentation

## Advanced Features

**Watch mode:**
```
For continuous building during development:

dune build --watch

This rebuilds automatically when files change.
Useful during active development.
```

**Parallel builds:**
```
Speed up builds with parallel compilation:

dune build -j4  # Use 4 cores

Caveat: May use more memory
```

**Targeted builds:**
```
Build specific module:

dune build src/MyModule.vo

Faster than full project build.
```

**Verbose output:**
```
Debug build issues:

dune build --verbose

Shows all commands executed.
```

## Build Systems Comparison

| Build System | Command | When to Use |
|--------------|---------|-------------|
| **Dune** | `dune build` | Modern projects, OCaml integration |
| **coq_makefile** | `make` (after coq_makefile) | Traditional, _CoqProject files |
| **coqc** | `coqc file.v` | Single files, quick tests |
| **CoqIDE** | Built-in | Interactive development |

**Recommendation:** Use Dune for new projects, respects existing build system for legacy.

## Related Commands

- `/fill-admit` - Fix admits that prevent building
- `/golf-proofs` - Optimize after build succeeds

## References

- [compilation-errors.md](../skills/rocq-theorem-proving/references/compilation-errors.md) - Detailed error patterns
- [tactics-reference.md](../skills/rocq-theorem-proving/references/tactics-reference.md) - Tactic reference
- [rocq-lsp-server.md](../skills/rocq-theorem-proving/references/rocq-lsp-server.md) - LSP setup for real-time feedback
- [SKILL.md](../skills/rocq-theorem-proving/SKILL.md) - General development workflow
