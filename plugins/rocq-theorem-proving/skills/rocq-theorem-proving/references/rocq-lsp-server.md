# Rocq LSP Server Reference

**The Rocq LSP server provides instant feedback for interactive theorem development.**

This reference documents the workflow and tools for Rocq/Coq proof development using the Rocq LSP MCP server.

**Key insight:** LSP tools provide instant feedback (< 1 second) versus build cycles (10-30+ seconds). This **30x speedup** transforms proof development from frustrating trial-and-error into smooth, interactive problem-solving.

## Prerequisites

**Before using LSP tools:**

1. **Build your project first** - The LSP server needs compiled dependencies. Run `coqc` or your build system (dune, make) before starting intensive LSP work to ensure fast startup and avoid timeouts.

2. **Install coq-lsp** - The LSP server implementation:
   - Via opam: `opam install coq-lsp`
   - From source: https://github.com/ejgallego/coq-lsp
   - Verify: `coq-lsp --version` should work

**Without these:** You may experience server timeouts or missing functionality.

## Why Use LSP Tools?

**Versus build-only workflow:**
- **Instant feedback:** < 1 second vs 10-30+ seconds
- **Goal visibility:** See exactly what to prove at each step
- **Integrated search:** Find lemmas without leaving your workflow
- **Real-time diagnostics:** Catch errors as you type
- **No guessing:** Verify before editing, not after building

**General advantages:**
- **Structured data:** Returns typed data structures, not text to parse
- **Integrated:** Single server for all Rocq interactions
- **Reliable:** Consistent error handling, no shell/network failures
- **Fast:** Direct API calls, no subprocess overhead
- **Context-aware:** Maintains file state and proof sessions

**Priority:** Always use LSP tools → Fall back to compilation only for final verification

## Critical Rules

1. **NEVER edit without checking goal state first** (`rocq_get_goals`)
2. **ALWAYS start a proof session before tactics** (`rocq_start_proof`)
3. **Search before guessing** - use `rocq_search` to find lemmas
4. **Check goals between tactics** - see intermediate progress
5. **Test tactics before committing** - verify with `rocq_run_tactic`

## Quick Reference

**Every proof follows this pattern:**

```
1. rocq_start_proof(file, theorem)           # Initialize session
2. rocq_get_goals(session)                   # What to prove?
3. rocq_search(session, "keyword")           # Find relevant lemmas
4. rocq_run_tactic(session, "tactic.")       # Test tactic
5. rocq_get_goals(session)                   # Check progress
6. [Edit file with working tactics]
7. rocq_get_goals(session)                   # Confirm "no goals"
```

**Total time:** < 10 seconds (LSP) vs 30+ seconds per iteration (build-only)

**Measured improvements:**
- Feedback: **30x faster** (< 1s vs 30s)
- Tactic exploration: **Fewer iterations** (test before committing)
- Lemma discovery: **Integrated search** in proof context

**When stuck:**
```
1. rocq_get_goals(session)                   # See exact state
2. rocq_get_premises(session)                # What's available?
3. rocq_search(session, "pattern")           # Find lemmas
```

**Emergency debugging:**
```
1. rocq_get_goals(session)                   # What are goals?
2. rocq_get_file_toc(file)                   # File structure
3. rocq_get_state_at_position(file, line, char) # State at position
```

## Essential Tools

### Tool Summary

| Tool | Purpose | Use For |
|------|---------|---------|
| `rocq_start_proof` | **Start session** | Initialize proof session for a theorem |
| `rocq_get_goals` | **Check goals** | See what remains to prove (use constantly!) |
| `rocq_run_tactic` | **Test tactics** | Execute tactics and see results |
| `rocq_get_premises` | **Find lemmas** | See available premises in context |
| `rocq_search` | **Search** | Find theorems/definitions by pattern |
| `rocq_get_file_toc` | **File structure** | Get all definitions/theorems in file |
| `rocq_get_state_at_position` | **Position query** | Get proof state at specific location |

### 1. `rocq_start_proof` - Initialize Proof Session

**When to use:**
- Before working on ANY theorem
- To begin interactive proof development
- When testing proof strategies

**Parameters:**
- `file_path` (required): Path to `.v` file
- `theorem_name` (required): Name of theorem/lemma to prove

**Example:**
```coq
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  (* Start session for this theorem *)
```

**Call:** `rocq_start_proof("file.v", "add_comm")`

**Returns:** Session ID for subsequent operations

**Important:** You must start a proof session before using other session-based tools.

### 2. `rocq_get_goals` - Check Proof State (USE CONSTANTLY!)

**When to use:**
- Before writing ANY tactic
- After each tactic to see progress
- To understand what remains to be proved
- To confirm proof completion

**Parameters:**
- `session_id` (required): Session from `rocq_start_proof`

**Example:**
```coq
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.  (* <- Check goals after this *)
```

**Call:** `rocq_get_goals(session)`

**Output:**
```
n : nat
m : nat
============================
n + m = m + n
```

**What this tells you:**
- Context: `n : nat, m : nat` (variables in scope)
- Goal: `n + m = m + n` (what you need to prove)
- Now you know exactly what tactic to use!

**Success signal:**
```
No more goals.
```
← Proof complete!

### 3. `rocq_run_tactic` - Execute Tactics

**When to use:**
- To test if a tactic works
- Step-by-step proof development
- Before editing the actual file

**Parameters:**
- `session_id` (required): Session ID
- `tactic` (required): Tactic string to execute (e.g., "intros n m.")

**Example:**
```python
# Test a tactic
result = rocq_run_tactic(session, "intros n m.")

# Check if it worked
goals = rocq_get_goals(session)
```

**Advantages:**
- Test tactics without editing file
- See exact error messages
- Understand why tactics fail
- Build proof incrementally

**Pro tip:** Test multiple tactics in sequence to find the right proof path before editing the file.

### 4. `rocq_get_premises` - Find Available Lemmas

**When to use:**
- Looking for lemmas to apply
- Understanding what's available in context
- Premise selection for automation
- Discovering relevant theorems

**Parameters:**
- `session_id` (required): Session ID

**Example:**
```python
premises = rocq_get_premises(session)

# Find lemmas about addition
for p in premises:
    if "add" in p.name:
        print(f"{p.name}: {p.type}")
```

**Returns:** List of available:
- Hypotheses from context
- Imported lemmas and theorems
- Definitions in scope

**Use case:** Find lemmas to apply, then test with `rocq_run_tactic`.

### 5. `rocq_search` - Search for Declarations

**When to use:**
- Looking for specific lemmas/theorems
- Checking if something exists
- Discovering library functions
- Finding definitions by pattern

**Parameters:**
- `session_id` (required): Session ID
- `query` (required): Search term or pattern

**Example:**
```python
# Search for commutativity lemmas
results = rocq_search(session, "comm")

for r in results:
    print(f"{r.name}: {r.type}")
```

**Pro tip:** Start with broad searches ("add"), then narrow down ("add_comm").

### 6. `rocq_get_file_toc` - Get File Structure

**When to use:**
- Understanding file organization
- Finding all theorems in a file
- Batch processing theorems
- Navigating large files

**Parameters:**
- `file_path` (required): Path to `.v` file

**Example:**
```python
toc = rocq_get_file_toc("MyTheorems.v")

# Find all lemmas
for item in toc:
    if item.kind in ["Lemma", "Theorem"]:
        print(f"{item.name} at line {item.line}")
```

**Returns:**
- All definitions, lemmas, theorems
- Section and module structure
- Line numbers for each item

### 7. `rocq_get_state_at_position` - Position-Based Query

**When to use:**
- IDE integrations (hover, completion)
- Understanding proof state at specific location
- Debugging particular proof steps
- Context-aware assistance

**Parameters:**
- `file_path` (required): Path to `.v` file
- `line` (required): Line number (0-indexed)
- `character` (required): Character offset (0-indexed)

**Example:**
```python
# Get state at line 42
state = rocq_get_state_at_position("file.v", 42, 0)

# What goals exist at this point?
print(state.goals)
```

**Use case:** Position-based proof assistance and IDE features.

## Complete Example: End-to-End Proof

**Task:** Prove `n + m = m + n`

```coq
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  (* We'll develop this proof interactively *)
Admitted.
```

### Step 1: Start proof session
```python
session = rocq_start_proof("file.v", "add_comm")
```

### Step 2: Check initial goal
```python
goals = rocq_get_goals(session)
# Output: forall n m : nat, n + m = m + n
```
**Now you know what to prove!**

### Step 3: Search for relevant lemmas
```python
results = rocq_search(session, "add_comm")
# Finds: Nat.add_comm, plus_comm, etc.
```

### Step 4: Test tactics
```python
# Try introducing variables
result = rocq_run_tactic(session, "intros n m.")
goals = rocq_get_goals(session)
# Output: n : nat, m : nat ⊢ n + m = m + n

# Check if we can apply a lemma
result = rocq_run_tactic(session, "apply Nat.add_comm.")
goals = rocq_get_goals(session)
# Output: No more goals. ✅
```

### Step 5: Edit file with working proof
```coq
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  apply Nat.add_comm.
Qed.
```

### Step 6: Verify completion
```python
goals = rocq_get_goals(session)
# Output: No more goals.
```
**SUCCESS!**

**Total time:** < 10 seconds with absolute certainty

**Build-only would take:** 30+ seconds per try-and-rebuild cycle

## Workflow Patterns

### Pattern 1: Interactive Proof Development
```python
# 1. Start session
session = rocq_start_proof("file.v", "my_theorem")

# 2. Check what to prove
goals = rocq_get_goals(session)

# 3. Search for lemmas
lemmas = rocq_search(session, "relevant_keyword")

# 4. Test tactics one by one
rocq_run_tactic(session, "intros.")
rocq_get_goals(session)  # Check progress

rocq_run_tactic(session, "apply some_lemma.")
rocq_get_goals(session)  # Check again

# 5. When done, edit file with working tactics
```

### Pattern 2: Premise-Driven Proof Search
```python
def find_applicable_lemmas(session):
    """Find lemmas that might help with current goal."""
    premises = rocq_get_premises(session)
    goals = rocq_get_goals(session)

    if not goals:
        return []

    # Try applying each premise
    applicable = []
    for p in premises:
        result = rocq_run_tactic(session, f"apply {p.name}.")
        new_goals = rocq_get_goals(session)

        if len(new_goals) < len(goals):
            applicable.append(p)

    return applicable
```

### Pattern 3: Batch Theorem Analysis
```python
def analyze_file(file_path):
    """Analyze all theorems in a file."""
    toc = rocq_get_file_toc(file_path)

    for item in toc:
        if item.kind in ["Theorem", "Lemma"]:
            print(f"\n{item.name}:")

            # Start session
            session = rocq_start_proof(file_path, item.name)

            # Check initial goal
            goals = rocq_get_goals(session)
            print(f"  Goals: {len(goals)}")

            # Try standard tactics
            for tactic in ["reflexivity.", "auto.", "trivial."]:
                result = rocq_run_tactic(session, tactic)
                if not result.error:
                    goals = rocq_get_goals(session)
                    if not goals:
                        print(f"  ✓ Solved with: {tactic}")
                        break
```

## Common Mistakes to Avoid

❌ **DON'T:**
- Edit → build → see error (too slow!)
- Guess lemma names without searching
- Apply tactics without checking goals first
- Skip intermediate goal checks
- Forget to start proof session

✅ **DO:**
- Start session → check goals → search → test → apply
- Use `rocq_get_goals` constantly
- Test tactics with `rocq_run_tactic` before editing
- Search with `rocq_search` before hallucinating
- Verify intermediate progress

## Troubleshooting

### "No such theorem" errors
**Problem:** `rocq_start_proof` can't find theorem

**Solutions:**
1. Check theorem name is exact (case-sensitive)
2. Use `rocq_get_file_toc` to see available theorems
3. Verify file path is correct

### Session errors
**Problem:** Session ID not valid

**Solutions:**
1. Ensure you called `rocq_start_proof` first
2. Don't reuse session IDs across different theorems
3. Start new session if previous one failed

### Search returns nothing
**Problem:** `rocq_search` returns empty

**Solutions:**
1. Try partial matches: "add" instead of "add_zero"
2. Check if imports are correct
3. Use `rocq_get_premises` to see what's actually available

### Goals not updating
**Problem:** Goals don't change after tactic

**Solutions:**
1. Check tactic syntax (need period at end: "intros.")
2. Verify tactic succeeded (check for errors in result)
3. Tactic might not affect this particular goal

## Advanced: Position-Based Features

### IDE Hover Integration
```python
def get_hover_info(file_path, line, char):
    """Get proof state for IDE hover."""
    state = rocq_get_state_at_position(file_path, line, char)

    if state.goals:
        return f"Goals: {len(state.goals)}\n{state.goals[0]}"
    else:
        return "No goals"
```

### Context-Aware Suggestions
```python
def suggest_tactics(session):
    """Suggest tactics based on current goal."""
    goals = rocq_get_goals(session)
    if not goals:
        return []

    goal = goals[0]
    suggestions = []

    # Pattern-based suggestions
    if "=" in goal:
        suggestions.append("reflexivity.")
    if "forall" in goal or "∀" in goal:
        suggestions.append("intros.")
    if "/\\" in goal:
        suggestions.append("split.")

    return suggestions
```

## Why This Matters

**Without LSP:** You're coding blind, relying on slow build cycles for feedback.

**With LSP:** You have interactive feedback at every step of proof development.

**The transformation:** From "guess and wait" to "see and verify" instantly.

**Measured results:**
- **30x faster feedback** (< 1s vs 30s)
- **Fewer iterations** (test before committing)
- **Better understanding** (see proof state evolution)

**Bottom line:** LSP tools fundamentally change how you develop proofs. Once you experience instant feedback, you'll never want to wait for builds again.

## Best Practices

### Development Workflow

**1. Always use LSP for development:**
- Start session for each theorem
- Check goals constantly
- Test tactics before editing
- Verify with LSP, then compile

**2. Compile before committing:**
```bash
# LSP says OK, but still compile to verify
dune build

# Commit only after compilation succeeds
git commit -m "proof: complete add_comm"
```

**3. Use both LSP and compilation:**
- LSP: fast feedback during development
- Compilation: final verification before commit

### Search Strategy

**1. Start local, go specific:**
```python
# Broad search first
rocq_search(session, "add")

# Narrow down
rocq_search(session, "add_comm")
```

**2. Use premises for context:**
```python
# See what's available right now
premises = rocq_get_premises(session)
```

**3. Test before applying:**
```python
# Don't just edit the file - test first!
result = rocq_run_tactic(session, "apply lemma.")
if not result.error:
    # Now edit file
```

## See Also

- [tactics-reference.md](tactics-reference.md) - Rocq tactics guide
- [compilation-errors.md](compilation-errors.md) - Debug with LSP hints
- [coq-lsp GitHub](https://github.com/ejgallego/coq-lsp) - LSP server repository
