# Lean LSP Server Reference

**The Lean LSP server provides instant feedback for interactive theorem development.**

This reference documents the battle-tested workflow and tools for Lean 4 proof development using the Lean LSP MCP server.

**Key insight from field testing:** LSP tools provide instant feedback (< 1 second) versus build cycles (10-30+ seconds). This **30x speedup** transforms proof development from frustrating trial-and-error into smooth, interactive problem-solving.

## Prerequisites

**Before using LSP tools:**

1. **Run `lake build` first** - The LSP server runs `lake serve` which can timeout during initial project build. Run `lake build` manually in your project directory before starting the MCP server to ensure fast startup and avoid timeouts.

2. **Install ripgrep** - Required for `lean_local_search` (the most-used search tool):
   - macOS: `brew install ripgrep`
   - Linux: `apt install ripgrep` or https://github.com/BurntSushi/ripgrep#installation
   - Windows: https://github.com/BurntSushi/ripgrep#installation
   - Verify: `rg --version` should work

**Without these:** You may experience server timeouts or missing search functionality.

## Why Use LSP Tools?

**Versus build-only workflow:**
- **Instant feedback:** < 1 second vs 10-30+ seconds
- **Goal visibility:** See exactly what to prove at each step
- **Parallel testing:** Test multiple tactics at once with `lean_multi_attempt`
- **Integrated search:** Find lemmas without leaving your workflow
- **No guessing:** Verify before editing, not after building

**General advantages:**
- **Structured data:** Returns typed data structures, not text to parse
- **Integrated:** Single server for all Lean interactions
- **Reliable:** Consistent error handling, no shell/network failures
- **Fast:** Direct API calls, no subprocess overhead
- **Context-aware:** Maintains file state, handles rate limits

**Priority:** Always use LSP tools → Fall back to scripts only if LSP unavailable

## Critical Rules

1. **NEVER edit without checking goal state first** (`lean_goal`)
2. **ALWAYS check diagnostics after edits** (don't wait for build)
3. **Search before guessing** - use `lean_local_search` FIRST (fast & unlimited!)
4. **Check goals between tactics** - see intermediate progress
5. **Use `lean_multi_attempt` liberally** - test multiple tactics at once
6. **Respect rate limits** - `lean_local_search` is unlimited, others are 3 req/30s

## Quick Reference

**Every proof follows this pattern:**

```
1. lean_goal(file, line)                    # What to prove?
2. lean_local_search("keyword", limit=10)   # Does it exist?
3. lean_multi_attempt(file, line, [         # Test tactics
     "  simp", "  omega", "  apply lemma"
   ])
4. [Edit file with winner]
5. lean_diagnostic_messages(file)           # Verify
6. lean_goal(file, line)                    # Confirm "no goals"
```

**Total time:** < 10 seconds (LSP) vs 30+ seconds per iteration (build-only)

**Measured improvements:**
- Feedback: **30x faster** (< 1s vs 30s)
- Tactic exploration: **4x fewer iterations** (parallel testing)
- Lemma discovery: **10x faster** (integrated search)

**When stuck:**
```
1. lean_goal(file, line)              # See exact state
2. lean_loogle("pattern")             # Type search
3. lean_leansearch("description")     # Natural language
4. lean_state_search(file, line, col) # Proof state
```

**Emergency debugging:**
```
1. lean_diagnostic_messages(file)     # What errors?
2. lean_hover_info(file, line, col)   # What's the type?
3. lean_goal(file, line)              # What are goals?
```

## Essential Tools

### Tool Categories

**Local tools (unlimited, instant):**
- Direct LSP queries against your project files
- No rate limits, < 1 second response time
- Tools: `lean_goal`, `lean_local_search`, `lean_multi_attempt`, `lean_diagnostic_messages`, `lean_hover_info`

**External tools (rate-limited to 3 req/30s):**
- Remote API calls to loogle.lean-lang.org, leansearch.net
- Managed by LSP server to avoid overwhelming services
- Tools: `lean_loogle`, `lean_leansearch`, `lean_state_search`

**Best practice:** Always use local tools first (especially `lean_local_search`), then external tools only when local search doesn't find what you need.

### Tool Summary

| Tool | Type | Rate Limit | Speed | Use For |
|------|------|------------|-------|---------|
| `lean_goal` | **Local** | None | Instant | See goals (always!) |
| `lean_local_search` | **Local** | None | Instant | Find lemmas (use first!) |
| `lean_multi_attempt` | **Local** | None | Instant | Test tactics in parallel |
| `lean_diagnostic_messages` | **Local** | None | Instant | Check errors |
| `lean_hover_info` | **Local** | None | Instant | Check syntax/types |
| `lean_loogle` | **External** | 3/30s (LSP managed) | Fast | Type patterns |
| `lean_leansearch` | **External** | 3/30s (LSP managed) | Slower | Natural language |
| `lean_state_search` | **External** | 3/30s (LSP managed) | Fast | Proof state |

**Rate limit note:** External tools call remote APIs (loogle.lean-lang.org, leansearch.net). The LSP server automatically manages rate limiting to 3 requests per 30 seconds for all external tools combined.

### 1. `lean_goal` - Check Proof State (USE CONSTANTLY!)

**When to use:**
- Before writing ANY tactic
- After each tactic to see progress
- To understand what remains to be proved

**Parameters:**
- `file_path` (required): Absolute path to Lean file
- `line` (required): Line number (1-indexed)
- `column` (optional): Usually omit - shows both before/after line

**Example:**
```lean
lemma test_add_comm (n m : ℕ) : n + m = m + n := by
  sorry  -- <- Check goal here (line 12)
```

**Call:** `lean_goal(file, line=12)`

**Output:**
```
Goals on line:
lemma test_add_comm (n m : ℕ) : n + m = m + n := by
Before:
No goals at line start.
After:
n m : ℕ
⊢ n + m = m + n
```

**What this tells you:**
- Context: `n m : ℕ` (variables in scope)
- Goal: `⊢ n + m = m + n` (what you need to prove)
- Now you know exactly what tactic to search for!

**Pro tip:** Call `lean_goal` on a line WITH a tactic to see before/after states - shows exactly what that tactic accomplishes.

**Success signal:**
```
After:
no goals
```
← Proof complete!

### 2. `lean_diagnostic_messages` - Instant Error Checking

**When to use:** After EVERY edit, before building

**Advantage:** Instant (< 1s) vs build (10-30s)

**Example - Errors found:**
```
lean_diagnostic_messages(file)
→ ["l13c9-l13c17, severity: 1\nUnknown identifier `add_comm`",
   "l20c30-l20c49, severity: 1\nFunction expected at StrictMono"]
```
- Line 13, columns 9-17: `add_comm` not in scope
- Line 20, columns 30-49: Syntax error with `StrictMono`
- Severity 1 = error, Severity 2 = warning

**Example - Success:**
```
lean_diagnostic_messages(file)
→ []
```
← Empty array = no errors!

**Critical:** Empty diagnostics means no errors, but doesn't mean proof complete. Always verify with `lean_goal` to confirm "no goals".

### 3. `lean_local_search` - Find Declarations (USE FIRST!)

**Why use this FIRST:**
- ✅ **Unlimited** - no rate limits
- ✅ **Instant** - fastest search option
- ✅ **Comprehensive** - searches workspace + mathlib
- ✅ **Structured** - returns name/kind/file

**When to use:**
- Checking if a declaration exists before hallucinating
- Finding project-specific lemmas
- Understanding what's available

**Parameters:**
- `query` (required): Search term (e.g., "add_zero", "StrictMono")
- `limit` (optional): Max results (default 10)

**Example:**
```
lean_local_search("add_zero", limit=5)
→ [{"name": "add_zero", "kind": "theorem", "file": "Init/Grind/Ring/Envelope.lean"},
   {"name": "add_zero", "kind": "theorem", "file": "Init/Grind/Module/Envelope.lean"}]
```

**Pro tip:** Start with partial matches. Search "add" to see all addition-related lemmas.

**Requires:** ripgrep installed and in PATH
- macOS: `brew install ripgrep`
- Linux: `apt install ripgrep` or see https://github.com/BurntSushi/ripgrep#installation
- Windows: See https://github.com/BurntSushi/ripgrep#installation

**If not installed:** The tool will fail with an error. Install ripgrep to enable fast local search.

### 4. `lean_multi_attempt` - Parallel Tactic Testing (GAME CHANGER!)

**This is the most powerful workflow tool.** Test multiple tactics at once and see EXACTLY why each succeeds or fails:

**Example 1: Choosing between working tactics**
```
lean_multi_attempt(file, line=13, snippets=[
  "  simp [Nat.add_comm]",
  "  omega",
  "  apply Nat.add_comm"
])

→ Output:
["  simp [Nat.add_comm]:\n no goals\n\n",
 "  omega:\n no goals\n\n",
 "  apply Nat.add_comm:\n no goals\n\n"]
```
All work! Pick simplest: `omega`

**Example 2: Learning from failures**
```
lean_multi_attempt(file, line=82, snippets=[
  "  exact Nat.lt_succ_self n",
  "  apply Nat.lt_succ_self",
  "  simp"
])

→ Output:
["  exact Nat.lt_succ_self n:\n Unknown identifier `n`",
 "  apply Nat.lt_succ_self:\n Could not unify...",
 "  simp:\n no goals\n\n"]
```
**Key insight:** Errors tell you WHY tactics fail - `n` out of scope, wrong unification, etc.

**Example 3: Multi-step tactics (single line)**
```
lean_multi_attempt(file, line=97, snippets=[
  "  intro i j hij; exact hij",
  "  intro i j; exact id",
  "  unfold StrictMono; simp"
])
```
Chain tactics with `;` - still single line!

**Use cases:**
- A/B test 3-5 candidate tactics
- Understand why approaches fail (exact error messages)
- Compare clarity/directness
- Explore proof strategies

**Critical constraints:**
- **Single-line snippets only** - no multi-line proofs
- **Must be fully indented** - `"  omega"` not `"omega"`
- **No comments** - avoid `--` in snippets
- **For testing only** - edit file properly after choosing

**Workflow:**
1. `lean_goal` to see what you need
2. Think of 3-5 candidate tactics
3. Test ALL with `lean_multi_attempt`
4. Pick winner, edit file
5. Verify with `lean_diagnostic_messages`

### 5. `lean_hover_info` - Get Documentation

**When to use:**
- Unsure about function signature
- Need to see implicit arguments
- Want to check type of a term
- Debugging syntax errors

**Parameters:**
- `file_path` (required)
- `line` (required)
- `column` (required): Must point to START of identifier

**Example:**
```
lean_hover_info(file, line=20, column=30)
→ Shows definition, type, diagnostics at that location
```

**Pro tip:** Use hover on error locations for detailed information about what went wrong.

## External Search Tools (Rate-Limited)

**Use these when `lean_local_search` doesn't find what you need.**

These tools call external APIs (loogle.lean-lang.org, leansearch.net). The **LSP server rate-limits all external tools to 3 requests per 30 seconds** to avoid overwhelming the services.

**Why rate-limited:** These tools make HTTP requests to external services, not your local Lean project. The LSP server manages the rate limiting automatically.

### `lean_loogle` - Type Pattern Search

**Best for:** You know input/output types but not the name

**Example:**
```
lean_loogle("(?a -> ?b) -> List ?a -> List ?b", num_results=5)
→ Returns: List.map, List.mapIdx
```

**Type pattern syntax:**
- `?a`, `?b`, `?c` - Type variables
- `_` - Wildcards
- `->` or `→` - Function arrow
- `|- pattern` - Search by conclusion

**Most useful patterns:**
- By type shape: `(?a -> ?b) -> List ?a -> List ?b` ✅
- By constant: `Real.sin`
- By subexpression: `_ * (_ ^ _)`

**IMPORTANT:** Loogle searches by *type structure*, not names.
- ❌ `"Measure.map"` - no results
- ✅ `"Measure ?X -> (?X -> ?Y) -> Measure ?Y"` - finds Measure.map

**Decision tree:**
```
Know exact name? → lean_local_search
Know concept/description? → lean_leansearch
Know input/output types? → lean_loogle ✅
```

### `lean_leansearch` - Natural Language Search

**Best for:** Conceptual/description-based search

**Query patterns:**
- Natural language: "Cauchy Schwarz inequality"
- Mixed: "natural numbers. from: n < m, to: n + 1 < m + 1"
- Lean identifiers: "List.sum", "Finset induction"

**Example:**
```
lean_leansearch("Cauchy Schwarz inequality", num_results=5)
```

### `lean_state_search` - Proof State Search

**Best for:** Finding lemmas that apply to your current proof state

**Use when stuck on a specific goal.**

## Complete Example: End-to-End Proof

**Task:** Prove `n + m = m + n`

```lean
lemma test_add_comm (n m : ℕ) : n + m = m + n := by
  sorry
```

### Step 1: Check goal (ALWAYS FIRST!)
```
lean_goal(file, line=12)
→ Output:
After:
n m : ℕ
⊢ n + m = m + n
```
**Now you know exactly what to prove!**

### Step 2: Search for lemmas
```
lean_local_search("add_comm", limit=5)
→ [{"name": "add_comm", "kind": "theorem", ...}]
```
**Found it! But let's test multiple approaches...**

### Step 3: Test tactics in parallel
```
lean_multi_attempt(file, line=13, snippets=[
  "  simp [Nat.add_comm]",
  "  omega",
  "  apply Nat.add_comm"
])
→ All three show "no goals" ✅
```
**Pick simplest: `omega`**

### Step 4: Edit file
```lean
lemma test_add_comm (n m : ℕ) : n + m = m + n := by
  omega
```

### Step 5: Verify immediately
```
lean_diagnostic_messages(file)
→ []  ← No errors!
```

### Step 6: Confirm completion
```
lean_goal(file, line=13)
→ After:
no goals
```
**SUCCESS! 🎉**

**Total time:** < 10 seconds with absolute certainty

**Build-only would take:** 30+ seconds per try-and-rebuild cycle

**Advanced tip:** When you don't know how to prove a definition (like `StrictMono`), use `lean_hover_info` to see the expanded form, then test tactics against the unfolded goal.

## Common Mistakes to Avoid

❌ **DON'T:**
- Edit → build → see error (too slow!)
- Guess lemma names without searching
- Apply tactics blind without checking goal
- Use rate-limited search when `lean_local_search` works
- Skip intermediate goal checks in multi-step proofs

✅ **DO:**
- Check goal → search (local first!) → test → apply → verify
- Use `lean_multi_attempt` to explore tactics
- Verify with `lean_diagnostic_messages` after every edit
- Check intermediate goals after each tactic
- Respect rate limits

## Troubleshooting

### "Unknown identifier" errors
**Problem:** `add_comm` not found

**Solutions:**
1. Try qualified name: `Nat.add_comm`
2. Use `lean_local_search` to find correct name
3. Try tactic instead: `omega` or `simp`

### "Function expected" with type classes
**Problem:** `StrictMono Nat.succ` fails

**Solution:** Add type annotation: `StrictMono (Nat.succ : ℕ → ℕ)`

### Search finds nothing
**Problem:** `lean_local_search` returns empty

**Solutions:**
1. Try partial matches: `"add"` instead of `"add_zero"`
2. Use wildcards in loogle: `"_ + 0"`
3. Try natural language: `lean_leansearch("addition with zero")`

### Multi-attempt shows all failures
**Check:**
1. Proper indentation? Include leading spaces
2. Correct line number? Point to tactic line
3. Single-line only? Multi-line not supported

### Empty diagnostics but proof incomplete
**Problem:** `[]` diagnostics but not done

**Solution:** Check `lean_goal` - if goals remain, need more tactics

**Key insight:** Empty diagnostics = no errors, but proof may be incomplete. Always verify goals.

## Why This Matters

**Without LSP:** You're coding blind, relying on slow build cycles for feedback.

**With LSP:** You have the same interactive feedback loop as a human using Lean InfoView.

**The transformation:** From "guess and wait" to "see and verify" instantly.

**Measured results:**
- **30x faster feedback** (< 1s vs 30s)
- **4x fewer iterations** (parallel testing)
- **10x faster discovery** (integrated search)

**Bottom line:** LSP tools fundamentally change how you develop proofs. Once you experience instant feedback, you'll never want to wait for builds again.
