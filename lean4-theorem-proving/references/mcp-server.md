# Lean MCP Server Reference

The Lean MCP (Model Context Protocol) server provides powerful tools for interactive theorem development in Lean 4. This reference documents the most important tools and common workflows.

## Why Use MCP Tools?

**General advantages of MCP tools over script-based alternatives:**
- **Structured data:** Returns typed data structures, not text to parse
- **Integrated:** Single server for all Lean interactions
- **Reliable:** Consistent error handling, no shell/network failures
- **Fast:** Direct API calls, no subprocess overhead
- **Context-aware:** Server maintains file state and handles rate limits

**Priority:** Always prefer MCP tools when available → Fall back to scripts if MCP unavailable

## Essential Tools

### 1. `lean_goal` - Check Proof State (VERY USEFUL!)

Shows current goals, hypotheses, and proof state at a specific location.

**When to use:**
- Before writing a `sorry` to see what needs to be proved
- After a tactic to see if it made progress
- To understand proof state evolution

**Parameters:**
- `file_path` (required): Absolute path to Lean file
- `line` (required): Line number (1-indexed)
- `column` (optional): Column number (1-indexed)

**Best practices:**
- **Avoid giving column if unsure** - default behavior works well (shows both before and after line)
- Check VERY OFTEN - it's the main tool to understand proof state
- To see goal at `sorry`, use cursor before the "s", not after

**Example:**
```json
{
  "file_path": "/path/to/MyTheorem.lean",
  "line": 150
}
```

### 2. `lean_diagnostic_messages` - Get All Compilation Errors

Returns all diagnostic messages (errors, warnings, infos) for a file.

**When to use:**
- Understanding compilation errors
- Checking if file compiles cleanly
- Finding all issues in a file at once

**Special messages:**
- "no goals to be solved" means code may need removal

**Example:**
```json
{
  "file_path": "/path/to/MyTheorem.lean"
}
```

### 3. `lean_hover_info` - Get Documentation

Get hover information (docs for syntax, variables, functions, etc.) at a specific location.

**When to use:**
- Understanding unfamiliar terms or tactics
- Checking type signatures
- Reading documentation

**Important:** Column must be at the start or within the term, not at the end.

**Example:**
```json
{
  "file_path": "/path/to/MyTheorem.lean",
  "line": 42,
  "column": 10
}
```

## Search and Discovery Tools

### 4. `lean_local_search` - Find Declarations in Your Project (VERY FAST!)

Searches for declarations in the current workspace.

**What it searches:**
- Theorems, lemmas, definitions
- Classes, instances, structures
- Inductives, abbrevs, opaque declarations

**When to use:**
- Checking if a declaration exists before hallucinating
- Finding project-specific lemmas
- Understanding project structure

**Best practices:**
- Pass a short prefix (e.g., "map_mul")
- Returns metadata: name, declaration kind, file location
- Much faster than grepping

**Requires:** ripgrep installed (`brew install ripgrep`)

**Example:**
```json
{
  "query": "map_mul",
  "limit": 10
}
```

### 5. `lean_leansearch` - Search Mathlib with Natural Language

Search for Lean theorems and definitions using natural language.

**Rate limit:** 3 requests per 30 seconds

**Query patterns:**
- Natural language: "If there exist injective maps of sets from A to B and from B to A, then there exists a bijective map between A and B"
- Mixed natural/Lean: "natural numbers. from: n < m, to: n + 1 < m + 1"
- Concept names: "Cauchy Schwarz"
- Lean identifiers: "List.sum", "Finset induction"
- Lean term: `{f : A → B} {g : B → A} (hf : Injective f) (hg : Injective g) : ∃ h, Bijective h`

**Example:**
```json
{
  "query": "Cauchy Schwarz inequality",
  "num_results": 5
}
```

### 6. `lean_loogle` - Search by Type Signature (**KILLER FEATURE**)

Search for definitions and theorems using type patterns.

**Rate limit:** 3 requests per 30 seconds

**Why use MCP `lean_loogle` over `smart_search.sh --source=loogle`:**

✅ **Structured output:** Returns `List[dict]` with name/kind/file, not text that needs parsing
✅ **Integrated:** Same server providing `lean_goal`, `lean_diagnostic_messages`, etc.
✅ **Reliable:** No curl/network failures, consistent error handling
✅ **Fast:** Direct API call, no shell subprocess overhead
✅ **Rate limiting:** Transparently managed by the MCP server

**When to use `smart_search.sh` instead:**
- MCP server unavailable (fallback)
- Need to search multiple sources in one script (`--source=all`)
- Custom filtering/formatting requirements

**Key insight:** Loogle excels at type-based search when you know what goes in/out but not the exact name.

**IMPORTANT:** Simple name searches often fail:
```json
// ❌ These DON'T work
{"query": "Measure.map"}          // No results (not a type pattern)
{"query": "IsProbabilityMeasure"} // No results (searches by type structure)
```

**Why:** Loogle searches by *type structure*, not text. For name searches, use `lean_leansearch` or `lean_local_search`.

**✅ Type pattern queries (what DOES work):**

```json
// Find map function: (?a -> ?b) -> List ?a -> List ?b
{"query": "(?a -> ?b) -> List ?a -> List ?b", "num_results": 5}
// Returns: List.map, List.mapIdx ✅

// Find measure pushforward
{"query": "Measure ?X -> (?X -> ?Y) -> Measure ?Y", "num_results": 5}
// Returns: Measure.map and related ✅

// Find measurable composition
{"query": "Measurable ?f -> Measurable ?g -> Measurable (?g ∘ ?f)", "num_results": 5}
// Returns: Measurable.comp ✅
```

**Query pattern syntax:**

- **Type variables:** `?a`, `?b`, `?c` - Match any type
- **Wildcards:** `_` - Match any term
- **Function arrow:** `->` or `→`
- **Conclusion:** `|-` prefix (what the theorem proves)

**Query patterns:**
- **By type shape:** `(?a -> ?b) -> List ?a -> List ?b` ✅ **MOST USEFUL**
- **By constant:** `Real.sin` - finds lemmas mentioning Real.sin
- **By lemma name:** `"differ"` - finds lemmas with "differ" in name (less reliable)
- **By subexpression:** `_ * (_ ^ _)` - finds lemmas with product and power
- **Non-linear:** `Real.sqrt ?a * Real.sqrt ?a`
- **By conclusion:** `|- tsum _ = _ * tsum _`
- **By conclusion with hyps:** `|- _ < _ → tsum _ < tsum _`

**When to use loogle:**

```
Know what you need?
├─ Know exact name? → lean_local_search
├─ Know concept/description? → lean_leansearch
└─ Know input/output types? → lean_loogle ✅ THIS!
```

**Example:**
```json
{
  "query": "(?a -> ?b) -> List ?a -> List ?b",
  "num_results": 8
}
```

### 7. `lean_state_search` - Find Theorems from Proof State

Search for theorems based on your current proof state.

**Rate limit:** 3 requests per 30 seconds

**When to use:**
- Stuck at a specific goal
- Need lemma that applies to current situation

**Note:** Only uses first goal if multiple exist

**Example:**
```json
{
  "file_path": "/path/to/file.lean",
  "line": 100,
  "column": 5,
  "num_results": 5
}
```

### 8. `lean_hammer_premise` - Get Relevant Premises

Search for premises based on proof state using the lean hammer.

**Rate limit:** 3 requests per 30 seconds

**When to use:**
- Need to find relevant lemmas for current goal
- Building intuition for what might apply

**Example:**
```json
{
  "file_path": "/path/to/file.lean",
  "line": 100,
  "column": 5,
  "num_results": 32
}
```

## Code Inspection Tools

### 9. `lean_file_contents` - Read Lean File

Get text contents of a Lean file, optionally with line numbers.

**Best practice:** ALWAYS use this to read Lean files instead of regular file reading tools.

**Example:**
```json
{
  "file_path": "/path/to/file.lean",
  "annotate_lines": true
}
```

### 10. `lean_declaration_file` - Find Symbol Declaration

Get the file contents where a symbol/lemma/class/structure is declared.

**Prerequisites:**
- Symbol must be present in the file
- Use `lean_hover_info` before this tool to confirm symbol exists

**Note:** Lean files can be large - use `lean_hover_info` first to decide if you need the full file.

**Example:**
```json
{
  "file_path": "/path/to/current_file.lean",
  "symbol": "Continuous"
}
```

### 11. `lean_completions` - Get Code Completions

Get code completions at a location.

**ONLY use on INCOMPLETE lines/statements** to check available identifiers and imports.

**Completion types:**
- Dot completion: Displays relevant identifiers after a dot (e.g., `Nat.`, `x.`)
- Identifier completion: Suggests matching identifiers after part of a name
- Import completion: Lists importable files after `import` at file beginning

**Example:**
```json
{
  "file_path": "/path/to/file.lean",
  "line": 10,
  "column": 15,
  "max_completions": 32
}
```

### 12. `lean_term_goal` - Get Expected Type

Get the expected type (term goal) at a specific location.

**When to use:**
- Understanding what term is needed at a position
- Filling in `_` placeholders

**Example:**
```json
{
  "file_path": "/path/to/file.lean",
  "line": 50,
  "column": 20
}
```

## Advanced Tools

### 13. `lean_multi_attempt` - Try Multiple Tactics in Parallel

Try multiple Lean code snippets at a line and get goal state and diagnostics for each.

**When to use:**
- Compare tactics or approaches
- **Use rarely** - prefer direct file edits to keep users involved

**Important constraints:**
- Only single-line, fully-indented snippets supported
- Avoid comments for best results
- For a single snippet, edit file and run `lean_diagnostic_messages` instead

**Example:**
```json
{
  "file_path": "/path/to/file.lean",
  "line": 75,
  "snippets": [
    "  exact my_lemma h",
    "  apply my_lemma; exact h",
    "  simp [my_lemma]"
  ]
}
```

### 14. `lean_run_code` - Run Standalone Code

Run a complete, self-contained code snippet and return diagnostics.

**Must include:**
- All imports
- All definitions

**When to use:**
- Testing outside open files
- **Keep user in loop** by editing files instead

**Example:**
```json
{
  "code": "import Mathlib.Data.Nat.Basic\nexample : 1 + 1 = 2 := by rfl"
}
```

### 15. `lean_build` - Build Project and Restart LSP

Build the Lean project and restart the LSP server.

**When to use:**
- New imports added
- Build artifacts out of date
- **Use only if needed** - can take a long time

**Parameters:**
- `lean_project_path` (optional): Inferred from previous calls
- `clean` (optional): Run `lake clean` first - **ONLY USE IF NECESSARY!** (very slow)

**Example:**
```json
{
  "clean": false
}
```

## Common Workflows

### Starting a New Proof

1. Use `lean_goal` to see what needs to be proved
2. Use `lean_local_search` to check for project lemmas
3. Use `lean_leansearch` or `lean_loogle` to find relevant mathlib lemmas
4. Edit the file with tactics
5. Check `lean_diagnostic_messages` for errors
6. Use `lean_goal` again to see progress
7. Repeat until complete

### Finding the Right Lemma

**Decision tree:**

```
Need a lemma?
├─ Is it in your project?
│  └─ Use lean_local_search (fast, no rate limit!)
│
├─ Know the exact name?
│  └─ Use lean_local_search or grep
│
├─ Know what types go in/out but not the name?
│  └─ Use lean_loogle with type pattern ✅ POWERFUL!
│     Example: "(?a -> ?b) -> List ?a -> List ?b" finds List.map
│
├─ Know the concept/description?
│  └─ Use lean_leansearch with natural language
│     Example: "Cauchy Schwarz inequality"
│
├─ Stuck at specific goal?
│  └─ Use lean_state_search (uses current proof state)
│
└─ Need relevant premises?
   └─ Use lean_hammer_premise (suggests applicable lemmas)
```

**Rate limit management:**
- **No limit:** `lean_local_search` ← Start here!
- **3 requests per 30 seconds (shared pool):**
  - `lean_leansearch`
  - `lean_loogle`
  - `lean_state_search`
  - `lean_hammer_premise`

**Strategy:**
1. Always try `lean_local_search` first (project lemmas, no rate limit)
2. If you know input/output types → `lean_loogle` (type patterns)
3. If you know concept → `lean_leansearch` (natural language)
4. If stuck at goal → `lean_state_search` or `lean_hammer_premise`

**Real-world example:**

```
Problem: Need function to transform List α to List β using (α → β)

❌ Don't: lean_loogle "List.map"  # Simple name search fails
✅ Do: lean_loogle "(?a -> ?b) -> List ?a -> List ?b"  # Type pattern succeeds!

Result: List.map, List.mapIdx, etc.
```

### Debugging Compilation Errors

1. Run `lean_diagnostic_messages` on the file
2. Identify error location from diagnostics
3. Use `lean_goal` at the error line to see proof state
4. Use `lean_hover_info` on unfamiliar terms
5. Check if imports are out of date (may need `lean_build`)
6. Fix error, check diagnostics again

### Understanding Proof State Evolution

**Best practice workflow:**

```lean
-- At line 100: theorem start
lean_goal(file, line=100)  -- See initial goal

-- At line 105: after first tactic
lean_goal(file, line=105)  -- See what changed

-- At line 110: after second tactic
lean_goal(file, line=110)  -- See further progress

-- At line 115: before sorry
lean_goal(file, line=115)  -- See what remains
```

**Check often!** Every 3-5 lines in complex proofs.

## Important Notes

### Line and Column Indexing

- **All line and column numbers are 1-indexed**
- Use `lean_file_contents` with `annotate_lines: true` if unsure
- Column numbers: count from start of line (1 = first character)

### File Editing

- The MCP server **does NOT make permanent file changes**
- Use other tools (Edit, Write) for file modifications
- MCP server is for **reading and analyzing** only

### Working Iteratively

**Best practices:**
- Small steps
- Intermediate sorries with documented strategy
- Frequent checks with `lean_goal` and `lean_diagnostic_messages`
- Build incrementally, not all at once

### Tool-Specific Tips

**`lean_goal` column parameter:**
- **Avoid guessing** - omit to see both before and after line
- Default behavior works well for most cases
- Specify column only when you need precise position

**`lean_hover_info` column parameter:**
- Must be at start or within term
- **Not at the end** of the term
- Example: For `my_lemma`, column should be at 'm', not after 'a'

## Performance Tips

### Before Starting Interactive Work

```bash
# ALWAYS run lake build first
lake build

# This ensures:
# - All imports are up to date
# - LSP server has current build artifacts
# - Faster MCP responses
```

### Search Tool Performance

- `lean_local_search`: **Very fast** (local ripgrep search)
- `lean_leansearch`, `lean_loogle`, etc.: **Rate limited** (external services)

**Strategy:** Check local first, then external.

### Large Files

- `lean_file_contents` may truncate large files
- Use `offset` and `limit` parameters to read in chunks
- Check file size before full read

### Build Performance

- `lean_build` without `clean`: Minutes
- `lean_build` with `clean: true`: **Much longer** (rebuilds everything)
- Only use `clean: true` when:
  - Corrupted build artifacts
  - Strange compilation errors that don't make sense
  - Last resort debugging

## Troubleshooting

### "Imports are out of date"

**Solution:**
1. Use `lean_build` tool
2. Or run `lake build` manually
3. Restart LSP server

### "ripgrep not found"

**Solution:**
```bash
brew install ripgrep  # macOS
# or apt install ripgrep  # Linux
# then restart MCP server
```

### Build Timeouts

**Prevention:**
- Always run `lake build` manually before starting MCP work
- Don't rely on MCP to handle initial build

**If it happens:**
- Cancel MCP operation
- Run `lake build` in terminal
- Resume MCP work after build completes

### Files Won't Compile

**Check:**
1. Run `lean_diagnostic_messages` to see all errors
2. Use `lean_build` to refresh
3. If strange errors persist, may need `lake clean && lake build` (slow!)

**Common causes:**
- Out of date imports (fix: `lean_build`)
- Corrupted build artifacts (fix: `lake clean && lake build`)
- Syntax errors (fix: check diagnostics)

### Rate Limit Errors

**If you hit rate limits:**
- Wait 30 seconds before next request
- Use `lean_local_search` instead (not rate limited)
- Plan searches to minimize external queries

**Rate-limited tools (3 req/30s):**
- `lean_leansearch`
- `lean_loogle`
- `lean_state_search`
- `lean_hammer_premise`

## Integration with Skill Workflow

### Phase 1: Structure Before Solving

Use MCP to understand goals:
```
1. lean_goal - See what needs to be proved
2. Identify subgoals
3. Create structure with documented sorries
4. Use lean_diagnostic_messages to verify structure compiles
```

### Phase 2: Helper Lemmas First

Use MCP to find building blocks:
```
1. lean_local_search - Check project lemmas
2. lean_leansearch - Find mathlib lemmas
3. Implement helpers
4. lean_diagnostic_messages to verify
```

### Phase 3: Incremental Filling

Use MCP to track progress:
```
1. Pick one sorry
2. lean_goal to see what's needed
3. Search for relevant lemmas
4. Fill sorry
5. lean_diagnostic_messages to verify
6. Repeat
```

### Phase 4: Managing Type Class Issues

Use MCP to debug:
```
1. lean_diagnostic_messages shows "failed to synthesize instance"
2. lean_goal shows context
3. lean_hover_info on problematic terms
4. Add haveI/letI declarations
5. Verify with lean_diagnostic_messages
```

## Summary: Tool Selection

| Need to... | Use... |
|------------|--------|
| See current proof state | `lean_goal` (VERY USEFUL!) |
| Check all errors | `lean_diagnostic_messages` |
| Understand a term | `lean_hover_info` |
| Find project lemma | `lean_local_search` |
| Find mathlib by concept | `lean_leansearch` |
| Find by type signature | `lean_loogle` |
| Find for current goal | `lean_state_search` |
| Get relevant premises | `lean_hammer_premise` |
| Read file with line numbers | `lean_file_contents` |
| Find declaration source | `lean_declaration_file` |
| Build project | `lean_build` |

**Most important:** `lean_goal` - use it often to understand proof evolution!
