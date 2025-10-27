---
description: Fast search for existing lemmas in mathlib to avoid reproving standard results
allowed-tools: Bash(bash:*)
---

# Mathlib Lemma Search

Quick search for existing lemmas, theorems, and definitions in mathlib before reproving standard results.

## Core Principle

**ALWAYS search mathlib before proving anything!**

Time saved by finding existing lemma: 5 minutes
Time wasted reproving something that exists: 30-60 minutes

**IMPORTANT:** Search scripts are bundled with this plugin - do not look for them in the current directory. Always use the full path with ${CLAUDE_PLUGIN_ROOT}.

## Workflow

### 1. Understand What You Need

**Ask clarifying questions if query is vague:**
```
What are you looking for?
- Type signature (e.g., "continuous function on compact space")
- Lemma name pattern (e.g., "continuous.*compact")
- Specific property (e.g., "image of compact set is compact")
- General topic (e.g., "conditional expectation properties")

Describe what you need: [wait for user]
```

### 2. Choose Search Strategy

**Based on query type:**

**A) Know approximate name:**
```bash
bash "$LEAN4_SEARCH_MATHLIB" "<pattern>" name
```
Example: `continuous_compact` → finds `Continuous.isCompact_image`

**Fallback:** Use Grep to search local mathlib if cloned, or use WebFetch with mathlib docs

**B) Know type signature pattern:**
```bash
bash "$LEAN4_SMART_SEARCH" "<type pattern>" --source=loogle
```
Example pattern: `(?f : ?α → ?β) → Continuous ?f → IsCompact ?s → IsCompact (?f '' ?s)`

**Fallback:** Use WebFetch to loogle API directly with the type pattern

**C) Natural language description:**
```bash
bash "$LEAN4_SMART_SEARCH" "<description>" --source=leansearch
```
Example: "continuous functions preserve compactness"

**Fallback:** Use WebFetch to leansearch API directly with the description

**D) Specific mathematical property:**
```bash
bash "$LEAN4_SEARCH_MATHLIB" "<math_term>" content
```
Example: `conditional expectation tower property`

**Fallback:** Use Grep to search local mathlib content if available

Replace angle-bracketed placeholders with actual search queries.

### 3. Run Search

**Present search command to user:**
```
Searching mathlib for: [query]
Strategy: [name/type/content/semantic]
Source: [local/leansearch/loogle]

Running: [exact command]
```

**Execute and show results:**
```
Found [N] results:

Top matches:
1. [lemma_name]
   Type: [signature]
   Import: [module_path]

2. [lemma_name]
   Type: [signature]
   Import: [module_path]

3. [lemma_name]
   Type: [signature]
   Import: [module_path]

[If N > 10]:
... and [N-10] more results
```

### 4. Evaluate Results

**For each result, provide context:**

a) **Check applicability:**
```
Result #1: [lemma_name]

Matches your need? [yes/no/maybe]
Reason: [brief analysis]

Type signature:
  [full signature with parameter names]

This lemma says: [plain English explanation]

Import path: [full import]
```

b) **Suggest refinement if no good matches:**
```
No exact matches found for: [original query]

Closest matches were about: [topic]

Try refining search:
1. More specific: [refined query 1]
2. More general: [refined query 2]
3. Different angle: [refined query 3]

Which refinement? (1/2/3/custom/give-up)
```

### 5. Help with Import and Usage

**If good match found:**

a) **Add import:**
```
I'll add this import to your file:

import [full_import_path]

Location: [suggest where in file to add it]

Add import? (yes/no)
```

b) **Generate usage example:**
```
How to use [lemma_name]:

#check [lemma_name]  -- Verify it's available

example (f : α → β) (hf : Continuous f) (s : Set α) (hs : IsCompact s) :
    IsCompact (f '' s) :=
  [lemma_name] hf hs

Apply to your proof? I'll adapt it to your specific context.
(yes/show-my-context-first/no)
```

c) **Adapt to user's context:**
```
Reading your proof context...

Your goal: [current goal from file]
Your hypotheses: [relevant hypotheses]

Here's how to apply [lemma_name]:

[specific application to their goal]

Try this? (yes/tweak-it/search-more)
```

### 6. Track Search History

**For complex proofs needing multiple lemmas:**
```
Mathlib Search Session

Lemmas found so far:
1. ✓ [lemma1] - Added to imports
2. ✓ [lemma2] - Applied at line [N]
3. ⏳ [lemma3] - Still evaluating
4. ✗ [lemma4] - Didn't fit our use case

Current need: [what we're searching for now]

Total searches: [N]
Successful finds: [M]
Time saved: ~[estimate] minutes
```

## Search Modes

### Mode 1: Quick Name Search (Fastest)

**When:** You know roughly what the lemma is called

```bash
./scripts/search_mathlib.sh "continuous.*compact" name
```

**Pros:**
- Fastest (grep-based)
- Works offline
- No rate limits

**Cons:**
- Need to guess naming convention
- May miss lemmas with different names

### Mode 2: Semantic Search (Most Intuitive)

**When:** You can describe what you need in natural language

```bash
./scripts/smart_search.sh "continuous functions on compact spaces" --source=leansearch
```

**Pros:**
- No need to know Lean syntax
- Finds conceptually related lemmas
- Best for exploration

**Cons:**
- Requires internet
- Rate limited (~3 requests/30 seconds)
- May return conceptually related but technically different results

### Mode 3: Type Pattern Search (Most Precise)

**When:** You know the type signature structure

```bash
./scripts/smart_search.sh "(?f : ?α → ?β) → Continuous ?f → IsCompact (?f '' ?s)" --source=loogle
```

**Pros:**
- Exact type matching
- Finds lemmas you might not know exist
- Good for refactoring (finding lemmas matching specific signature)

**Cons:**
- Need to know Lean type syntax
- Rate limited (~3 requests/30 seconds)
- Requires internet

### Mode 4: Content Search (Most Comprehensive)

**When:** Searching by mathematical concept or technique

```bash
./scripts/search_mathlib.sh "monotone convergence" content
```

**Pros:**
- Finds lemmas using specific techniques
- Good for discovering related results
- Works offline

**Cons:**
- Slower (searches file contents)
- More false positives
- Need to know mathematical terminology

## Common Search Patterns

### Pattern 1: Building Proof Step by Step

```
1. /search-mathlib "continuous function"
   → Find: Continuous f

2. /search-mathlib "compact image"
   → Find: IsCompact (f '' s)

3. /search-mathlib "continuous compact image"
   → Find: Continuous.isCompact_image (combines both!)

Lesson: Search for composition of properties!
```

### Pattern 2: Unknown Lemma Name

```
User: "I need to prove image of compact set under continuous function is compact"

Search sequence:
1. Natural language: "continuous compact image"
2. Check results for import paths
3. Add import and use #check to verify
4. Apply in proof
```

### Pattern 3: Type-Driven Discovery

```
User: "I have `f : α → β`, `Continuous f`, and `s : Set α`"
User: "What can I prove about `f '' s`?"

Search: Use type pattern to discover available lemmas
Results show: isCompact_image, isClosed_image, etc.
```

## Error Handling

**If no results found:**
```
No results for: [query]

This might mean:
1. Lemma exists with different name (try variations)
2. Lemma exists with different generality (try more general search)
3. Lemma truly doesn't exist in mathlib (you'll need to prove it!)

Next steps:
- Try search variations: [suggestion 1], [suggestion 2]
- Check mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Ask on Lean Zulip if you think it should exist

Try variation or give up? (variation/docs/zulip/give-up)
```

**If rate limited:**
```
⚠️ Rate limited by [leansearch/loogle]

Limit: ~3 requests per 30 seconds

Options:
1. Wait 30 seconds and retry
2. Use local search (--source=mathlib)
3. Try different search strategy

What would you like to do? (wait/local/different)
```

**If import path unclear:**
```
Found lemma but import path unclear from search results.

Let me check mathlib docs for [lemma_name]...

Import path: [determined from docs]

Would you like me to add this import? (yes/no)
```

## Integration with Other Commands

**With /fill-sorry:**
```
When filling a sorry:
1. /search-mathlib to find needed lemmas
2. Add imports
3. Apply lemmas in proof
4. Verify with /build-lean
```

**With /analyze-sorries:**
```
For each documented sorry:
1. Extract required lemma description from TODO
2. /search-mathlib for that lemma
3. Update sorry documentation with found lemmas
4. Fill sorry using found lemmas
```

## Best Practices

✅ **Do:**
- Search before proving ANYTHING
- Try multiple search strategies
- Use specific search for known patterns
- Use semantic search for exploration
- Verify found lemmas with #check before using

❌ **Don't:**
- Assume mathlib doesn't have it
- Give up after one search
- Forget to add imports
- Use lemmas without checking their types
- Skip reading lemma documentation

## Advanced Tips

**Tip 1: Use mathlib naming conventions**
```
Pattern: [type].[property]_[operation]
Examples:
  - Continuous.isCompact_image
  - Measurable.integral_eq
  - IsProbabilityMeasure.measure_univ
```

**Tip 2: Search for dual/opposite**
```
Can't find: "surjective implies has right inverse"
Try: "right inverse implies surjective" (might be easier to find)
```

**Tip 3: Search by field**
```
Need topology result: Search with "continuous", "compact", "open", "closed"
Need measure theory: Search with "measurable", "integral", "measure"
Need probability: Search with "probability", "expectation", "independent"
```

**Tip 4: Use imports to navigate**
```
Found lemma in: Mathlib.Topology.Compactness.Compact
Explore that file for related lemmas about compactness
```

## Related Commands

- `/fill-sorry` - Use found lemmas to fill incomplete proofs
- `/analyze-sorries` - Check which sorries need mathlib searches
- `/check-axioms` - Verify you're not accidentally axiomatizing something mathlib has

## References

- [mathlib-guide.md](../references/mathlib-guide.md) - Detailed search strategies
- [scripts/README.md](../scripts/README.md#search_mathlibsh) - Tool documentation
- [Mathlib docs](https://leanprover-community.github.io/mathlib4_docs/) - Official documentation
