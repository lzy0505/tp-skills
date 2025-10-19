# check_axioms.sh Testing Findings

**Date:** 2025-10-19
**Project:** exchangeability-cursor

## Test Results

### Files Tested
1. ✅ Exchangeability/DeFinetti/ViaL2.lean - Found 38 declarations
2. ✅ Exchangeability/Core.lean - Found 40 declarations

### Issues Discovered

#### Critical Limitation: Namespaced Declarations Not Accessible

**Problem:**
The script generates an external Lean file that imports the target module and runs `#print axioms` on each declaration. However, declarations inside namespaces, sections, or marked as `private` cannot be accessed via import.

**Error Example:**
```
error(lean.unknownIdentifier): Unknown constant `window`
error(lean.unknownIdentifier): Unknown constant `prefixProj`
```

Even though these declarations exist in the files, they're not in the exported API.

**Root Cause:**
```lean
-- In Core.lean
namespace Foo
  def prefixProj ...  -- ❌ Not accessible as Exchangeability.Core.prefixProj
end Foo

private def window ...  -- ❌ Not accessible at all from outside
```

### Bugs Fixed During Testing

1. **mktemp pattern** - Changed from `/tmp/check_axioms_XXXXX.lean` to `mktemp` (let system choose)
2. **Bash 3.2 compatibility** - Removed `declare -A` (associative arrays) for macOS compatibility
3. **Empty array handling** - Fixed `set -u` issues with `${ARRAY[@]+"${ARRAY[@]}"}`
4. **Regex pattern** - Changed from grep -P to grep -E + sed for portability

### What Works

**Declaration extraction:**
```bash
✅ Regex correctly finds theorem/lemma/def declarations
✅ Successfully extracted 38 declarations from ViaL2.lean
✅ Successfully extracted 40 declarations from Core.lean
✅ Module name conversion works (path → import)
✅ Temp file generation works
✅ Lean compilation initiated correctly
```

**What Doesn't Work:**
```bash
❌ Accessing namespaced declarations
❌ Accessing private declarations
❌ Accessing section-scoped declarations
```

## Alternative Approaches

### Option 1: In-File Axiom Checking
Instead of external imports, append to the original file:

```bash
# At end of file being checked
cat >> MyFile.lean <<'EOF'
#print axioms theorem1
#print axioms theorem2
EOF
lake env lean MyFile.lean
# Then remove the appended lines
```

**Pros:** Can access all declarations
**Cons:** Modifies source files temporarily

### Option 2: Manual Per-Theorem Checking
User-facing workflow:

```bash
# In the Lean file itself
#print axioms my_theorem_name
```

**Pros:** Simple, always works
**Cons:** Manual, no batching

### Option 3: Restrict to Public API Only
Document that the script only works for exported declarations.

**Pros:** Current implementation works
**Cons:** Limited usefulness for development files

### Option 4: Use Lean's JSON Output
```bash
lake env lean --json MyFile.lean
```

**Pros:** Structured output, better parsing
**Cons:** More complex implementation, still has namespace issues

## Recommendation

For v2.1.0, **document the limitation** clearly:

```markdown
**Note:** This script only works for declarations that are part of the module's
public API. Declarations in namespaces, sections, or marked `private` cannot be
checked via external import.

For checking all declarations (including internal ones), use #print axioms
directly in your Lean files.
```

**For v2.2.0, consider:**
- Implementing Option 1 (in-file checking with temp modifications)
- Or simplifying to a wrapper that helps with manual checking

## Scripts Status Summary

After testing:

| Script | Status | Notes |
|--------|--------|-------|
| search_mathlib.sh | ✅ **Working** | Successfully finds lemmas |
| sorry_analyzer.py | ✅ **Working** | Successfully extracts sorries with context |
| check_axioms.sh | ⚠️ **Limited** | Works only for public API declarations |

## Test Output Examples

### sorry_analyzer.py (SUCCESS)
```
Found 10 sorry statement(s)

[1] Exchangeability/DeFinetti/ViaKoopman.lean:1825
    Documentation:
      • TODO: Once birkhoffAverage_tendsto_condexp_L2 is proved...
    In: theorem condexp_tower_for_products
```

### search_mathlib.sh (SUCCESS)
```
File: .lake/packages/mathlib/Mathlib/Probability/CondVar.lean
103:lemma condVar_ae_eq_condExp_sq_sub_sq_condExp
```

### check_axioms.sh (LIMITATION FOUND)
```
Found 38 declarations
error: Unknown constant `window`
```

## Conclusion

The check_axioms.sh script has a fundamental architectural limitation that makes it unsuitable for checking internal declarations in Lean files. Two of three scripts work perfectly; one needs redesign or clear limitation documentation.

**Recommendation:** Ship v2.1.0 with current scripts, document check_axioms limitations, and plan redesign for v2.2.0.
