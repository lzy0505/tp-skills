# Common Compilation Errors in Lean 4

This reference provides detailed explanations and fixes for the most common compilation errors encountered in Lean 4 theorem proving.

## Quick Reference Table

| Error | Cause | Fix |
|-------|-------|-----|
| **"failed to synthesize instance"** | Missing type class | Add `haveI : IsProbabilityMeasure μ := ⟨proof⟩` |
| **"maximum recursion depth"** | Type class loop/complex search | Provide manually: `letI := instance` or increase: `set_option synthInstance.maxHeartbeats 40000` |
| **"type mismatch"** (has type ℕ but expected ℝ) | Wrong type | Use coercion: `(x : ℝ)` or `↑x` |
| **"tactic 'exact' failed"** | Goal/term type mismatch | Use `apply` for unification or restructure: `⟨h.2, h.1⟩` |
| **"unknown identifier 'ring'"** | Missing import | Add: `import Mathlib.Tactic.Ring` |
| **"equation compiler failed"** | Can't prove termination | Add `termination_by my_rec n => n` clause |

## Detailed Error Explanations

### 1. Failed to Synthesize Instance

**Full error message:**
```
failed to synthesize instance
  IsProbabilityMeasure μ
```

**What it means:** Lean cannot automatically infer the required type class instance.

**Common scenarios:**
- Working with sub-σ-algebras: `m ≤ m₀` but Lean can't infer instances on `m`
- Trimmed measures: `μ.trim hm` needs explicit `SigmaFinite` instance
- Conditional expectations requiring multiple measure properties

**Solutions:**

**Pattern 1: Explicit instance declaration**
```lean
haveI : IsProbabilityMeasure μ := ⟨measure_univ⟩
haveI : IsFiniteMeasure μ := inferInstance
haveI : SigmaFinite (μ.trim hm) := sigmaFinite_trim μ hm
```

**Pattern 2: Using Fact for inequalities**
```lean
have h_le : m ≤ m₀ := ...
haveI : Fact (m ≤ m₀) := ⟨h_le⟩
```

**Pattern 3: Explicit instance passing**
```lean
@condExp Ω ℝ m₀ m (by exact inst) μ (by exact hm) f
```

**Debug with:**
```lean
set_option trace.Meta.synthInstance true in
theorem my_theorem : Goal := by
  apply_instance
```

### 2. Maximum Recursion Depth

**Full error message:**
```
(deterministic) timeout at 'typeclass', maximum number of heartbeats (20000) has been reached
```

**What it means:** Type class synthesis is stuck in a loop or the search is too complex.

**Common causes:**
- Circular instance dependencies
- Very deep instance search trees
- Ambiguous instances competing

**Solutions:**

**Solution 1: Provide instance manually**
```lean
letI : MeasurableSpace Ω := m₀  -- Freeze the instance
-- Now Lean won't search
```

**Solution 2: Increase search limit**
```lean
set_option synthInstance.maxHeartbeats 40000 in
theorem my_theorem : Goal := ...
```

**Solution 3: Check for instance loops**
```lean
-- ❌ BAD: Creates loop
instance [Foo A] : Bar A := ...
instance [Bar A] : Foo A := ...

-- ✅ GOOD: One-directional
instance [Foo A] : Bar A := ...
```

### 3. Type Mismatch

**Full error message:**
```
type mismatch
  x
has type
  ℕ
but is expected to have type
  ℝ
```

**What it means:** The term's type doesn't match what's expected.

**Common scenarios:**
- Natural number used where real number expected
- Integer used where rational expected
- General coercion needed

**Solutions:**

**Pattern 1: Explicit coercion**
```lean
-- Natural to real
(n : ℝ)  -- Preferred
↑n       -- Alternative

-- Integer to real
(z : ℝ)

-- Custom coercion
⟨x, hx⟩ : {x : ℝ // x > 0}
```

**Pattern 2: Check actual types**
```lean
#check x        -- See current type
#check (x : ℝ)  -- Verify coercion works
```

**Pattern 3: Function application**
```lean
-- If f : ℝ → ℝ and n : ℕ
f ↑n    -- Apply after coercion
f (n : ℝ)  -- Explicit
```

### 4. Tactic 'exact' Failed

**Full error message:**
```
tactic 'exact' failed, type mismatch
  term
has type
  A → B
but is expected to have type
  ∀ x, A x → B x
```

**What it means:** The term's type is close but not exactly the goal type.

**Solutions:**

**Solution 1: Use apply instead**
```lean
-- exact doesn't work but apply might
apply my_lemma
-- Leaves subgoals to fill
```

**Solution 2: Restructure term**
```lean
-- Wrong order
exact ⟨h.1, h.2⟩  -- Type mismatch

-- Correct order
exact ⟨h.2, h.1⟩  -- Works
```

**Solution 3: Add intermediate steps**
```lean
-- Instead of: exact complex_term
have h1 := part1
have h2 := part2
exact ⟨h1, h2⟩
```

### 5. Unknown Identifier (Missing Tactic)

**Full error message:**
```
unknown identifier 'ring'
```

**What it means:** Tactic not imported.

**Common missing imports:**
```lean
import Mathlib.Tactic.Ring          -- ring, ring_nf
import Mathlib.Tactic.Linarith      -- linarith, nlinarith
import Mathlib.Tactic.FieldSimp     -- field_simp
import Mathlib.Tactic.Continuity    -- continuity
import Mathlib.Tactic.Measurability -- measurability
import Mathlib.Tactic.Positivity    -- positivity
```

**Quick fix:**
1. See error for tactic name
2. Add `import Mathlib.Tactic.TacticName`
3. Rebuild

### 6. Equation Compiler Failed (Termination)

**Full error message:**
```
fail to show termination for
  my_recursive_function
with errors
  ...
```

**What it means:** Lean can't automatically prove the function terminates.

**Solutions:**

**Pattern 1: Add termination_by clause**
```lean
def my_rec (n : ℕ) : ℕ :=
  if n = 0 then 0
  else my_rec (n - 1)
termination_by n  -- Decreasing argument
```

**Pattern 2: Well-founded recursion**
```lean
def my_rec (l : List α) : Result :=
  match l with
  | [] => base_case
  | h :: t => combine h (my_rec t)
termination_by l.length
```

**Pattern 3: Use sorry for termination proof**
```lean
def my_rec (x : X) : Y := ...
termination_by measure_func x
decreasing_by sorry  -- TODO: Prove later
```

## Quick Debug Workflow

When encountering any error:

1. **Read error location carefully** - Often points to exact issue
2. **Use #check** - Verify types of all terms involved
3. **Simplify** - Try to create minimal example that fails
4. **Search mathlib** - Error might be documented in lemma comments
5. **Ask Zulip** - Lean community is very helpful

## Type Class Debugging Commands

```lean
-- See synthesis trace
set_option trace.Meta.synthInstance true in
theorem test : Goal := by apply_instance

-- See which instance was chosen
#check (inferInstance : IsProbabilityMeasure μ)

-- Check all implicit arguments
#check @my_lemma
```

## Common Patterns to Avoid

### ❌ Fighting the Type Checker

```lean
-- Repeatedly trying variations until something compiles
exact h
exact h.1
exact ⟨h⟩
exact (h : _)  -- Guessing
```

### ✅ Understanding Then Fixing

```lean
#check h  -- See what h actually is
#check goal  -- See what's needed
-- Now fix systematically
```

### ❌ Ignoring Error Messages

```lean
-- "It says type mismatch, let me try random things"
```

### ✅ Reading Carefully

```lean
-- Error says "has type A but expected B"
-- Solution: Convert A to B or restructure
```
