# Porting Status: Lean 4 → Rocq

This document tracks the migration of the Lean 4 theorem proving plugin to Rocq/Coq.

## Summary

**Completed:** 15 files (~11,000 lines)
- ✅ Core skill (SKILL.md)
- ✅ 10 reference guides
- ✅ 3 commands (build, fill-admit, golf-proofs)
- ✅ README.md, plugin.json

**Missing:** 16 files (automation infrastructure)

---

## 1. Commands

### Completed ✅

| Command | Status | Notes |
|---------|--------|-------|
| `build-rocq` | ✅ Complete | Adapted from `build-lean.md`, uses `dune build` |
| `fill-admit` | ✅ Complete | Adapted from `fill-sorry.md`, searches stdlib/MathComp |
| `golf-proofs` | ✅ Complete | Adapted from `golf-proofs.md`, includes SSReflect patterns |

### Intentionally Skipped ⏭️

| Command | Reason | Alternative |
|---------|--------|-------------|
| `analyze-sorries` | User requested skip | Use `/fill-admit` for individual admits |
| `search-mathlib` | User requested skip | Use stdlib Search commands directly |

### Missing TODOs 🔴

| Command | Priority | Lean 4 Version | Rocq Adaptation Needed |
|---------|----------|----------------|------------------------|
| `check-axioms` | **HIGH** | Checks axiom usage in proofs | Adapt to use `Print Assumptions` command |
| `clean-warnings` | MEDIUM | Removes unused variables/imports | Adapt to Coq warning messages |

**TODO: check-axioms command**
- **Purpose:** Verify proof doesn't use unnecessary axioms
- **Implementation:**
  ```bash
  # Rocq/Coq command:
  coqtop -q -batch -l file.v -e "Print Assumptions theorem_name."
  ```
- **Notes:** Critical for verifying constructive proofs, checking `Classical` usage
- **Priority:** HIGH (axiom hygiene is critical)

**TODO: clean-warnings command**
- **Purpose:** Remove unused variables, simplify imports
- **Implementation:** Parse Coq warnings, suggest removals
- **Notes:** Lower priority, manual cleanup usually sufficient
- **Priority:** MEDIUM

---

## 2. Scripts (Automation)

### All Scripts Missing 🔴

The Lean 4 plugin has 16 automation scripts in `scripts/`. **None have been ported yet.**

| Script | Priority | Purpose | Rocq Adaptation Strategy |
|--------|----------|---------|--------------------------|
| **Core Automation** ||||
| `analyze_sorries.py` | LOW | Find and categorize sorry locations | Adapt for `admit`/`Admitted`, but skipped per user |
| `extract_typeclass_info.py` | **HIGH** | Extract typeclass instances | Adapt for Coq typeclasses (Show Instances, Print Canonical) |
| `fill_admit_with_search.py` | **HIGH** | Auto-fill admits using search | Use `Search`, `SearchPattern`, `SearchAbout` |
| `search_mathlib.sh` | LOW | Search mathlib | Adapt for stdlib/MathComp, but skipped per user |
| **Proof Optimization** ||||
| `golf_proof_auto.py` | MEDIUM | Automated proof golfing | Port patterns from `proof-golfing.md` |
| `simplify_proof.py` | MEDIUM | Simplify tactic sequences | Detect `simpl; reflexivity` → `reflexivity` |
| `inline_single_use_asserts.py` | MEDIUM | Remove single-use asserts | SSReflect: detect `assert` → inline |
| **Error Analysis** ||||
| `categorize_errors.py` | **HIGH** | Parse and categorize build errors | Adapt for Coq error messages (typeclass, universe, etc.) |
| `suggest_fixes.py` | **HIGH** | Suggest fixes for errors | Use patterns from `compilation-errors.md` |
| `fix_imports.py` | MEDIUM | Auto-fix missing imports | Parse "not found" errors, add `Require Import` |
| **Axiom Management** ||||
| `check_axioms.py` | **HIGH** | Verify axiom hygiene | Use `Print Assumptions`, check against whitelist |
| `suggest_axiom_elimination.py` | MEDIUM | Suggest axiom removal strategies | Use patterns from `axiom-elimination.md` |
| **Build Optimization** ||||
| `optimize_build_order.py` | LOW | Optimize file compilation order | Dune handles this automatically |
| `parallel_build_advisor.py` | LOW | Suggest parallelization | Dune: `dune build -j4` |
| **Quality Checks** ||||
| `proof_quality_metrics.py` | LOW | Measure proof metrics (lines, tactics, etc.) | Adapt for Coq syntax |
| `unused_lemmas.py` | LOW | Find unused lemmas | Parse Coq warnings |

### Priority Breakdown

**HIGH Priority (5 scripts)** - Core functionality
- `extract_typeclass_info.py` - Typeclass debugging is critical in Coq
- `fill_admit_with_search.py` - High-value automation
- `categorize_errors.py` - Essential for workflow
- `suggest_fixes.py` - Essential for workflow
- `check_axioms.py` - Axiom hygiene verification

**MEDIUM Priority (6 scripts)** - Nice to have
- Proof optimization scripts (golf, simplify, inline)
- `fix_imports.py` - Helpful but manual work is feasible
- `suggest_axiom_elimination.py` - Complements manual workflow

**LOW Priority (5 scripts)** - Marginal benefit
- Build optimization (Dune handles this)
- Quality metrics (manual inspection works)
- Search scripts (already skipped per user)

### Implementation Notes

**Coq-specific adaptations needed:**

1. **Error message parsing:**
   - Lean 4: JSON output
   - Rocq: Text output, different format
   - Need custom parsers for Coq error messages

2. **Typeclass system:**
   - Lean 4: `#check` for instances
   - Rocq: `Print Canonical Projections`, `About [instance]`
   - Different typeclass inference behavior

3. **Library search:**
   - Lean 4: mathlib search, `exact?`
   - Rocq: `Search`, `SearchPattern`, no direct equivalent to `exact?`
   - Need to parse Search output

4. **Build system:**
   - Lean 4: `lake`
   - Rocq: `dune`, `coq_makefile`, or `coqc`
   - Scripts must detect and support multiple build systems

5. **Syntax:**
   - Lean 4: Different proof syntax
   - Rocq: Both standard Coq and SSReflect styles
   - Scripts must handle both styles

---

## 3. Hooks

### All Hooks Missing 🔴

| Hook | Priority | Purpose | Rocq Adaptation |
|------|----------|---------|-----------------|
| `bootstrap.sh` | **HIGH** | Setup script for plugin initialization | Adapt for Rocq environment, check `coqc`/`dune` |
| `hooks.json` | **HIGH** | Hook configuration | Define Rocq-specific hooks |

**TODO: bootstrap.sh**
- **Purpose:** Verify Rocq installation, setup environment
- **Checks needed:**
  - `coqc --version` (Rocq/Coq available?)
  - `dune --version` (Build system available?)
  - `opam list | grep coq-lsp` (LSP available?)
  - Python dependencies for scripts
- **Priority:** HIGH (required for plugin to function)

**TODO: hooks.json**
- **Purpose:** Define when commands run automatically
- **Examples:**
  - Run `check-axioms` before commit
  - Run `build-rocq` on save
  - Suggest `fill-admit` when cursor on admit
- **Priority:** HIGH (improves UX significantly)

---

## 4. Documentation

### Completed ✅

| Document | Status | Notes |
|----------|--------|-------|
| `SKILL.md` | ✅ Complete | Core skill adapted, ~800 lines |
| `README.md` | ✅ Complete | Full plugin documentation |
| **References** (10 files) |||
| `rocq-phrasebook.md` | ✅ Complete | Math → Rocq translations, ~5800 lines |
| `tactics-reference.md` | ✅ Complete | 40+ tactics with examples, ~850 lines |
| `compilation-errors.md` | ✅ Complete | Error debugging guide, ~450 lines |
| `stdlib-guide.md` | ✅ Complete | Stdlib + ecosystem, ~650 lines |
| `ssreflect-patterns.md` | ✅ Complete | SSReflect style guide, ~550 lines |
| `domain-patterns.md` | ✅ Complete | Domain-specific patterns, ~550 lines |
| `proof-golfing.md` | ✅ Complete | Optimization patterns, ~600 lines |
| `admit-filling.md` | ✅ Complete | Admit completion strategies, ~550 lines |
| `axiom-elimination.md` | ✅ Complete | Axiom removal guide, ~500 lines |
| `rocq-lsp-server.md` | ✅ Complete | LSP setup guide, ~500 lines |

### Missing TODOs 🔴

| Document | Priority | Purpose | Notes |
|----------|----------|---------|-------|
| `COMMANDS.md` | MEDIUM | Command listing and usage | List all commands, when to use each |
| `FUTURE-FEATURES.md` | LOW | Roadmap | Future enhancements planned |
| `TESTING.md` | MEDIUM | Testing guide | How to test plugin functionality |
| `calc-patterns.md` | LOW | Calculation mode patterns | Rocq has limited calc support |
| `subagent-workflows.md` | LOW | When to use subagents | Agent orchestration patterns |

**TODO: COMMANDS.md**
- **Purpose:** Quick reference for all commands
- **Content:** List all commands, examples, when to use
- **Priority:** MEDIUM (helpful but README covers most)

**TODO: FUTURE-FEATURES.md**
- **Purpose:** Document planned enhancements
- **Content:** Automation scripts, advanced features, LSP integration
- **Priority:** LOW (not blocking current functionality)

**TODO: scripts/TESTING.md**
- **Purpose:** Testing methodology for scripts
- **Content:** How to test automation, edge cases, regression tests
- **Priority:** MEDIUM (important when scripts are implemented)

**TODO: calc-patterns.md**
- **Purpose:** Step-by-step calculation proofs
- **Content:** Rocq's limited calc mode, alternatives
- **Notes:** Coq has less support than Lean 4 for calc-style proofs
- **Priority:** LOW (can use standard rewriting)

**TODO: subagent-workflows.md**
- **Purpose:** When to delegate to subagents
- **Content:** Multi-file refactoring, large-scale analysis
- **Priority:** LOW (advanced usage)

---

## 5. Implementation Roadmap

### Phase 1: Core Automation (Recommended Next) 🎯

**Goal:** Get basic automation working

1. **check-axioms command** (1-2 hours)
   - Implement using `Print Assumptions`
   - Parse output, check against whitelist
   - Report custom axioms

2. **categorize_errors.py** (2-3 hours)
   - Parse dune/coqc error output
   - Categorize: typeclass, universe, type mismatch, etc.
   - Output structured error list

3. **suggest_fixes.py** (3-4 hours)
   - Use patterns from `compilation-errors.md`
   - Match error types to fix suggestions
   - Generate fix candidates

4. **bootstrap.sh** (1 hour)
   - Check Rocq/Coq installation
   - Verify dune/coqc available
   - Setup Python environment

5. **hooks.json** (1 hour)
   - Define basic hooks
   - Auto-run check-axioms before commit
   - Suggest fill-admit on cursor

**Total Phase 1:** ~10 hours

### Phase 2: Search & Fill Automation

**Goal:** Automated admit filling

1. **extract_typeclass_info.py** (2-3 hours)
   - Parse `Print Canonical Projections`
   - Extract instance information
   - Suggest missing instances

2. **fill_admit_with_search.py** (4-6 hours)
   - Use Search/SearchPattern
   - Parse search results
   - Generate proof candidates
   - Test candidates automatically

3. **fix_imports.py** (2-3 hours)
   - Parse "not found" errors
   - Search for identifier location
   - Add `Require Import` statements

**Total Phase 2:** ~10 hours

### Phase 3: Proof Optimization

**Goal:** Automated proof golfing

1. **golf_proof_auto.py** (4-5 hours)
   - Detect patterns from `proof-golfing.md`
   - Apply transformations
   - Test each optimization
   - Revert if compilation fails

2. **simplify_proof.py** (2-3 hours)
   - Remove unnecessary tactics
   - Combine tactic sequences
   - SSReflect optimizations

3. **inline_single_use_asserts.py** (2-3 hours)
   - Detect single-use asserts
   - Inline where beneficial
   - Preserve readability

**Total Phase 3:** ~10 hours

### Phase 4: Quality & Polish

**Goal:** Documentation and nice-to-haves

1. **COMMANDS.md** (1 hour)
2. **TESTING.md** (2 hours)
3. **clean-warnings command** (2-3 hours)
4. Remaining low-priority scripts (optional)

**Total Phase 4:** ~5 hours

---

## 6. Key Differences: Lean 4 vs Rocq

### Terminology Mapping

| Lean 4 | Rocq/Coq | Notes |
|--------|----------|-------|
| `sorry` | `admit` / `Admitted` | Incomplete proofs |
| `lake` | `dune` / `coq_makefile` | Build systems |
| mathlib | stdlib / MathComp | Standard libraries |
| `#check` | `Check` / `About` | Type inspection |
| `exact?` | Search commands | No direct equivalent |
| `simp` | `simpl` / `by []` | Simplification |
| `rw` | `rewrite` | Rewriting |
| calc mode | Limited support | Coq less ergonomic |

### Ecosystem Differences

**Lean 4:**
- Single standard library (mathlib)
- Unified tactic language
- Modern LSP with excellent tooling
- Fast compilation
- JSON error output

**Rocq/Coq:**
- Multiple libraries (stdlib, MathComp, ExtLib, etc.)
- Two major styles (standard + SSReflect)
- LSP improving (coq-lsp)
- Slower compilation
- Text-based error output
- Richer universe system (Prop/Set/Type)
- More mature ecosystem (30+ years)

### Implications for Porting

1. **Scripts must handle both Coq and SSReflect syntax**
2. **Error parsing is harder (no structured output)**
3. **Library search more fragmented**
4. **Build system detection needed (Dune vs coq_makefile vs coqc)**
5. **Typeclass system works differently (canonical structures)**

---

## 7. Testing Strategy

### Manual Testing (Current)

✅ All documentation tested manually:
- SKILL.md reviewed for accuracy
- Reference guides verified against Coq documentation
- Command workflows validated against typical use cases

### Automated Testing (TODO)

When scripts are implemented:

1. **Unit tests** (Python pytest)
   - Error parsing
   - Search result parsing
   - Fix suggestion generation

2. **Integration tests** (Bash scripts)
   - End-to-end command execution
   - Build → fix → verify cycle
   - Admit filling workflow

3. **Example projects** (Small Coq projects)
   - Software Foundations examples
   - MathComp examples
   - Custom test cases

4. **Regression tests**
   - Known error cases
   - Edge cases from real usage

See `scripts/TESTING.md` (TODO) for full testing guide.

---

## 8. Maintenance Notes

### When Updating Lean 4 Plugin

If the Lean 4 plugin adds new features:

1. **Review additions:**
   - New commands?
   - New scripts?
   - New reference docs?

2. **Evaluate applicability:**
   - Does this apply to Rocq?
   - Need adaptation or skip?

3. **Update this file:**
   - Add to TODO list with priority
   - Note adaptation strategy

4. **Consider roadmap:**
   - High priority → add to Phase 1
   - Low priority → defer

### When Rocq/Coq Changes

If Rocq/Coq ecosystem evolves:

1. **Major version updates:**
   - Update `rocq-lsp-server.md`
   - Test all commands
   - Update error patterns

2. **New libraries:**
   - Update `stdlib-guide.md`
   - Add to search strategies

3. **New tactics:**
   - Update `tactics-reference.md`
   - Update `rocq-phrasebook.md`

---

## 9. Contributing

### Adding Missing Components

**Priority order:**
1. HIGH priority items (core automation)
2. MEDIUM priority items (quality of life)
3. LOW priority items (nice to have)

**Implementation checklist:**
- [ ] Implement core functionality
- [ ] Add tests (unit + integration)
- [ ] Update documentation
- [ ] Test with real Coq projects
- [ ] Update this PORTING.md (move from TODO to ✅)

### Style Guide for Scripts

**Follow Lean 4 plugin conventions:**
- Python 3.8+ for scripts
- Type hints for clarity
- Docstrings for all functions
- CLI interface using `argparse`
- Exit codes: 0 (success), 1 (error), 2 (warnings)

**Coq-specific conventions:**
- Support both standard Coq and SSReflect
- Detect and handle multiple build systems
- Parse text output robustly
- Provide clear error messages

---

## 10. Questions & Decisions

### Open Questions

1. **Automation scripts:** Implement in Python (like Lean 4) or use OCaml (native Coq ecosystem)?
   - **Recommendation:** Python (easier to maintain, matches Lean 4 structure)

2. **Build system priority:** Focus on Dune only or support all three (Dune, coq_makefile, coqc)?
   - **Recommendation:** Dune primary, detect others, basic support for coq_makefile

3. **SSReflect:** Treat as first-class or secondary style?
   - **Recommendation:** First-class (include in all automation and docs)

4. **Library focus:** Prioritize stdlib or MathComp?
   - **Recommendation:** Both (stdlib for basics, MathComp for algebra/analysis)

### Design Decisions Made

✅ **Build system:** Dune assumed by default (per user request)
✅ **Skip commands:** analyze-sorries, search-mathlib (per user request)
✅ **Documentation first:** Complete all reference guides before scripts
✅ **Dual style:** Support both standard Coq and SSReflect equally

---

## Summary

**Completed:** Core documentation (15 files, ~11,000 lines)
- All essential reference guides
- 3 core commands
- Plugin infrastructure

**Missing:** Automation layer (16 scripts + hooks)
- HIGH priority: 5 scripts + check-axioms command + hooks
- MEDIUM priority: 6 scripts + 3 docs
- LOW priority: 5 scripts + 2 docs

**Estimated effort to complete:**
- Phase 1 (core automation): ~10 hours
- Phase 2 (search & fill): ~10 hours
- Phase 3 (optimization): ~10 hours
- Phase 4 (polish): ~5 hours
- **Total:** ~35 hours to full parity with Lean 4 plugin

**Recommendation:** Prioritize Phase 1 (core automation) for maximum impact with minimal effort.

---

**Last updated:** 2025-01-XX
**Status:** Documentation complete, automation pending
