---
name: rocq-theorem-proving
description: Use when developing Rocq/Coq proofs, facing typeclass resolution errors, managing admits/axioms, or searching standard library/MathComp - provides build-first workflow, instance management patterns, and domain-specific tactics
---

# Rocq Theorem Proving

## Core Principle

**Build incrementally, structure before solving, trust the type checker.** Rocq's type checker is your test suite.

**Success = `dune build` passes + zero admits + zero custom axioms.** Theorems with admits/axioms are scaffolding, not results.

## Quick Reference

| **Resource** | **What You Get** | **Where to Find** |
|--------------|------------------|-------------------|
| **Interactive Commands** | 7 slash commands for search, analysis, optimization | Type `/rocq` in Claude Code ([full guide](../../COMMANDS.md)) |
| **Automation Scripts** | 16 tools for search, verification, refactoring | Plugin `scripts/` directory ([scripts/README.md](../../scripts/README.md)) |
| **Subagents** | 3 specialized agents for batch tasks (optional) | [subagent-workflows.md](references/subagent-workflows.md) |
| **LSP Server** | Fast feedback with instant proof state via coq-lsp | [rocq-lsp-server.md](references/rocq-lsp-server.md) |
| **Reference Files** | 11 detailed guides (phrasebook, tactics, patterns, errors, Iris) | [List below](#reference-files) |

## When to Use

Use for ANY Rocq/Coq development: pure/applied math, program verification, software foundations.

**Critical for:** Typeclass resolution errors, admit/axiom management, SSReflect/MathComp proofs, **Iris separation logic proofs**.

**Iris proofs?** Read [iris-proofs.md](references/iris-proofs.md) immediately - it covers proof mode tactics, resource algebras, ghost state, invariants, and HeapLang verification.

## Tools & Workflows

**7 slash commands** for search, analysis, and optimization - type `/rocq` in Claude Code. See [COMMANDS.md](../../COMMANDS.md) for full guide with examples and workflows.

**16 automation scripts** for search, verification, and refactoring. See [scripts/README.md](../../scripts/README.md) for complete documentation.

**coq-lsp Server** (optional) provides fast feedback with instant proof state and interactive proof development. See [rocq-lsp-server.md](references/rocq-lsp-server.md) for setup and workflows.

**Subagent delegation** (optional, Claude Code users) enables batch automation. See [subagent-workflows.md](references/subagent-workflows.md) for patterns.

## Build-First Principle

**ALWAYS compile before committing.** Run `dune build` (or `coqc` for single files) to verify. "Compiles" ≠ "Complete" - files can compile with admits/`Admitted` but aren't done until those are eliminated.

## The 4-Phase Workflow

1. **Structure Before Solving** - Outline proof strategy with `assert` statements and documented admits before writing tactics
2. **Helper Lemmas First** - Build infrastructure bottom-up, extract reusable components as separate lemmas
3. **Incremental Filling** - Fill ONE admit at a time, compile after each, commit working code
4. **Typeclass Management** - Add explicit instances with `Existing Instance` or local declarations when resolution fails, manage hints carefully

## Essential Tactics

**Key tactics:** `intros`, `apply`, `rewrite`, `reflexivity`, `simpl`, `destruct`, `induction`, `unfold`, `auto`, `eauto`

**SSReflect tactics:** `move`, `case`, `elim`, `rewrite`, `apply/`, `have`, `pose`

See [tactics-reference.md](references/tactics-reference.md) for comprehensive guide with examples and decision trees.

## Domain-Specific Patterns

**Algebra (MathComp):** Canonical structures, hierarchy builder patterns. Tactics: `ring`, `field`, `lra`, `lia`, `nia`.

**Software Foundations:** Inductive definitions, fixpoint functions, structural induction.

**Iris Separation Logic:** Concurrent program verification with proof mode tactics, resource algebras (RAs), ghost state management, invariants. Use for: concurrent algorithm verification, heap reasoning, program logic. **Read [iris-proofs.md](references/iris-proofs.md) for:**
- Proof mode tactics (`iIntros`, `iDestruct`, `iFrame`, `iApply`, `iMod`, `iLöb`)
- Resource algebras (`exclR`, `authR`, `agreeR`, `fracR`, `one_shotR`)
- Ghost state allocation and updates
- Invariant management (opening/closing)
- HeapLang weakest precondition verification
- Handling modalities (`|==>`, `|={E1,E2}=>`, `▷`, `□`)
- Understanding equalities and entailments

**Complete domain guide:** [domain-patterns.md](references/domain-patterns.md)

## Managing Incomplete Proofs

**CRITICAL: Admits/axioms are NOT complete work.** A theorem that compiles with `admit` or `Admitted` is scaffolding, not a result. Document every admit with concrete strategy and dependencies. Never add custom axioms without explicit user approval.

**When admits are acceptable:** (1) Active work in progress with documented plan, (2) User explicitly approves temporary axioms with elimination strategy.

**Not acceptable:** "Should be in stdlib", "infrastructure lemma", "will prove later" without concrete plan.

**Rocq admit keywords:**
- `admit.` - Incomplete tactic-mode proof (replaced with actual proof)
- `Admitted.` - Incomplete theorem declaration (replaced with `Qed.` or `Defined.`)
- `Axiom` - Custom axiom (avoid!)

## Common Compilation Errors

| Error | Fix |
|-------|-----|
| "Cannot infer..." / "Cannot find instance" | Add `Existing Instance` or provide explicit instance |
| "Universe inconsistency" | Check Type/Set/Prop levels, use `Set Universe Polymorphism` |
| "The term ... has type ... which should be Set, Prop or Type" | Fix universe levels |
| "Not found: ..." | Add `Require Import` or check module path |
| "Tactic failure" | Check goal state, use `Show.` to inspect current context |

See [compilation-errors.md](references/compilation-errors.md) for detailed debugging workflows.

## Documentation Conventions

- Write **timeless** documentation (describe what code is, not development history)
- Don't highlight "axiom-free" status after proofs are complete
- Mark internal helpers as `Local` or in dedicated sections
- Use `Example` for educational code, not `Lemma`/`Theorem`

## Quality Checklist

**Before commit:**
- [ ] `dune build` (or `make`) succeeds on full project
- [ ] All admits documented with concrete strategy
- [ ] No new axioms without elimination plan
- [ ] Imports minimal and organized

**Doing it right:** Admits/axioms decrease over time, each commit completes one lemma.

**Red flags:** Admits multiply, claiming "complete" with admits/axioms, fighting type checker for hours, monolithic proofs (>200 lines without intermediate lemmas).

## Reference Files

**Core references:** [rocq-phrasebook.md](references/rocq-phrasebook.md), [stdlib-guide.md](references/stdlib-guide.md), [tactics-reference.md](references/tactics-reference.md), [compilation-errors.md](references/compilation-errors.md)

**Domain-specific:** [domain-patterns.md](references/domain-patterns.md), [ssreflect-patterns.md](references/ssreflect-patterns.md), **[iris-proofs.md](references/iris-proofs.md)** ⭐

**Optimization:** [proof-golfing.md](references/proof-golfing.md)

**Tools:** [rocq-lsp-server.md](references/rocq-lsp-server.md)

### When to Read iris-proofs.md

**Read immediately if:**
- Working with Iris separation logic
- Verifying concurrent programs with HeapLang
- Using proof mode tactics (`iIntros`, `iFrame`, `iApply`, etc.)
- Managing ghost state or invariants
- Seeing errors about resource algebras (RAs)
- Proofs involve `|==>`, `|={E}=>`, `▷`, `□`, or `∗` operators
- Using weakest precondition reasoning (`WP e {{ Φ }}`)

**What you'll learn:**
- **12 sections** covering everything from basics to complete examples
- **Resource algebras:** 5 common RAs with patterns and use cases
- **Equalities:** 6 types of equality/entailment and when to use each
- **Proof mode:** All essential tactics with introduction patterns
- **HeapLang:** WP tactics for memory operations and concurrent code
- **Modalities:** Handling update, fancy update, later, and persistence
- **Invariants:** Opening, closing, and managing invariants correctly
- **Common pitfalls:** 6 mistakes and how to avoid them
- **Complete examples:** 3 worked proofs (counter, list sum, parallel code)
