---
name: lean4-theorem-proving
description: Use when developing Lean 4 proofs, facing type class synthesis errors, managing sorries/axioms, or searching mathlib - provides build-first workflow, instance management patterns (haveI/letI), and domain-specific tactics
---

# Lean 4 Theorem Proving

## Core Principle

**Build incrementally, structure before solving, trust the type checker.** Lean's type checker is your test suite.

**Success = `lake build` passes + zero sorries + zero custom axioms.** Theorems with sorries/axioms are scaffolding, not results.

## Quick Reference

| **Resource** | **What You Get** | **Where to Find** |
|--------------|------------------|-------------------|
| **Interactive Commands** | 7 slash commands for search, analysis, optimization | Type `/lean` in Claude Code ([full guide](../../COMMANDS.md)) |
| **Automation Scripts** | 16 tools for search, verification, refactoring | Plugin `scripts/` directory ([scripts/README.md](../../scripts/README.md)) |
| **Subagents** | 3 specialized agents for batch tasks (optional) | [subagent-workflows.md](references/subagent-workflows.md) |
| **LSP Server** | 30x faster feedback with instant proof state (optional) | [lean-lsp-server.md](references/lean-lsp-server.md) |
| **Reference Files** | 11 detailed guides (phrasebook, tactics, patterns, errors) | [List below](#reference-files) |

## When to Use

Use for ANY Lean 4 development: pure/applied math, program verification, mathlib contributions.

**Critical for:** Type class synthesis errors, sorry/axiom management, mathlib search, measure theory/probability work.

## Tools & Workflows

**7 slash commands** for search, analysis, and optimization - type `/lean` in Claude Code. See [COMMANDS.md](../../COMMANDS.md) for full guide with examples and workflows.

**16 automation scripts** for search, verification, and refactoring. See [scripts/README.md](../../scripts/README.md) for complete documentation.

**Lean LSP Server** (optional) provides 30x faster feedback with instant proof state and parallel tactic testing. See [lean-lsp-server.md](references/lean-lsp-server.md) for setup and workflows.

**Subagent delegation** (optional, Claude Code users) enables batch automation. See [subagent-workflows.md](references/subagent-workflows.md) for patterns.

## Build-First Principle

**ALWAYS compile before committing.** Run `lake build` to verify. "Compiles" ≠ "Complete" - files can compile with sorries/axioms but aren't done until those are eliminated.

## The 4-Phase Workflow

1. **Structure Before Solving** - Outline proof strategy with `have` statements and documented sorries before writing tactics
2. **Helper Lemmas First** - Build infrastructure bottom-up, extract reusable components as separate lemmas
3. **Incremental Filling** - Fill ONE sorry at a time, compile after each, commit working code
4. **Type Class Management** - Add explicit instances with `haveI`/`letI` when synthesis fails, respect binder order for sub-structures

## Finding and Using Mathlib Lemmas

**Philosophy:** Search before prove. Mathlib has 100,000+ theorems.

Use `/search-mathlib` slash command, LSP server search tools, or automation scripts. See [mathlib-guide.md](references/mathlib-guide.md) for detailed search techniques, naming conventions, and import organization.

## Essential Tactics

**Key tactics:** `simp only`, `rw`, `apply`, `exact`, `refine`, `by_cases`, `rcases`, `ext`/`funext`. See [tactics-reference.md](references/tactics-reference.md) for comprehensive guide with examples and decision trees.

## Domain-Specific Patterns

**Analysis & Topology:** Integrability, continuity, compactness patterns. Tactics: `continuity`, `fun_prop`.

**Algebra:** Instance building, quotient constructions. Tactics: `ring`, `field_simp`, `group`.

**Measure Theory & Probability** (emphasis in this skill): Conditional expectation, sub-σ-algebras, a.e. properties. Tactics: `measurability`, `positivity`. See [measure-theory.md](references/measure-theory.md) for detailed patterns.

**Complete domain guide:** [domain-patterns.md](references/domain-patterns.md)

## Managing Incomplete Proofs

**Standard mathlib axioms (acceptable):** `Classical.choice`, `propext`, `quot.sound`. Check with `#print axioms theorem_name` or `/check-axioms`.

**CRITICAL: Sorries/axioms are NOT complete work.** A theorem that compiles with sorries is scaffolding, not a result. Document every sorry with concrete strategy and dependencies. Search mathlib exhaustively before adding custom axioms.

**When sorries are acceptable:** (1) Active work in progress with documented plan, (2) User explicitly approves temporary axioms with elimination strategy.

**Not acceptable:** "Should be in mathlib", "infrastructure lemma", "will prove later" without concrete plan.

## Common Compilation Errors

| Error | Fix |
|-------|-----|
| "failed to synthesize instance" | Add `haveI : Instance := ...` |
| "maximum recursion depth" | Provide manually: `letI := ...` |
| "type mismatch" | Use coercion: `(x : ℝ)` or `↑x` |
| "unknown identifier" | Add import |

See [compilation-errors.md](references/compilation-errors.md) for detailed debugging workflows.


## Documentation Conventions

- Write **timeless** documentation (describe what code is, not development history)
- Don't highlight "axiom-free" status after proofs are complete
- Mark internal helpers as `private` or in dedicated sections
- Use `example` for educational code, not `lemma`/`theorem`

## Quality Checklist

**Before commit:**
- [ ] `lake build` succeeds on full project
- [ ] All sorries documented with concrete strategy
- [ ] No new axioms without elimination plan
- [ ] Imports minimal

**Doing it right:** Sorries/axioms decrease over time, each commit completes one lemma, proofs build on mathlib.

**Red flags:** Sorries multiply, claiming "complete" with sorries/axioms, fighting type checker for hours, monolithic proofs (>100 lines).

## Reference Files

**Core references:** [lean-phrasebook.md](references/lean-phrasebook.md), [mathlib-guide.md](references/mathlib-guide.md), [tactics-reference.md](references/tactics-reference.md), [compilation-errors.md](references/compilation-errors.md)

**Domain-specific:** [domain-patterns.md](references/domain-patterns.md), [measure-theory.md](references/measure-theory.md), [calc-patterns.md](references/calc-patterns.md)

**Optimization:** [proof-golfing.md](references/proof-golfing.md), [mathlib-style.md](references/mathlib-style.md)

**Tools:** [lean-lsp-server.md](references/lean-lsp-server.md), [subagent-workflows.md](references/subagent-workflows.md)
