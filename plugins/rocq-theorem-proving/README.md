# Rocq Theorem Proving Plugin

Systematic workflows for Rocq/Coq proofs: admits management, stdlib/MathComp usage, verified mathematics and program verification.

**Version:** 1.0.0
**Status:** Initial Release
**Author:** Zongyuan Liu

---

## Overview

This plugin provides comprehensive support for theorem proving in Rocq (formerly Coq), including:

- **Core Skill** with build-first workflow and 4-phase development process
- **Comprehensive Reference Documentation** covering tactics, patterns, and common errors
- **Support for Multiple Styles** - Standard Coq and SSReflect/MathComp
- **Domain-Specific Patterns** for algebra, analysis, software foundations, and more

---

## Quick Start

### Installation

1. **Clone or copy** this plugin to your Claude Code plugins directory:
   ```
   ~/.claude-code/plugins/rocq-theorem-proving/
   ```

2. **Restart Claude Code** to load the plugin.

3. **Invoke the skill** when working on Rocq/Coq projects:
   - The skill activates automatically for `.v` files
   - Use `/rocq` commands (when implemented)
   - Reference guides are always available

### Basic Usage

When developing Rocq proofs, the skill provides:

1. **Build-first principle** - Always compile before committing
2. **4-phase workflow** - Structure before solving, helper lemmas first, incremental filling, typeclass management
3. **Search-first approach** - Always search stdlib/MathComp before proving
4. **Quality gates** - Zero admits, zero custom axioms, minimal imports

---

## What's Included

### Core Skill

**File:** `skills/rocq-theorem-proving/SKILL.md`

The main skill file provides:
- Core principles (build incrementally, trust the type checker)
- 4-phase development workflow
- Essential tactics quick reference
- Quality checklist
- Integration with reference files

### Reference Documentation

#### 1. Rocq Phrasebook (`references/rocq-phrasebook.md`)

Mathematical English → Rocq translations organized by proof situation.

**Covers:**
- Forward and backward reasoning
- Case analysis and induction
- Rewriting and simplification
- Quantifiers and connectives
- Contradiction and contrapositive
- Set theory and extensionality
- Algebraic reasoning
- SSReflect patterns

**Use when:** Translating informal proof ideas to formal Rocq tactics.

#### 2. Tactics Reference (`references/tactics-reference.md`)

Comprehensive guide to all Rocq/Coq tactics with examples and decision trees.

**Covers:**
- Core tactics (intros, apply, exact, rewrite)
- Simplification (simpl, compute, unfold)
- Case analysis and induction
- Automation (auto, lia, ring, congruence)
- SSReflect tactics (move, case, elim, have)
- Goal management
- Decision procedures

**Use when:** Need to know which tactic to use or how to use it.

#### 3. Compilation Errors (`references/compilation-errors.md`)

Detailed explanations and fixes for common Rocq/Coq errors.

**Covers:**
- Typeclass resolution errors
- Universe inconsistency
- Type mismatches
- Tactic failures
- Recursion and termination errors
- Module and import errors
- Error recovery strategies

**Use when:** Debugging compilation or tactic failures.

#### 4. Standard Library Guide (`references/stdlib-guide.md`)

Guide to finding and using lemmas from Coq standard library and ecosystem.

**Covers:**
- Standard library structure
- Core modules (Lists, Arith, ZArith, Reals, etc.)
- Search strategies (Search, SearchPattern, Locate)
- Third-party libraries (MathComp, Coquelicot, ExtLib)
- Common lemma patterns
- Import strategies

**Use when:** Looking for existing lemmas before proving.

#### 5. SSReflect Patterns (`references/ssreflect-patterns.md`)

Comprehensive guide to SSReflect proof style (MathComp).

**Covers:**
- Core SSReflect principles (stack-based, explicit bookkeeping)
- Basic stack operations (move, case, elim)
- Rewriting patterns
- Views (bool ↔ Prop bridge)
- Boolean reflection
- Common idioms
- Comparison with standard Coq

**Use when:** Working with MathComp or want SSReflect style.

#### 6. Domain Patterns (`references/domain-patterns.md`)

Domain-specific tactics and patterns for specialized areas.

**Covers:**
- Software Foundations (inductive types, structural induction)
- Algebra (groups, rings, fields, MathComp hierarchy)
- Analysis (limits, continuity, derivatives, Coquelicot)
- Logic and set theory
- Type theory and dependent types
- Program verification
- MathComp algebraic hierarchy

**Use when:** Working in a specific mathematical or CS domain.

---

## Feature Comparison: Rocq vs Lean 4

| Aspect | Lean 4 | Rocq/Coq |
|--------|--------|----------|
| **Incomplete proofs** | `sorry` | `admit`, `Admitted` |
| **Build system** | `lake build` | `dune build`, `coqc` |
| **Main library** | mathlib | stdlib + MathComp + UniMath |
| **LSP** | Lean LSP | coq-lsp |
| **Tactics style** | Term-style, `simp`, `rw` | Ltac, SSReflect, `rewrite`, `simpl` |
| **Type classes** | `haveI`, `letI` | `Existing Instance`, context |
| **Automation** | `simp`, `ring`, `linarith` | `auto`, `ring`, `lia`, `congruence` |
| **Proof style** | Calculation chains, `calc` | Rewrite chains, SSReflect |

---

## Directory Structure

```
rocq-theorem-proving/
├── .claude-plugin/
│   └── plugin.json           # Plugin metadata
├── skills/
│   └── rocq-theorem-proving/
│       ├── SKILL.md          # Main skill file
│       └── references/       # Reference documentation
│           ├── rocq-phrasebook.md
│           ├── tactics-reference.md
│           ├── compilation-errors.md
│           ├── stdlib-guide.md
│           ├── ssreflect-patterns.md
│           └── domain-patterns.md
├── commands/                 # Slash commands (TODO)
├── scripts/                  # Automation scripts (TODO)
├── hooks/                    # Session hooks (TODO)
└── README.md                 # This file
```

---

## Roadmap

### Phase 1: Core Documentation ✅ (Current)
- [x] Main skill file
- [x] Core reference documentation (6 files)
- [x] Plugin metadata

### Phase 2: Commands and Scripts (Planned)
- [ ] `/search-coq-libs` - Search stdlib/MathComp
- [ ] `/build-rocq` - Build with error analysis
- [ ] `/fill-admit` - Interactive admit filling
- [ ] `/check-axioms` - Verify axiom hygiene
- [ ] `/analyze-admits` - Scan for incomplete proofs
- [ ] `/clean-warnings` - Warning cleanup
- [ ] Automation scripts (search, analysis, verification)

### Phase 3: Advanced Features (Future)
- [ ] Subagents for batch automation
- [ ] Memory integration (persistent patterns)
- [ ] LSP integration guide
- [ ] Pre-commit hooks
- [ ] CI/CD integration examples

---

## Usage Examples

### Example 1: Basic Theorem Proving

```coq
Require Import Coq.Arith.Arith.

(* 1. Structure before solving *)
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  (* 2. Helper lemmas first - use stdlib *)
  (* Search for existing lemmas *)
  (* SearchPattern (_ + _ = _ + _). *)
  (* Found: Nat.add_comm *)

  (* 3. Incremental filling *)
  intros n m.
  apply Nat.add_comm.  (* Use existing lemma *)
Qed.
```

### Example 2: SSReflect Style

```coq
From mathcomp Require Import all_ssreflect.

Lemma addn_comm : forall n m, n + m = m + n.
Proof.
  (* SSReflect style: explicit and composable *)
  move=> n m.
  by rewrite addnC.  (* MathComp commutativity *)
Qed.
```

### Example 3: Using Reference Guides

1. **Need tactic?** → Check [tactics-reference.md](skills/rocq-theorem-proving/references/tactics-reference.md)
2. **Compilation error?** → Check [compilation-errors.md](skills/rocq-theorem-proving/references/compilation-errors.md)
3. **Looking for lemma?** → Check [stdlib-guide.md](skills/rocq-theorem-proving/references/stdlib-guide.md)
4. **Working with MathComp?** → Check [ssreflect-patterns.md](skills/rocq-theorem-proving/references/ssreflect-patterns.md)
5. **Proving algebra?** → Check [domain-patterns.md](skills/rocq-theorem-proving/references/domain-patterns.md)

---

## Best Practices

### 1. Build-First Workflow

```bash
# Always compile before committing
dune build    # or: coqc file.v

# "Compiles" ≠ "Complete"
# Files can compile with admits but aren't done
```

### 2. Search Before Proving

```coq
(* Always search first *)
SearchPattern (_ + _ = _ + _).
SearchAbout list.
Search "map" inside Coq.Lists.

(* 60-90% of standard results exist *)
```

### 3. Document Admits

```coq
(* ❌ BAD: Undocumented admit *)
Lemma hard : forall n, complicated n.
Proof. admit. Admitted.

(* ✅ GOOD: Documented strategy *)
Lemma hard : forall n, complicated n.
Proof.
  (* TODO: Need to prove helper_lemma first *)
  (* STRATEGY: Induction on n, use helper_lemma in step case *)
  admit.
Admitted.
```

### 4. Quality Checklist

Before committing:
- [ ] `dune build` succeeds
- [ ] All admits documented with strategy
- [ ] No new axioms without elimination plan
- [ ] Imports minimal and organized

---

## Getting Help

### Within the Plugin

- Read the [SKILL.md](skills/rocq-theorem-proving/SKILL.md) for core workflow
- Check appropriate reference guide (see above)
- Use Coq's built-in help: `Check`, `Search`, `SearchPattern`, `About`, `Print`

### External Resources

**Learning Coq:**
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) - Start here
- [Coq'Art](https://www.labri.fr/perso/casteran/CoqArt/) - Comprehensive book
- [CPDT](http://adam.chlipala.net/cpdt/) - Advanced patterns

**Reference:**
- [Coq Reference Manual](https://coq.inria.fr/refman/)
- [Standard Library Docs](https://coq.inria.fr/distrib/current/stdlib/)

**MathComp/SSReflect:**
- [Mathematical Components Book](https://math-comp.github.io/mcb/)
- [MathComp Documentation](https://math-comp.github.io/)

**Real Analysis:**
- [Coquelicot](http://coquelicot.saclay.inria.fr/)
- [MathComp Analysis](https://github.com/math-comp/analysis)

---

## Contributing

This plugin is in active development. Contributions welcome:

1. **Additional reference guides** (more domains, specialized tactics)
2. **Command implementations** (slash commands for common workflows)
3. **Automation scripts** (search, verification, refactoring)
4. **Examples and case studies**

---

## License

MIT License

---

## Acknowledgments

- Inspired by the Lean 4 skills in this repository
- SSReflect/MathComp community for algebraic hierarchy patterns
- Software Foundations authors for pedagogical approach
- Coq development team for the proof assistant

---

## Version History

### 1.0.0 (2025-10-29) - Initial Release
- Core skill file with 4-phase workflow
- 6 comprehensive reference guides:
  - Rocq Phrasebook (Mathematical English → Rocq)
  - Tactics Reference (comprehensive tactics guide)
  - Compilation Errors (debugging guide)
  - Standard Library Guide (finding lemmas)
  - SSReflect Patterns (MathComp style)
  - Domain Patterns (specialized domains)
- Plugin infrastructure and metadata
- README with usage examples and best practices

---

**For questions, feedback, or contributions, please file an issue or reach out to the maintainers.**
