# Rocq Theorem Proving Plugin

Systematic workflows for Rocq/Coq proofs: LSP-driven development, admits management, stdlib/MathComp usage, verified mathematics and program verification.

**Version:** 1.1.0
**Status:** Active Development
**Author:** Zongyuan Liu

---

## Overview

This plugin provides comprehensive support for theorem proving in Rocq (formerly Coq), featuring:

- **LSP-First Workflow** with instant feedback via Rocq LSP MCP server
- **Core Skill** with build-first principles and 4-phase development process
- **9 Reference Guides** covering tactics, patterns, LSP usage, and optimization
- **4 Slash Commands** for axiom checking, proof optimization, admit filling, and building
- **Automation Scripts** for axiom verification with detailed reporting
- **Support for Multiple Styles** - Standard Coq and SSReflect/MathComp

**Key insight:** LSP tools provide **30x faster feedback** (< 1s vs 30s build cycles), transforming proof development from "guess and wait" to "see and verify" instantly.

---

## Quick Start

### Prerequisites

1. **Install coq-lsp:**
   ```bash
   opam install coq-lsp
   ```

2. **Configure MCP Server:**
   Add Rocq LSP MCP server to your Claude Code settings for instant feedback on proof state, goals, and tactics.

### Installation

1. **Clone or copy** this plugin to your Claude Code plugins directory:
   ```
   ~/.claude-code/plugins/rocq-theorem-proving/
   ```

2. **Restart Claude Code** to load the plugin.

3. **Invoke the skill** when working on Rocq/Coq projects:
   - The skill activates automatically for `.v` files
   - Use slash commands: `/check-axioms`, `/golf-proofs`, `/fill-admit`, `/build-rocq`
   - Reference guides are always available

### Basic Usage

When developing Rocq proofs, the plugin provides:

1. **LSP-first workflow** - Use `rocq_get_goals` constantly, test tactics with `rocq_run_tactic` before editing
2. **Build-first principle** - Always compile before committing
3. **4-phase development** - Structure before solving, helper lemmas first, incremental filling, typeclass management
4. **Search-first approach** - Always search stdlib/MathComp before proving
5. **Quality gates** - Zero admits, zero custom axioms, minimal imports

---

## What's Included

### Core Skill

**File:** [skills/rocq-theorem-proving/SKILL.md](skills/rocq-theorem-proving/SKILL.md)

The main skill file provides:
- Core principles (build incrementally, trust the type checker, LSP-first)
- 4-phase development workflow
- Essential tactics quick reference
- Quality checklist
- Integration with reference files and LSP tools

### Reference Documentation

#### 1. Rocq LSP Server Reference ([references/rocq-lsp-server.md](skills/rocq-theorem-proving/references/rocq-lsp-server.md))

**NEW!** Comprehensive guide to using Rocq LSP MCP server for 30x faster proof development.

**Covers:**
- LSP-first workflow patterns (start session → check goals → test tactics → edit file)
- 7 essential tools: `rocq_start_proof`, `rocq_get_goals`, `rocq_run_tactic`, `rocq_get_premises`, `rocq_search`, `rocq_get_file_toc`, `rocq_get_state_at_position`
- Complete end-to-end examples
- Interactive proof development patterns
- Troubleshooting and best practices

**Use when:** Developing proofs interactively with instant feedback (ALWAYS!)

#### 2. Rocq Phrasebook ([references/rocq-phrasebook.md](skills/rocq-theorem-proving/references/rocq-phrasebook.md))

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

#### 3. Tactics Reference ([references/tactics-reference.md](skills/rocq-theorem-proving/references/tactics-reference.md))

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

#### 4. Compilation Errors ([references/compilation-errors.md](skills/rocq-theorem-proving/references/compilation-errors.md))

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

#### 5. Standard Library Guide ([references/stdlib-guide.md](skills/rocq-theorem-proving/references/stdlib-guide.md))

Guide to finding and using lemmas from Coq standard library and ecosystem.

**Covers:**
- Standard library structure
- Core modules (Lists, Arith, ZArith, Reals, etc.)
- Search strategies (Search, SearchPattern, Locate)
- Third-party libraries (MathComp, Coquelicot, ExtLib)
- Common lemma patterns
- Import strategies

**Use when:** Looking for existing lemmas before proving.

#### 6. SSReflect Patterns ([references/ssreflect-patterns.md](skills/rocq-theorem-proving/references/ssreflect-patterns.md))

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

#### 7. Domain Patterns ([references/domain-patterns.md](skills/rocq-theorem-proving/references/domain-patterns.md))

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

#### 8. Admit Filling ([references/admit-filling.md](skills/rocq-theorem-proving/references/admit-filling.md))

Systematic approach to filling admits and completing proof obligations.

**Covers:**
- Categorizing admits (trivial, routine, challenging, blocked)
- Prioritization strategies
- Filling workflow (context → search → test → fill)
- Dependency resolution
- Progress tracking

**Use when:** Working through incomplete proofs systematically.

#### 9. Axiom Elimination ([references/axiom-elimination.md](skills/rocq-theorem-proving/references/axiom-elimination.md))

Strategies for eliminating or justifying axiom usage.

**Covers:**
- Standard vs custom axioms
- Elimination strategies for common axioms
- When axioms are acceptable
- Verification workflow
- Documentation requirements

**Use when:** Reducing axiom dependencies or verifying axiom hygiene.

#### 10. Proof Golfing ([references/proof-golfing.md](skills/rocq-theorem-proving/references/proof-golfing.md))

**NEW!** Patterns for optimizing proof length while maintaining readability (20-40% reduction).

**Covers:**
- 7 key optimization patterns (tactic chaining, SSReflect idioms, elimination of redundancy)
- When to optimize vs when readability matters
- Interactive optimization workflow
- Benchmarks and measurements

**Use when:** Proofs are complete but could be more concise.

### Slash Commands

#### 1. `/check-axioms` ([commands/check-axioms.md](commands/check-axioms.md))

**NEW!** Verify axiom hygiene in Rocq/Coq proofs.

**Features:**
- Scans files for axiom dependencies using `Print Assumptions`
- Distinguishes standard axioms (functional_extensionality, etc.) from custom ones
- Highlights `proof_admitted` from incomplete proofs
- Generates detailed reports with elimination strategies

**Usage:**
```
/check-axioms
```

**Backed by:** [scripts/check_axioms.sh](scripts/check_axioms.sh) - Automated axiom analysis

#### 2. `/golf-proofs` ([commands/golf-proofs.md](commands/golf-proofs.md))

**NEW!** Interactively optimize Rocq/Coq proofs.

**Features:**
- Identifies 7 optimization patterns automatically
- Applies changes interactively with user approval
- Tests each optimization with compilation
- Tracks size reduction (target: 20-40%)

**Usage:**
```
/golf-proofs
```

#### 3. `/fill-admit` ([commands/fill-admit.md](commands/fill-admit.md))

Systematically fill admits in Rocq/Coq files.

**Features:**
- Scans for all admits in file/directory
- Categorizes by difficulty (trivial, routine, challenging, blocked)
- Provides interactive filling workflow
- Tracks progress

**Usage:**
```
/fill-admit
```

#### 4. `/build-rocq` ([commands/build-rocq.md](commands/build-rocq.md))

Build Rocq/Coq project with enhanced error analysis.

**Features:**
- Runs appropriate build system (dune, make, coqc)
- Parses and categorizes errors
- Provides targeted fixes
- Suggests next steps

**Usage:**
```
/build-rocq
```

### Automation Scripts

#### `scripts/check_axioms.sh`

**NEW!** Robust axiom checker for Coq/Rocq projects.

**Features:**
- Generates temporary verification files
- Extracts and categorizes axioms
- Distinguishes standard vs custom axioms
- Provides detailed reports with line numbers
- Suggests elimination strategies

**Usage:**
```bash
./scripts/check_axioms.sh path/to/file.v
./scripts/check_axioms.sh src/theories/  # Directory
```

---

## Directory Structure

```
rocq-theorem-proving/
├── .claude-plugin/
│   └── plugin.json              # Plugin metadata
├── skills/
│   └── rocq-theorem-proving/
│       ├── SKILL.md             # Main skill file
│       └── references/          # Reference documentation (10 guides)
│           ├── rocq-lsp-server.md       ⭐ NEW!
│           ├── rocq-phrasebook.md
│           ├── tactics-reference.md
│           ├── compilation-errors.md
│           ├── stdlib-guide.md
│           ├── ssreflect-patterns.md
│           ├── domain-patterns.md
│           ├── admit-filling.md
│           ├── axiom-elimination.md
│           └── proof-golfing.md         ⭐ NEW!
├── commands/                    # Slash commands (4 implemented)
│   ├── check-axioms.md          ⭐ NEW!
│   ├── golf-proofs.md           ⭐ NEW!
│   ├── fill-admit.md
│   └── build-rocq.md
├── scripts/                     # Automation scripts
│   └── check_axioms.sh          ⭐ NEW!
├── hooks/                       # Plugin hooks
│   ├── bootstrap.sh             # Hook initialization
│   └── hooks.json               # Hook configuration
└── README.md                    # This file
```

---

## Feature Comparison: Rocq vs Lean 4

| Aspect | Lean 4 | Rocq/Coq |
|--------|--------|----------|
| **Incomplete proofs** | `sorry` | `admit`, `Admitted` |
| **Build system** | `lake build` | `dune build`, `coqc` |
| **Main library** | mathlib | stdlib + MathComp + UniMath |
| **LSP** | Lean LSP | coq-lsp ⭐ |
| **LSP MCP Tools** | 15+ tools | 7 core tools ⭐ |
| **Tactics style** | Term-style, `simp`, `rw` | Ltac, SSReflect, `rewrite`, `simpl` |
| **Type classes** | `haveI`, `letI` | `Existing Instance`, context |
| **Automation** | `simp`, `ring`, `linarith` | `auto`, `ring`, `lia`, `congruence` |
| **Proof style** | Calculation chains, `calc` | Rewrite chains, SSReflect |

---

## LSP-First Workflow (NEW!)

The plugin now emphasizes **LSP-first development** for 30x faster feedback:

### Quick Reference Pattern

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

### 7 Essential LSP Tools

| Tool | Purpose | Use Constantly? |
|------|---------|-----------------|
| `rocq_start_proof` | Initialize proof session | Start of each proof |
| `rocq_get_goals` | Check proof state | ✅ ALWAYS! After every tactic |
| `rocq_run_tactic` | Test tactics | Before editing file |
| `rocq_get_premises` | Find available lemmas | When stuck |
| `rocq_search` | Search for theorems | Before hallucinating |
| `rocq_get_file_toc` | Get file structure | Batch operations |
| `rocq_get_state_at_position` | Position-based queries | IDE features |

**See [rocq-lsp-server.md](skills/rocq-theorem-proving/references/rocq-lsp-server.md) for complete guide.**

---

## Usage Examples

### Example 1: LSP-Driven Proof Development (RECOMMENDED!)

```coq
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  (* LSP workflow - FAST! *)
Admitted.
```

**Interactive workflow:**
```python
# 1. Start session
session = rocq_start_proof("file.v", "add_comm")

# 2. Check what to prove
goals = rocq_get_goals(session)
# Output: forall n m : nat, n + m = m + n

# 3. Search for lemmas
results = rocq_search(session, "add_comm")
# Found: Nat.add_comm

# 4. Test tactics
rocq_run_tactic(session, "intros n m.")
rocq_get_goals(session)  # Check progress

rocq_run_tactic(session, "apply Nat.add_comm.")
rocq_get_goals(session)  # Output: No more goals. ✅

# 5. Edit file with working proof
```

**Final proof:**
```coq
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  apply Nat.add_comm.
Qed.
```

**Time:** < 10 seconds with absolute certainty!

### Example 2: Traditional Build Workflow

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

**Time:** 30+ seconds per try-and-rebuild cycle

### Example 3: SSReflect Style

```coq
From mathcomp Require Import all_ssreflect.

Lemma addn_comm : forall n m, n + m = m + n.
Proof.
  (* SSReflect style: explicit and composable *)
  move=> n m.
  by rewrite addnC.  (* MathComp commutativity *)
Qed.
```

### Example 4: Axiom Checking

```bash
# Check current file
/check-axioms

# Check entire project
/check-axioms

# Sample output:
# ✓ add_comm: No axioms
# ⚠ harder_theorem: Depends on functional_extensionality (STANDARD)
# ❌ incomplete_proof: Depends on proof_admitted (CUSTOM - from Admitted)
```

### Example 5: Proof Optimization

```bash
# Optimize proofs interactively
/golf-proofs

# Sample optimization:
# Before (5 lines):
#   intros n m.
#   simpl.
#   rewrite H.
#   simpl.
#   reflexivity.
#
# After (1 line):
#   intros; simpl; rewrite H; reflexivity.
#
# Reduction: 80% shorter, same clarity
```

---

## Best Practices

### 1. LSP-First Development (NEW!)

```
✅ DO:
- Start LSP session for every proof
- Check goals with rocq_get_goals constantly
- Test tactics with rocq_run_tactic before editing
- Search with rocq_search before hallucinating
- Verify with LSP, then compile

❌ DON'T:
- Edit → build → see error (too slow!)
- Guess lemma names without searching
- Apply tactics without checking goals
- Skip intermediate goal checks
```

### 2. Build-First Workflow

```bash
# Always compile before committing
dune build    # or: coqc file.v

# "Compiles" ≠ "Complete"
# Files can compile with admits but aren't done
```

### 3. Search Before Proving

```coq
(* Always search first *)
SearchPattern (_ + _ = _ + _).
SearchAbout list.
Search "map" inside Coq.Lists.

(* Or use LSP: *)
(* rocq_search(session, "add_comm") *)

(* 60-90% of standard results exist *)
```

### 4. Document Admits

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

### 5. Quality Checklist

Before committing:
- [ ] `dune build` succeeds
- [ ] All admits documented with strategy
- [ ] No new axioms without elimination plan (`/check-axioms`)
- [ ] Imports minimal and organized
- [ ] Proofs optimized if appropriate (`/golf-proofs`)

---

## Getting Help

### Within the Plugin

- **LSP-first!** Read [rocq-lsp-server.md](skills/rocq-theorem-proving/references/rocq-lsp-server.md) for instant feedback workflow
- Read the [SKILL.md](skills/rocq-theorem-proving/SKILL.md) for core workflow
- Check appropriate reference guide (10 guides available)
- Use slash commands: `/check-axioms`, `/golf-proofs`, `/fill-admit`, `/build-rocq`
- Use Coq's built-in help: `Check`, `Search`, `SearchPattern`, `About`, `Print`

### External Resources

**Learning Coq:**
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/) - Start here
- [Coq'Art](https://www.labri.fr/perso/casteran/CoqArt/) - Comprehensive book
- [CPDT](http://adam.chlipala.net/cpdt/) - Advanced patterns

**Reference:**
- [Coq Reference Manual](https://coq.inria.fr/refman/)
- [Standard Library Docs](https://coq.inria.fr/distrib/current/stdlib/)
- [coq-lsp GitHub](https://github.com/ejgallego/coq-lsp) - LSP server

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
2. **Command implementations** (more slash commands)
3. **Automation scripts** (search, verification, refactoring)
4. **Examples and case studies**
5. **LSP tool improvements** (better patterns, more workflows)

---

## Roadmap

### Phase 1: Core Documentation ✅ COMPLETE
- [x] Main skill file
- [x] Core reference documentation (6 files)
- [x] Plugin metadata

### Phase 2: Commands and Scripts ✅ COMPLETE
- [x] `/check-axioms` - Axiom hygiene verification ⭐
- [x] `/golf-proofs` - Interactive proof optimization ⭐
- [x] `/fill-admit` - Interactive admit filling
- [x] `/build-rocq` - Build with error analysis
- [x] `check_axioms.sh` - Automated axiom analysis ⭐
- [x] Additional references (admit-filling, axiom-elimination, proof-golfing) ⭐

### Phase 3: LSP Integration ✅ COMPLETE
- [x] LSP server reference guide ⭐
- [x] LSP-first workflow patterns ⭐
- [x] Complete tool documentation (7 tools) ⭐
- [x] End-to-end examples ⭐
- [x] Troubleshooting and best practices ⭐

### Phase 4: Advanced Features (Current)
- [ ] `/analyze-admits` - Project-wide admit analysis
- [ ] `/clean-warnings` - Warning cleanup automation
- [ ] Subagents for batch automation
- [ ] Memory integration (persistent patterns)
- [ ] Pre-commit hooks for axiom checking
- [ ] CI/CD integration examples

---

## Version History

### 1.1.0 (2025-10-31) - LSP Integration & Automation
- ⭐ Added Rocq LSP Server Reference with 30x speedup workflow
- ⭐ Implemented `/check-axioms` command with `check_axioms.sh` script
- ⭐ Implemented `/golf-proofs` command for proof optimization
- ⭐ Added 3 new reference guides:
  - admit-filling.md (systematic admit resolution)
  - axiom-elimination.md (axiom reduction strategies)
  - proof-golfing.md (optimization patterns, 20-40% reduction)
- Added hooks infrastructure (bootstrap.sh, hooks.json)
- Emphasized LSP-first development throughout documentation
- Updated all examples to show LSP workflow
- Enhanced directory structure with scripts and commands

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

## License

MIT License

---

## Acknowledgments

- Inspired by the Lean 4 skills in this repository
- coq-lsp team for excellent LSP implementation
- SSReflect/MathComp community for algebraic hierarchy patterns
- Software Foundations authors for pedagogical approach
- Coq development team for the proof assistant

---

**For questions, feedback, or contributions, please file an issue or reach out to the maintainers.**
