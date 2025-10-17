# Formal Verification Skills

Skills for working with formal verification systems, proof assistants, and mathematical formalization.

## Skills in this Category

### Lean 4 Theorem Proving
Systematic approach to developing formal proofs in Lean 4, managing proofs incrementally, integrating with mathlib, and building verified mathematics.

**Use when:** Working on Lean 4 formalization projects, proving theorems, or developing mathematical libraries.

## What is Formal Verification?

Formal verification uses mathematical logic to prove properties about software, algorithms, and mathematical theorems. Unlike testing (which checks specific cases), formal verification provides guarantees that properties hold for ALL possible inputs.

**Common verification systems:**
- **Lean 4** - Interactive theorem prover with strong mathlib ecosystem
- **Coq** - Mature proof assistant with extensive standard library
- **Isabelle** - Automated reasoning with higher-order logic
- **Agda** - Dependently typed language for proofs and programs
- **F*** - Verification-oriented programming language

## Why Formal Verification?

**Benefits:**
- Mathematical certainty (not just confidence from tests)
- Find edge cases that testing misses
- Documentation that can't become outdated (proofs must match code)
- Deep understanding through proving properties

**Challenges:**
- Steep learning curve
- Time investment required
- Some properties hard to express formally
- Proof maintenance as code evolves

## When to Use These Skills

**Good candidates for formal verification:**
- Security-critical code (crypto, authentication, access control)
- Safety-critical systems (medical devices, aerospace, automotive)
- Mathematical algorithms (optimization, numerical methods)
- Foundational libraries (compilers, operating systems, distributed systems)
- Academic research requiring mathematical rigor

**Poor candidates:**
- Rapidly changing prototypes
- UI/UX code with subjective requirements
- Integration glue code
- Simple CRUD operations
- Time-sensitive delivery with low risk

## Core Principles

1. **Build incrementally** - One proven lemma at a time
2. **Structure before solving** - Outline proof strategy before tactics
3. **Trust the type checker** - It's your test suite
4. **Leverage libraries** - Don't reprove standard results
5. **Document assumptions** - Make axioms explicit

## Related Skill Categories

- **debugging/** - Systematic debugging applies to proof errors
- **problem-solving/** - Breaking down complex theorems
- **research/** - Understanding prior art in formalization
- **testing/** - Complementary verification approach

## Getting Started with Formal Verification

**If new to formal verification:**

1. **Start with tutorial** - Complete language-specific tutorial
2. **Study existing proofs** - Read formalized mathematics in your domain
3. **Begin with simple theorems** - Build confidence with basic proofs
4. **Use automation** - Let tactics do routine work
5. **Join community** - Forums and chat rooms are invaluable

**Lean 4 specific:**
- Read "Theorem Proving in Lean 4"
- Browse mathlib documentation
- Join Lean Zulip chat
- Study proofs in your domain (algebra, analysis, etc.)

## Success Indicators

You're making progress when:
- Code compiles more often than not
- Proofs reuse helper lemmas
- Type errors make sense
- You find existing library lemmas before reproving
- Axioms/sorries decrease over time
- Commit history shows steady incremental progress

## Learning Path

**Beginner:**
- Master basic tactics (intro, apply, rw, simp)
- Understand type signatures
- Prove simple properties (commutativity, associativity)
- Use existing library results

**Intermediate:**
- Structure complex proofs with helper lemmas
- Navigate library documentation
- Manage type class instances
- Prove moderate theorems with multi-step arguments

**Advanced:**
- Develop reusable abstractions
- Contribute to mathematical libraries
- Handle tricky type class inference
- Formalize research mathematics

## Resources

**General formal verification:**
- Software Foundations (Coq): https://softwarefoundations.cis.upenn.edu/
- Concrete Semantics (Isabelle): http://www.concrete-semantics.org/

**Lean 4 specific:**
- Theorem Proving in Lean 4: https://leanprover.github.io/theorem_proving_in_lean4/
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- Functional Programming in Lean: https://leanprover.github.io/functional_programming_in_lean/
- Lean Zulip: https://leanprover.zulipchat.com/
