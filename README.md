# Lean 4 Theorem Proving - Claude Code Skill

A comprehensive [Claude Code](https://claude.com/claude-code) skill for systematic development of formal proofs in Lean 4.

## 🎯 What is This?

This is a **Claude Skill** that teaches Claude Code how to work effectively with Lean 4 theorem proving. It provides:

- 📚 **Systematic workflow** for proof development (structure → helpers → incremental filling)
- 🔧 **Type class management** patterns for sub-σ-algebras and instance inference
- 📖 **Mathlib integration** guide (finding lemmas, imports, naming conventions)
- 🎓 **Domain-specific patterns** for measure theory, probability, and algebra
- ✅ **Quality standards** (compile before commit, document sorries, eliminate axioms)
- 💡 **Real-world examples** from successful Lean formalization projects

## 🚀 Installation

### For Claude Code Users

1. **Clone or download this repository:**
   ```bash
   git clone https://github.com/YOUR_USERNAME/lean4-theorem-proving-skill.git
   ```

2. **Copy to your skills directory:**
   ```bash
   cp -r lean4-theorem-proving-skill/skills/formal-verification \
         ~/.config/superpowers/skills/skills/
   ```

3. **Verify installation:**
   ```bash
   ls ~/.config/superpowers/skills/skills/formal-verification/lean4-theorem-proving/
   # Should show: SKILL.md
   ```

That's it! The skill is immediately available in all Claude Code sessions.

### Alternative: Manual Installation

If you prefer to install manually:

1. Create the directory structure:
   ```bash
   mkdir -p ~/.config/superpowers/skills/skills/formal-verification/lean4-theorem-proving
   ```

2. Copy the files:
   - Copy `skills/formal-verification/ABOUT.md` to `~/.config/superpowers/skills/skills/formal-verification/`
   - Copy `skills/formal-verification/lean4-theorem-proving/SKILL.md` to the appropriate directory

## 📖 Usage

### Automatic (Proactive)

Claude Code will automatically invoke this skill when you:
- Work on `.lean` files
- Prove theorems
- Manage sorries or axioms
- Ask about Lean-specific concepts

### Explicit Invocation

You can explicitly request the skill:

```
Use the lean4-theorem-proving skill to help me structure this proof
```

Or in the context of formal verification:

```
Following the Lean 4 skill, how should I manage these type class instances?
```

### Query the Skill

Ask specific questions about the guidance:

```
What does the Lean 4 skill say about managing sorries?
What's the recommended workflow for eliminating axioms?
```

## 🎓 What the Skill Teaches

### Core Workflow

1. **Structure Before Solving** - Outline proof strategy before writing tactics
2. **Helper Lemmas First** - Build infrastructure bottom-up
3. **Incremental Filling** - One `sorry` at a time, compile, commit, repeat
4. **Type Class Management** - Explicit instance handling for sub-structures

### Key Principles

- ✅ **Always compile before commit** (`lake build` is your test suite)
- ✅ **Document every sorry** with strategy and dependencies
- ✅ **Search mathlib first** before reproving standard results
- ✅ **Eliminate axioms systematically** with documented plans
- ✅ **One change at a time** - fill one sorry, compile, commit

### Common Patterns Included

- **Integrability proofs** (bounded + measurable + finite measure)
- **Conditional expectation equalities** (uniqueness via integral identity)
- **Sigma algebra manipulations** (sub-σ-algebra relationships)
- **Type class instance management** (explicit `haveI` declarations)

## 📚 Contents

### Files in This Repository

```
skills/
└── formal-verification/
    ├── ABOUT.md                      # Category overview
    └── lean4-theorem-proving/
        └── SKILL.md                  # Main skill (13KB, comprehensive)
```

### What's in SKILL.md

- **The Build-First Principle** - Lean workflow fundamentals
- **Proof Development Workflow** - 4-phase systematic approach
- **Mathlib Integration** - Finding and using existing lemmas
- **Managing Axioms and Sorries** - Documentation and elimination patterns
- **Common Patterns** - Domain-specific proof strategies
- **Tactics Reference** - Essential and specialized tactics
- **Commit Message Patterns** - Based on successful Lean projects
- **Red Flags** - Anti-patterns to avoid
- **Quality Checklist** - Pre-commit verification
- **Learning Resources** - Official docs and community links

## 🎯 When to Use This Skill

**Perfect for:**
- Formalizing mathematical theorems (analysis, algebra, topology)
- Working with measure theory and probability
- Contributing to mathlib
- Managing complex proof development
- Converting axioms to proven lemmas
- Dealing with type class inference issues

**Especially helpful when:**
- Starting a new Lean formalization project
- Learning Lean 4 from Lean 3 or other proof assistants
- Stuck with type class synthesis errors
- Managing multiple interrelated proofs
- Working on real analysis, probability, or abstract algebra

## 🔧 Requirements

- [Claude Code](https://claude.com/claude-code) CLI tool
- Unix-like system (macOS, Linux) for standard skills directory
- (Optional) Lean 4 installed for testing the guidance

## 🤝 Contributing

This skill was developed from real-world Lean 4 formalization work. Contributions welcome!

**Ways to contribute:**
- Share additional proof patterns
- Add domain-specific tactics and strategies
- Submit examples from successful projects
- Report issues or unclear guidance
- Suggest improvements to the workflow

## 📄 License

MIT License - feel free to use, modify, and share.

## 🙏 Acknowledgments

This skill was developed from patterns observed in:
- Real-world Lean 4 formalization projects (de Finetti theorem, exchangeability)
- Mathlib contribution experience
- Common pitfalls and solutions from the Lean community
- Successful proof development workflows

## 📚 Related Resources

**Official Lean 4:**
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean Zulip Chat](https://leanprover.zulipchat.com/)

**Claude Code:**
- [Claude Code Documentation](https://docs.claude.com/claude-code)
- [Skills Documentation](https://docs.claude.com/claude-code/skills)

## 🚦 Status

**Version:** 1.0.0
**Status:** Stable and production-ready
**Last Updated:** October 2025

## ❓ FAQ

### Does this require Lean 4 to be installed?

No! The skill teaches Claude Code how to work with Lean 4, but Claude Code itself doesn't need Lean installed. If you're working on Lean projects, you'll obviously need Lean 4 installed locally.

### Will this work with Claude Code updates?

Yes! Skills are read from the filesystem and work with the standard Claude Code skills system.

### Can I modify the skill for my specific needs?

Absolutely! Clone this repo, modify `SKILL.md` to add your project-specific patterns, and use your customized version.

### Does this work for Lean 3?

This skill is specifically designed for Lean 4. Lean 3 has different syntax and tactics. You'd need to adapt it significantly for Lean 3.

### How is this different from Claude's general Lean knowledge?

Claude has general knowledge about Lean from training data. This skill provides:
- Specific workflows (structure before solve, one sorry at a time)
- Project-specific patterns (type class management, mathlib integration)
- Quality standards (compile before commit, document sorries)
- Real-world patterns from successful projects

It's like having a Lean 4 expert mentor coaching Claude on best practices.

---

**Made with 🧠 by Claude Code users, for Claude Code users**

If this helps your Lean formalization work, consider starring the repo and sharing with others!
