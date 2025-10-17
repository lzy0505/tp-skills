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

### Prerequisites

This skill requires the **[Superpowers](https://github.com/obra/superpowers)** plugin for Claude Code. Superpowers is a skills library system created by Jesse Vincent that extends Claude Code with structured workflows and domain expertise.

**Install Superpowers first:**

1. Ensure you have **Claude Code 2.0.13 or later**
2. In Claude Code, run:
   ```
   /plugin marketplace add obra/superpowers-marketplace
   /plugin install superpowers@superpowers-marketplace
   ```

For more details, visit: https://github.com/obra/superpowers

### Installing This Skill

Once Superpowers is installed:

1. **Clone this repository:**
   ```bash
   git clone https://github.com/cameronfreer/lean4-theorem-proving-skill.git
   cd lean4-theorem-proving-skill
   ```

2. **Copy to your Superpowers skills directory:**
   ```bash
   cp -r skills/formal-verification ~/.config/superpowers/skills/skills/
   ```

3. **Verify installation:**
   ```bash
   ls ~/.config/superpowers/skills/skills/formal-verification/lean4-theorem-proving/
   # Should show: SKILL.md
   ```

The skill is now available in all Claude Code sessions!

### Alternative: Use Skill Files Directly

If you want to use the skill content without Superpowers, you can reference the skill files directly in your prompts or project documentation:

1. Clone the repository
2. Reference the content in `skills/formal-verification/lean4-theorem-proving/SKILL.md`
3. Copy relevant sections into your project's `CLAUDE.md` or prompt Claude Code to read the file

This approach works but won't have automatic activation based on context.

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

- [Claude Code](https://claude.com/claude-code) CLI tool (version 2.0.13 or later)
- [Superpowers plugin](https://github.com/obra/superpowers) for Claude Code skills system
- Unix-like system (macOS, Linux) recommended
- (Optional) Lean 4 installed for working on Lean projects

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

**Claude Code & Superpowers:**
- [Claude Code Documentation](https://docs.claude.com/claude-code)
- [Superpowers Plugin](https://github.com/obra/superpowers) - Skills system for Claude Code
- [Superpowers Skills Library](https://github.com/obra/superpowers-skills) - Community skills

## 🚦 Status

**Version:** 1.0.0
**Status:** Stable and production-ready
**Last Updated:** October 2025

## ❓ FAQ

### What is Superpowers and do I need it?

**Superpowers** is a plugin for Claude Code created by Jesse Vincent that provides a skills system for teaching Claude structured workflows. This Lean 4 skill is packaged for Superpowers.

**Do you need it?**
- **Yes, for automatic activation** - The skill will automatically load when working on Lean files
- **No, for manual use** - You can copy the SKILL.md content into your project documentation or reference it directly

Install Superpowers: https://github.com/obra/superpowers

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
