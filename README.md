# Lean 4 Theorem Proving - Claude Skill

A comprehensive [Claude Skill](https://www.anthropic.com/news/skills) for systematic development of formal proofs in Lean 4.

## 🎯 What is This?

This is a **Claude Skill** that teaches Claude how to work effectively with Lean 4 theorem proving. Claude Skills are custom tools that provide specialized knowledge and workflows, available across Claude.ai, API, and Code.

**What this skill provides:**
- 📚 **Systematic workflow** for proof development (structure → helpers → incremental filling)
- 🔧 **Type class management** patterns for sub-σ-algebras and instance inference
- 📖 **Mathlib integration** guide (finding lemmas, imports, naming conventions)
- 🎓 **Domain-specific patterns** for measure theory, probability, and algebra
- ✅ **Quality standards** (compile before commit, document sorries, eliminate axioms)
- 💡 **Real-world examples** from successful Lean formalization projects

## 🚀 Installation

### Method 1: Marketplace (Recommended for Claude Code)

Install directly from the marketplace using Claude Code's plugin system:

```
/plugin marketplace add cameronfreer/lean4-theorem-proving-skill
/plugin install lean4-theorem-proving
```

The skill will automatically load when Claude detects you're working on Lean files!

### Method 2: Manual Installation

Copy the skill to your local Claude skills directory:

```bash
# Clone the repository
git clone https://github.com/cameronfreer/lean4-theorem-proving-skill.git
cd lean4-theorem-proving-skill

# Copy to Claude skills directory
cp -r lean4-theorem-proving ~/.claude/skills/

# Verify installation
ls ~/.claude/skills/lean4-theorem-proving/
# Should show: SKILL.md
```

The skill is now available in all Claude sessions (Claude.ai, API, and Code)!

### Method 3: Project-Specific (CLAUDE.md)

For project-specific use without installation:

1. Clone this repository
2. Copy relevant sections from `lean4-theorem-proving/SKILL.md` into your project's `CLAUDE.md`
3. Or reference the skill file directly in your prompts

## 📖 Usage

### Automatic Activation

Claude automatically loads this skill when you:
- Work on `.lean` files
- Mention Lean 4, theorem proving, or formal verification
- Prove theorems or manage sorries/axioms
- Ask about mathlib or type class issues

No manual invocation needed - Claude sees the skill in its chain of thought!

### Explicit Invocation

You can explicitly request the skill if desired:

```
Use the lean4-theorem-proving skill to help me structure this proof
```

### Query the Skill

Ask about specific guidance:

```
What does the Lean 4 skill recommend for managing sorries?
How should I handle type class inference issues?
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
- **Commit message patterns** from successful Lean projects

## 📚 Contents

```
lean4-theorem-proving/
└── SKILL.md      # Complete skill (32KB of Lean 4 expertise)
```

**What's in SKILL.md:**
- The Build-First Principle
- 4-Phase Proof Development Workflow
- Mathlib Integration Guide (with comprehensive search techniques)
- **Command-Line Search Patterns** (find/grep workflows for mathlib and local files)
- **Interactive Exploration** (#check, #print, #eval, debugging commands)
- **The simp Tactic Deep Dive** (when to use, pitfalls, best practices)
- **Expanded Error Messages** (10 common errors with concrete fixes)
- Managing Axioms and Sorries
- Measure Theory Patterns
- Tactics Reference
- Commit Message Patterns
- Quality Checklist
- Learning Resources

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

- **Claude Code 2.0.13+** (for marketplace installation), OR
- **Claude.ai Pro/Max/Team/Enterprise** (for web/API), OR
- **Just Claude** (for CLAUDE.md method)
- (Optional) Lean 4 installed for working on Lean projects

## 🤝 Contributing

This skill was developed from real-world Lean 4 formalization work. Contributions welcome!

**Ways to contribute:**
- Share additional proof patterns
- Add domain-specific tactics and strategies
- Submit examples from successful projects
- Report issues or unclear guidance
- Suggest improvements to the workflow

Open an issue or PR at: https://github.com/cameronfreer/lean4-theorem-proving-skill

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

**Claude Skills:**
- [Claude Skills Announcement](https://www.anthropic.com/news/skills)
- [Claude Skills Repository](https://github.com/anthropics/skills) - Official examples
- [Claude Code Documentation](https://docs.claude.com/claude-code)

## 🚦 Status

**Version:** 1.2.0
**Status:** Production-ready
**Last Updated:** October 2025

**Recent updates:**
- v1.2.0: Optimized for balance and best practices - balanced coverage across algebra, topology, analysis, probability; compressed by 364 lines while maintaining quality
- v1.1.0: Added simp tactic deep dive, interactive exploration commands, and 10 common error messages with fixes
- v1.0.0: Initial release with core workflow and mathlib integration

## ❓ FAQ

### What are Claude Skills?

Claude Skills are custom tools announced by Anthropic in October 2025 that teach Claude specialized tasks. Skills are folders containing instructions, scripts, and resources that Claude loads dynamically when relevant. They work across Claude.ai, API, and Code.

Learn more: https://www.anthropic.com/news/skills

### Do I need a subscription?

- **Claude Code (marketplace)**: Available to all Claude Code users
- **Manual installation (~/.claude/skills)**: Available to all users
- **Claude.ai/API**: Skills feature requires Pro, Max, Team, or Enterprise

### Does this require Lean 4?

No! The skill teaches Claude how to work with Lean 4. You only need Lean 4 installed if you're actually working on Lean projects locally.

### How is this different from Claude's general Lean knowledge?

Claude has general knowledge about Lean from training data. This skill provides:
- **Specific workflows** (structure before solve, one sorry at a time)
- **Project patterns** (type class management, mathlib integration)
- **Quality standards** (compile before commit, document sorries)
- **Real-world patterns** from successful projects

It's like having a Lean 4 expert mentor coaching Claude on best practices.

### Can I modify the skill?

Absolutely! Clone this repo, modify `lean4-theorem-proving/SKILL.md` to add your project-specific patterns, and either:
- Use your fork as a custom marketplace
- Install locally from your modified version
- Add custom content to your project's CLAUDE.md

### Does this work with Superpowers?

While this is now packaged as an official Claude Skill, you can still use it with Superpowers by copying the skill folder to `~/.config/superpowers/skills/skills/`. However, we recommend using the official Claude Skills installation for better integration.

---

**Made with 🧠 for the Lean formalization community**

If this helps your Lean 4 work, please ⭐ star the repo and share with others working on formal mathematics!
