# Lean 4 Skills for Claude

Claude Skills for systematic development of formal proofs in Lean 4.

## Skills in This Repository

| Skill | Description | Standalone | Requirements |
|-------|-------------|------------|--------------|
| **[lean4-theorem-proving](lean4-theorem-proving/)** | Core workflows, 16 automation tools, best practices | ✅ Yes | None |
| **[lean4-memories](lean4-memories/)** | Persistent learning across sessions | ❌ No | MCP memory server |

## Quick Start

### Installation

**Via Marketplace (Recommended):**
```bash
/plugin marketplace add cameronfreer/lean4-skills
/plugin install lean4-theorem-proving    # Core skill
/plugin install lean4-memories           # Optional memory skill
```

**Manual Installation:**
```bash
git clone https://github.com/cameronfreer/lean4-skills.git
cd lean4-skills

# Install core skill (required)
cp -r lean4-theorem-proving ~/.claude/skills/

# Install memory skill (optional)
cp -r lean4-memories ~/.claude/skills/
```

**Windows 11 Users:**

Claude Code requires Bash, which isn't installed by default on Windows 11.

**Option 1: Use Git Bash (simplest)**
1. Install [Git for Windows](https://git-scm.com/download/win) (includes Git Bash)
2. Open Git Bash
3. Start Claude Code: `claude`
4. Run installation commands above

**Option 2: VSCode Extension**
- Install [Claude Code for VS Code](https://marketplace.visualstudio.com/items?itemName=anthropic.claude-code)
- No Bash required
- Full documentation: https://docs.claude.com/en/docs/claude-code/vs-code

### Usage

Skills activate automatically when you work on Lean 4 files. No manual invocation needed!

**Toggle skills on/off:**
```bash
/plugin disable lean4-memories    # Disable memory skill
/plugin enable lean4-memories     # Re-enable memory skill
```

## lean4-theorem-proving

Systematic workflows for Lean 4 proof development.

**What you get:**
- 4-Phase proof development workflow (structure → helpers → incremental → type classes)
- 16 automation scripts (search, analysis, verification, refactoring)
- Type class management patterns
- mathlib integration guide
- Domain-specific tactics (measure theory, probability, algebra)

**Perfect for:**
- Any Lean 4 formalization project
- Learning Lean 4 from other proof assistants
- Managing sorries, axioms, and type class issues
- Contributing to mathlib

➡️ **[Full Documentation](lean4-theorem-proving/README.md)**

## lean4-memories

Optional persistent learning across Lean 4 sessions.

**What you get:**
- Remember successful proof patterns
- Avoid repeating failed approaches (infinite loops, timeouts)
- Learn project-specific conventions
- Track theorem dependencies

**Perfect for:**
- Multi-session projects (days/weeks/months)
- Repeated proof patterns
- Team projects with shared knowledge

**Requires:** MCP memory server configuration

➡️ **[Full Documentation](lean4-memories/README.md)**

## How They Work Together

**Example: Proving `condExp μ m X =ᵐ[μ] condExp μ m Y`**

**lean4-theorem-proving says:** "Try `condExp_unique` from mathlib"

**lean4-memories adds:** "Similar goals in this project used `condExp_unique` + `ae_eq` pattern (success rate: 3/3)"

Result: Faster proofs with project-specific context!

## Requirements

**For lean4-theorem-proving:**
- Claude Code 2.0.13+ (marketplace) OR
- Claude.ai Pro/Max/Team/Enterprise OR
- Any Claude (CLAUDE.md method)

**For lean4-memories (additional):**
- MCP memory server (simple config file edit - [setup guide](lean4-memories/README.md#installation))
- Claude Desktop or Claude Code with MCP support

## Documentation

- **[lean4-theorem-proving/README.md](lean4-theorem-proving/README.md)** - Core skill guide
- **[lean4-memories/README.md](lean4-memories/README.md)** - Memory skill guide
- **[lean4-theorem-proving/scripts/](lean4-theorem-proving/scripts/)** - 16 automation tools
- **[lean4-theorem-proving/references/](lean4-theorem-proving/references/)** - Detailed guides

## Status

**Version:** 3.0.0
**Status:** Production-ready
**Last Updated:** October 2025

Recent updates:
- v3.0.0: Added lean4-memories skill (optional MCP memory integration)
- v2.1.0: Added 16 automation scripts (search, analysis, verification)
- v2.0.0: Progressive disclosure restructuring

## Contributing

Contributions welcome! Open an issue or PR at https://github.com/cameronfreer/lean4-skills

## License

MIT License - see [LICENSE](LICENSE)
