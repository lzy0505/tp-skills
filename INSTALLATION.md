# Installation Guide

Detailed installation instructions for Lean 4 Skills.

## Quick Start

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

## Platform-Specific Setup

### Windows 11 Users

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

### macOS Users

No special setup required. Use Terminal with the installation commands above.

### Linux Users

No special setup required. Use your preferred shell with the installation commands above.

## Lean LSP Server

**The LSP server provides 30x faster feedback than build-only workflows.**

If you're using Claude Code or Claude Desktop, you can install the Lean LSP MCP server for instant proof state inspection, integrated search, and parallel tactic testing.

### Installation

**Full instructions:** https://github.com/oOo0oOo/lean-lsp-mcp

**Quick summary:**
1. Install the Lean LSP MCP server (follow repo instructions)
2. Install ripgrep: `brew install ripgrep` (macOS) or see https://github.com/BurntSushi/ripgrep#installation
3. Configure Claude Code/Desktop to use the server
4. **Before first use:** Run `lake build` in your Lean project to avoid timeouts
5. Restart Claude

**One-time setup:** ~5 minutes

**Important prerequisites:**
- **ripgrep (rg):** Required for `lean_local_search` tool. Install and ensure it's in your PATH.
- **lake build:** Run this in your project before starting the LSP server to avoid client timeouts during initial setup.

### What You Get

- **Instant feedback:** < 1 second vs 30+ seconds building
- **Goal visibility:** See exactly what needs proving at each step
- **Parallel testing:** Test multiple tactics at once with `lean_multi_attempt`
- **Integrated search:** Find lemmas without leaving your workflow
- **No guessing:** Verify before editing, not after slow builds

### Verification

After installation, test with:
```bash
# In Claude Code, test these commands:
mcp__lean-lsp__lean_goal(file_path, line)
mcp__lean-lsp__lean_local_search("add_comm")
```

If they work, you're ready! See `lean4-theorem-proving/references/lean-lsp-server.md` for complete workflows.

## Requirements

**For lean4-theorem-proving:**
- Claude Code 2.0.13+ (marketplace) OR
- Claude.ai Pro/Max/Team/Enterprise OR
- Any Claude (CLAUDE.md method)

**For lean4-memories (additional):**
- MCP memory server (simple config file edit - [setup guide](lean4-memories/README.md#installation))
- Claude Desktop or Claude Code with MCP support

**For Lean LSP server (optional but highly recommended):**
- Claude Code or Claude Desktop with MCP support
- Lean LSP MCP server installed (see above)

## Troubleshooting

### Skill Not Activating

**Check:**
1. Files are in `~/.claude/skills/` directory
2. Skill is enabled: `/plugin list` should show it
3. You're working with `.lean` files

### LSP Server Not Working

**Check:**
1. Lean LSP MCP server is installed and configured
2. Claude Code/Desktop is restarted
3. Test basic commands (see Verification above)
4. Check server logs for errors

**Full troubleshooting:** https://github.com/oOo0oOo/lean-lsp-mcp/issues

### Windows Issues

**Git Bash not found:**
- Install Git for Windows from https://git-scm.com/download/win
- Restart terminal after installation

**Permission errors:**
- Run Git Bash as Administrator
- Or use VSCode extension (no Bash required)

## Getting Help

- **Lean 4 Skills issues:** https://github.com/cameronfreer/lean4-skills/issues
- **Lean LSP server issues:** https://github.com/oOo0oOo/lean-lsp-mcp/issues
- **Claude Code help:** `/help` or https://docs.claude.com/en/docs/claude-code
