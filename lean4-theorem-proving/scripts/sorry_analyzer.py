#!/usr/bin/env python3
"""
sorry_analyzer.py - Extract and analyze sorry statements in Lean 4 code

Usage:
    ./sorry_analyzer.py <file-or-directory> [--format=text|json|markdown]

This script finds all 'sorry' instances in Lean files and extracts:
- Location (file, line number)
- Context (surrounding code)
- Documentation (TODO comments)
- Type information (from goal state if available)

Examples:
    ./sorry_analyzer.py MyFile.lean
    ./sorry_analyzer.py src/DeFinetti/ --format=markdown
    ./sorry_analyzer.py . --format=json > sorries.json
"""

import re
import sys
import json
from pathlib import Path
from dataclasses import dataclass, asdict
from typing import List, Optional

@dataclass
class Sorry:
    """Represents a sorry instance with context"""
    file: str
    line: int
    context_before: List[str]
    context_after: List[str]
    documentation: List[str]
    in_declaration: Optional[str] = None

def extract_declaration_name(lines: List[str], sorry_idx: int) -> Optional[str]:
    """Extract the theorem/lemma/def name containing this sorry"""
    # Search backwards for declaration
    for i in range(sorry_idx - 1, max(0, sorry_idx - 50), -1):
        match = re.match(r'^\s*(theorem|lemma|def|example)\s+(\w+)', lines[i])
        if match:
            return f"{match.group(1)} {match.group(2)}"
    return None

def extract_documentation(lines: List[str], sorry_idx: int) -> List[str]:
    """Extract TODO/NOTE comments near the sorry"""
    docs = []
    # Check lines after sorry
    for i in range(sorry_idx + 1, min(len(lines), sorry_idx + 10)):
        line = lines[i].strip()
        if line.startswith('--'):
            comment = line[2:].strip()
            if any(keyword in comment.upper() for keyword in ['TODO', 'NOTE', 'FIXME', 'STRATEGY', 'DEPENDENCIES']):
                docs.append(comment)
        elif line and not line.startswith('--'):
            break
    return docs

def find_sorries_in_file(filepath: Path) -> List[Sorry]:
    """Find all sorries in a single Lean file"""
    try:
        with open(filepath, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"Warning: Could not read {filepath}: {e}", file=sys.stderr)
        return []

    sorries = []
    for i, line in enumerate(lines):
        # Look for sorry (not in comments)
        if 'sorry' in line:
            # Simple check: not in a comment
            code_part = line.split('--')[0]
            if 'sorry' in code_part:
                context_before = [l.rstrip() for l in lines[max(0, i-3):i]]
                context_after = [l.rstrip() for l in lines[i+1:min(len(lines), i+4)]]

                sorry = Sorry(
                    file=str(filepath),
                    line=i + 1,  # 1-indexed
                    context_before=context_before,
                    context_after=context_after,
                    documentation=extract_documentation(lines, i),
                    in_declaration=extract_declaration_name(lines, i)
                )
                sorries.append(sorry)

    return sorries

def find_sorries(target: Path) -> List[Sorry]:
    """Find all sorries in target file or directory"""
    if target.is_file():
        return find_sorries_in_file(target)
    elif target.is_dir():
        sorries = []
        for lean_file in target.rglob("*.lean"):
            sorries.extend(find_sorries_in_file(lean_file))
        return sorries
    else:
        raise ValueError(f"{target} is not a file or directory")

def format_text(sorries: List[Sorry]) -> str:
    """Format sorries as human-readable text"""
    output = []
    output.append(f"Found {len(sorries)} sorry statement(s)\n")
    output.append("=" * 80)

    for i, sorry in enumerate(sorries, 1):
        output.append(f"\n[{i}] {sorry.file}:{sorry.line}")
        if sorry.in_declaration:
            output.append(f"    In: {sorry.in_declaration}")

        if sorry.documentation:
            output.append("    Documentation:")
            for doc in sorry.documentation:
                output.append(f"      • {doc}")

        output.append("\n    Context:")
        for line in sorry.context_before[-2:]:
            output.append(f"      {line}")
        output.append(f"      >>> SORRY <<<")
        for line in sorry.context_after[:2]:
            output.append(f"      {line}")
        output.append("")

    return "\n".join(output)

def format_markdown(sorries: List[Sorry]) -> str:
    """Format sorries as Markdown"""
    output = []
    output.append(f"# Sorry Analysis Report\n")
    output.append(f"**Total sorries found:** {len(sorries)}\n")

    # Group by file
    by_file = {}
    for sorry in sorries:
        by_file.setdefault(sorry.file, []).append(sorry)

    for filepath, file_sorries in sorted(by_file.items()):
        output.append(f"## {filepath}\n")
        output.append(f"**Count:** {len(file_sorries)}\n")

        for sorry in file_sorries:
            output.append(f"### Line {sorry.line}")
            if sorry.in_declaration:
                output.append(f"**Declaration:** `{sorry.in_declaration}`\n")

            if sorry.documentation:
                output.append("**Documentation:**")
                for doc in sorry.documentation:
                    output.append(f"- {doc}")
                output.append("")

            output.append("**Context:**")
            output.append("```lean")
            for line in sorry.context_before[-2:]:
                output.append(line)
            output.append("sorry  -- ⚠️")
            for line in sorry.context_after[:2]:
                output.append(line)
            output.append("```\n")

    return "\n".join(output)

def format_json(sorries: List[Sorry]) -> str:
    """Format sorries as JSON"""
    return json.dumps({
        'total_count': len(sorries),
        'sorries': [asdict(s) for s in sorries]
    }, indent=2)

def main():
    if len(sys.argv) < 2:
        print(__doc__)
        sys.exit(1)

    target = Path(sys.argv[1])
    format_type = 'text'

    if len(sys.argv) > 2:
        arg = sys.argv[2]
        if arg.startswith('--format='):
            format_type = arg.split('=')[1]

    if not target.exists():
        print(f"Error: {target} does not exist", file=sys.stderr)
        sys.exit(1)

    # Find all sorries
    sorries = find_sorries(target)

    # Format output
    if format_type == 'json':
        print(format_json(sorries))
    elif format_type == 'markdown':
        print(format_markdown(sorries))
    else:
        print(format_text(sorries))

    # Exit code: 0 if no sorries, 1 if sorries found
    sys.exit(0 if len(sorries) == 0 else 1)

if __name__ == '__main__':
    main()
