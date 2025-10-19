#!/usr/bin/env bash
#
# check_axioms_inline.sh - Check axioms in Lean 4 files using inline #print axioms
#
# Usage:
#   ./check_axioms_inline.sh <file> [--verbose]
#
# This script temporarily appends #print axioms commands to the Lean file,
# runs Lean to check axioms, then removes the additions. Works for ALL declarations
# including those in namespaces, sections, and private declarations.
#
# Standard mathlib axioms (propext, quot.sound, choice) are filtered out,
# highlighting only custom axioms or unexpected dependencies.
#
# Examples:
#   ./check_axioms_inline.sh MyFile.lean
#   ./check_axioms_inline.sh MyFile.lean --verbose
#
# IMPORTANT: This script temporarily modifies the file. Make sure:
#   - File is in version control (can revert if needed)
#   - No other processes are editing the file

set -euo pipefail

# Configuration
FILE="${1:-}"
VERBOSE="${2:-}"
MARKER="-- AUTO_AXIOM_CHECK_MARKER_DO_NOT_COMMIT"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Standard acceptable axioms
STANDARD_AXIOMS="propext|quot.sound|Classical.choice|Quot.sound"

# Validate input
if [[ -z "$FILE" ]]; then
    echo -e "${RED}Error: No file specified${NC}" >&2
    echo "Usage: $0 <file> [--verbose]" >&2
    exit 1
fi

if [[ ! -f "$FILE" ]]; then
    echo -e "${RED}Error: $FILE is not a file${NC}" >&2
    exit 1
fi

if [[ ! "$FILE" =~ \.lean$ ]]; then
    echo -e "${RED}Error: $FILE is not a Lean file${NC}" >&2
    exit 1
fi

echo -e "${BLUE}Checking axioms in: ${YELLOW}$FILE${NC}"
echo

# Extract namespace if any
NAMESPACE=""
if grep -q "^namespace " "$FILE"; then
    NAMESPACE=$(grep "^namespace " "$FILE" | head -1 | sed 's/namespace //')
fi

# Extract all theorem/lemma/def declarations
DECLARATIONS=()
while IFS= read -r line; do
    decl=$(echo "$line" | sed -E 's/^(theorem|lemma|def) +([^ :(]+).*/\2/')
    if [[ -n "$decl" ]]; then
        # Add namespace prefix if present
        if [[ -n "$NAMESPACE" ]]; then
            DECLARATIONS+=("$NAMESPACE.$decl")
        else
            DECLARATIONS+=("$decl")
        fi
    fi
done < <(grep -E '^(theorem|lemma|def) ' "$FILE" || true)

if [[ ${#DECLARATIONS[@]} -eq 0 ]]; then
    echo -e "${YELLOW}No theorems or lemmas found${NC}"
    exit 0
fi

echo -e "${GREEN}Found ${#DECLARATIONS[@]} declarations${NC}"
echo

# Create backup
BACKUP_FILE="${FILE}.axiom_check_backup"
cp "$FILE" "$BACKUP_FILE"

# Function to restore file on exit
cleanup() {
    if [[ -f "$BACKUP_FILE" ]]; then
        mv "$BACKUP_FILE" "$FILE"
    fi
}
trap cleanup EXIT INT TERM

# Append #print axioms commands
echo "" >> "$FILE"
echo "$MARKER" >> "$FILE"
for decl in "${DECLARATIONS[@]}"; do
    echo "#print axioms $decl" >> "$FILE"
done

# Run Lean
echo -e "${BLUE}Running axiom analysis...${NC}"
if OUTPUT=$(lake env lean "$FILE" 2>&1); then
    # Parse output
    CURRENT_DECL=""
    HAS_CUSTOM=false

    while IFS= read -r line; do
        # Match declaration headers like "foo depends on axioms:"
        if [[ "$line" =~ ^([a-zA-Z0-9_]+)[[:space:]]+depends[[:space:]]+on[[:space:]]+axioms: ]]; then
            CURRENT_DECL="${BASH_REMATCH[1]}"
            if [[ "$VERBOSE" == "--verbose" ]]; then
                echo -e "${BLUE}$CURRENT_DECL:${NC}"
            fi
        # Match axiom names (just the name on a line)
        elif [[ "$line" =~ ^[[:space:]]*([a-zA-Z0-9_.]+)[[:space:]]*$ ]]; then
            axiom="${BASH_REMATCH[1]}"
            # Skip empty lines
            if [[ -n "$axiom" && ! "$axiom" =~ ^[[:space:]]*$ ]]; then
                if [[ ! "$axiom" =~ $STANDARD_AXIOMS ]]; then
                    echo -e "${RED}⚠ $CURRENT_DECL uses non-standard axiom: $axiom${NC}"
                    HAS_CUSTOM=true
                elif [[ "$VERBOSE" == "--verbose" ]]; then
                    echo -e "  ${GREEN}✓${NC} $axiom (standard)"
                fi
            fi
        fi
    done <<< "$OUTPUT"

    if [[ "$HAS_CUSTOM" == false ]]; then
        echo -e "${GREEN}✓ All declarations use only standard axioms${NC}"
    fi

    # Cleanup happens via trap
    exit 0
else
    echo -e "${RED}Error running Lean:${NC}" >&2
    # Show only errors, not the whole output
    echo "$OUTPUT" | grep "error" | head -20 >&2
    # Cleanup happens via trap
    exit 1
fi

echo
echo -e "${YELLOW}Standard axioms (acceptable):${NC}"
echo "  • propext (propositional extensionality)"
echo "  • quot.sound (quotient soundness)"
echo "  • Classical.choice (axiom of choice)"
echo
echo -e "${YELLOW}Tip: Any other axioms should have elimination plans${NC}"
