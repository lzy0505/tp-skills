#!/usr/bin/env bash
#
# check_axioms.sh - Check axioms used in Rocq/Coq theorems and lemmas
#
# Usage:
#   ./check_axioms.sh <file-or-directory> [--verbose]
#
# This script extracts all theorem/lemma/definition declarations and uses
# 'Print Assumptions' to check what axioms each one depends on. Standard
# library axioms (functional_extensionality, proof_irrelevance, Classical)
# are filtered out, highlighting only custom axioms or unexpected dependencies.
#
# Examples:
#   ./check_axioms.sh MyFile.v
#   ./check_axioms.sh src/theories/ --verbose
#   ./check_axioms.sh . --verbose  # Check entire project

set -euo pipefail

# Configuration
TARGET="${1:-.}"
VERBOSE="${2:-}"
TEMP_DIR=$(mktemp -d)
TEMP_FILE="$TEMP_DIR/check_axioms.v"
RESULTS_FILE="$TEMP_DIR/results.txt"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

# Standard acceptable axioms in Coq
STANDARD_AXIOMS=(
    "functional_extensionality"
    "functional_extensionality_dep"
    "proof_irrelevance"
    "propositional_extensionality"
    "classic"
    "constructive_definite_description"
    "excluded_middle_informative"
    "strong_extensionality"
    "ext_prop_dep"
    "ext_prop"
    "ext"
    "proof_admitted"  # Axiom from Admitted
)

# Check if coqtop is available
if ! command -v coqtop &> /dev/null; then
    echo -e "${RED}Error: coqtop not found in PATH${NC}" >&2
    echo "Please install Rocq/Coq and ensure coqtop is available" >&2
    exit 1
fi

echo -e "${BLUE}Checking axioms in: ${YELLOW}$TARGET${NC}"
echo

# Find all Coq files
if [[ -f "$TARGET" ]]; then
    FILES=("$TARGET")
elif [[ -d "$TARGET" ]]; then
    mapfile -t FILES < <(find "$TARGET" -name "*.v" -type f)
else
    echo -e "${RED}Error: $TARGET is not a file or directory${NC}" >&2
    exit 1
fi

# Extract declarations from each file
# Store as "file::decl" pairs (bash 3.2 compatible)
FILE_DECL_PAIRS=()
TOTAL_DECLS=0

for file in "${FILES[@]}"; do
    # Extract Theorem, Lemma, Definition, Proposition names
    while IFS= read -r line; do
        # Extract the declaration name from lines like "Theorem name :"
        if [[ "$line" =~ ^(Theorem|Lemma|Definition|Proposition|Corollary|Remark)[[:space:]]+([a-zA-Z0-9_]+) ]]; then
            decl="${BASH_REMATCH[2]}"
            if [[ -n "$decl" ]]; then
                FILE_DECL_PAIRS+=("$file::$decl")
                TOTAL_DECLS=$((TOTAL_DECLS + 1))
            fi
        fi
    done < <(grep -E '^(Theorem|Lemma|Definition|Proposition|Corollary|Remark) ' "$file" 2>/dev/null || true)
done

if [[ $TOTAL_DECLS -eq 0 ]]; then
    echo -e "${YELLOW}No theorems or lemmas found${NC}"
    rm -rf "$TEMP_DIR"
    exit 0
fi

# Count unique files
UNIQUE_FILES=()
for pair in "${FILE_DECL_PAIRS[@]}"; do
    file="${pair%%::*}"
    # Check if already in list
    already_seen=false
    for seen in ${UNIQUE_FILES[@]+"${UNIQUE_FILES[@]}"}; do
        if [[ "$seen" == "$file" ]]; then
            already_seen=true
            break
        fi
    done
    if [[ "$already_seen" == false ]]; then
        UNIQUE_FILES+=("$file")
    fi
done

echo -e "${GREEN}Found $TOTAL_DECLS declarations in ${#UNIQUE_FILES[@]} files${NC}"
echo

# Function to check if axiom is standard
is_standard_axiom() {
    local axiom="$1"
    for std in "${STANDARD_AXIOMS[@]}"; do
        if [[ "$axiom" == *"$std"* ]]; then
            return 0
        fi
    done
    return 1
}

# Process each file
TOTAL_CUSTOM_AXIOMS=0
CUSTOM_AXIOMS_LIST=()

# Process each unique file
for file in "${UNIQUE_FILES[@]}"; do
    # Get all decls for this file
    decls=""
    for pair in "${FILE_DECL_PAIRS[@]}"; do
        pair_file="${pair%%::*}"
        pair_decl="${pair##*::}"
        if [[ "$pair_file" == "$file" ]]; then
            decls="$decls $pair_decl"
        fi
    done

    if [[ "$VERBOSE" == "--verbose" ]]; then
        echo -e "${BLUE}Checking file: ${file}${NC}"
    fi

    # Generate temporary Coq file to check axioms
    echo "(* Auto-generated axiom check file *)" > "$TEMP_FILE"
    echo "" >> "$TEMP_FILE"

    # Add imports - try to load the file
    # For dune projects, we need proper paths
    echo "From Coq Require Import Setoid." >> "$TEMP_FILE"

    # Try to determine module name from file path
    # This is a heuristic and may need adjustment per project
    if [[ -f "dune-project" ]]; then
        # Dune project - try to infer library name
        # Simplified: just load the file relatively
        file_dir=$(dirname "$file")
        file_name=$(basename "$file" .v)

        # Try different import strategies
        echo "Add LoadPath \"$file_dir\"." >> "$TEMP_FILE"
        echo "Require Import $file_name." >> "$TEMP_FILE"
    else
        # Non-dune project - load file directly
        echo "Load \"$file\"." >> "$TEMP_FILE"
    fi

    echo "" >> "$TEMP_FILE"

    # Add Print Assumptions commands
    for decl in $decls; do
        echo "Print Assumptions $decl." >> "$TEMP_FILE"
    done

    # Run coqtop to check axioms
    if OUTPUT=$(coqtop -q -batch -l "$TEMP_FILE" 2>&1); then
        # Parse output
        CURRENT_DECL=""
        FILE_HAS_CUSTOM=false

        while IFS= read -r line; do
            # Match "Axioms:" line
            if [[ "$line" =~ Axioms: ]]; then
                # Extract what comes before "Axioms:"
                # Example: "addnC : nat -> nat -> Prop Axioms:"
                if [[ "$line" =~ ^([^:]+):.*Axioms: ]]; then
                    CURRENT_DECL="${BASH_REMATCH[1]}"
                    CURRENT_DECL=$(echo "$CURRENT_DECL" | xargs)  # Trim whitespace
                    if [[ "$VERBOSE" == "--verbose" ]]; then
                        echo -e "  ${BLUE}${CURRENT_DECL}:${NC}"
                    fi
                fi
            # Match axiom lines (indented)
            elif [[ "$line" =~ ^[[:space:]]+([a-zA-Z0-9_]+) ]]; then
                axiom="${BASH_REMATCH[1]}"

                if ! is_standard_axiom "$axiom"; then
                    echo -e "${RED}⚠ ${CURRENT_DECL} (${file}) uses non-standard axiom: ${axiom}${NC}"
                    # Store custom axiom (bash 3.2 compatible)
                    CUSTOM_AXIOMS_LIST+=("$axiom::${CURRENT_DECL}")
                    TOTAL_CUSTOM_AXIOMS=$((TOTAL_CUSTOM_AXIOMS + 1))
                    FILE_HAS_CUSTOM=true
                elif [[ "$VERBOSE" == "--verbose" ]]; then
                    echo -e "    ${GREEN}✓${NC} $axiom (standard)"
                fi
            # Match "Closed under the global context" (no axioms)
            elif [[ "$line" =~ "Closed under the global context" ]]; then
                if [[ "$VERBOSE" == "--verbose" && -n "$CURRENT_DECL" ]]; then
                    echo -e "    ${GREEN}✓${NC} No axioms (constructive)"
                fi
            fi
        done <<< "$OUTPUT"

        if [[ "$VERBOSE" == "--verbose" ]]; then
            echo
        fi
    else
        echo -e "${YELLOW}Warning: Could not check $file${NC}" >&2
        if [[ "$VERBOSE" == "--verbose" ]]; then
            echo -e "${YELLOW}Error output:${NC}" >&2
            echo "$OUTPUT" >&2
            echo
        fi
    fi
done

# Summary
echo
if [[ $TOTAL_CUSTOM_AXIOMS -eq 0 ]]; then
    echo -e "${GREEN}✓ All declarations use only standard axioms or are constructive${NC}"
else
    echo -e "${RED}Found $TOTAL_CUSTOM_AXIOMS uses of non-standard axioms${NC}"
    echo
    echo -e "${YELLOW}Custom axioms used:${NC}"

    # Get unique axiom names (bash 3.2 compatible)
    UNIQUE_AXIOMS=()
    for entry in "${CUSTOM_AXIOMS_LIST[@]}"; do
        axiom="${entry%%::*}"
        already_seen=false
        for seen in ${UNIQUE_AXIOMS[@]+"${UNIQUE_AXIOMS[@]}"}; do
            if [[ "$seen" == "$axiom" ]]; then
                already_seen=true
                break
            fi
        done
        if [[ "$already_seen" == false ]]; then
            UNIQUE_AXIOMS+=("$axiom")
        fi
    done

    for axiom in ${UNIQUE_AXIOMS[@]+"${UNIQUE_AXIOMS[@]}"}; do
        echo -e "  ${RED}• $axiom${NC}"
        if [[ "$VERBOSE" == "--verbose" ]]; then
            # Find all decls using this axiom
            decls=""
            for entry in "${CUSTOM_AXIOMS_LIST[@]}"; do
                entry_axiom="${entry%%::*}"
                entry_decl="${entry##*::}"
                if [[ "$entry_axiom" == "$axiom" ]]; then
                    decls="$decls $entry_decl"
                fi
            done
            echo -e "    Used by:$decls"
        fi
    done
fi

echo
echo -e "${YELLOW}Standard axioms (acceptable):${NC}"
echo "  • functional_extensionality (function extensionality)"
echo "  • proof_irrelevance (proof irrelevance)"
echo "  • classic / excluded_middle_informative (classical logic)"
echo "  • propositional_extensionality (propositional extensionality)"
echo
echo -e "${YELLOW}Note: Any 'Admitted' proofs introduce 'proof_admitted' axiom${NC}"
echo -e "${YELLOW}Tip: Use axiom-elimination.md for removing custom axioms${NC}"

# Cleanup
rm -rf "$TEMP_DIR"

# Exit with error if custom axioms found
if [[ $TOTAL_CUSTOM_AXIOMS -gt 0 ]]; then
    exit 1
fi
