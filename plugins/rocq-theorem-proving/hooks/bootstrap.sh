#!/bin/bash
# Bootstrap env for the Rocq/Coq session so commands can reference plugin scripts reliably.

set -euo pipefail

# --- Sanity: hooks get this; commands do not. Fail fast if missing.
: "${CLAUDE_PLUGIN_ROOT:?missing CLAUDE_PLUGIN_ROOT in hook context}"

# Optional: where Claude tells us to persist env vars for the whole session.
ENV_OUT="${CLAUDE_ENV_FILE:-}"

# Check for Rocq/Coq installation
COQC_BIN="$(command -v coqc || true)"
if [[ -z "${COQC_BIN}" ]]; then
  echo "WARN: No coqc (Rocq/Coq compiler) found in PATH; compilation will fail." >&2
fi

# Check for build system (prefer dune)
BUILD_SYSTEM=""
DUNE_BIN="$(command -v dune || true)"
if [[ -n "${DUNE_BIN}" ]]; then
  BUILD_SYSTEM="dune"
else
  # Fallback: check for coq_makefile
  COQMAKEFILE_BIN="$(command -v coq_makefile || true)"
  if [[ -n "${COQMAKEFILE_BIN}" ]]; then
    BUILD_SYSTEM="coq_makefile"
  elif [[ -n "${COQC_BIN}" ]]; then
    BUILD_SYSTEM="coqc"
  fi
fi

# Check for LSP server (coq-lsp)
COQLSP_BIN="$(command -v coq-lsp || true)"
if [[ -z "${COQLSP_BIN}" ]]; then
  echo "INFO: No coq-lsp found; consider installing for faster interactive development." >&2
fi

# Resolve python (prefer python3, fall back to python).
PYTHON_BIN="$(command -v python3 || true)"
if [[ -z "${PYTHON_BIN}" ]]; then
  PYTHON_BIN="$(command -v python || true)"
fi
if [[ -z "${PYTHON_BIN}" ]]; then
  echo "WARN: No python interpreter found in PATH; automation scripts will fail." >&2
fi

# Candidate locations for the admit analyzer (support both layouts):
#   (A) plugin-level:   plugins/rocq-theorem-proving/scripts/admit_analyzer.py
#   (B) skill-scoped:   plugins/rocq-theorem-proving/skills/rocq-theorem-proving/scripts/admit_analyzer.py
CANDIDATES=(
  "${CLAUDE_PLUGIN_ROOT}/scripts/admit_analyzer.py"
  "${CLAUDE_PLUGIN_ROOT}/skills/rocq-theorem-proving/scripts/admit_analyzer.py"
)

ANALYZER_PATH=""
for f in "${CANDIDATES[@]}"; do
  if [[ -f "$f" ]]; then
    ANALYZER_PATH="$f"
    break
  fi
done

# Tools dir = directory containing the analyzer if we found it; else default to plugin-level scripts/
TOOLS_DIR=""
if [[ -n "${ANALYZER_PATH}" ]]; then
  TOOLS_DIR="$(cd "$(dirname "$ANALYZER_PATH")" && pwd)"
else
  if [[ -d "${CLAUDE_PLUGIN_ROOT}/scripts" ]]; then
    TOOLS_DIR="$(cd "${CLAUDE_PLUGIN_ROOT}/scripts" && pwd)"
  fi
fi

# Make analyzer executable if present.
if [[ -n "${ANALYZER_PATH}" && -f "${ANALYZER_PATH}" ]]; then
  chmod +x "${ANALYZER_PATH}" || true
fi

# Copy scripts to workspace to avoid parameter substitution in commands.
# This makes commands immune to Claude Code's ${...} security filter.
WORKSPACE_TOOLS_DIR=".claude/tools/rocq"
mkdir -p "${WORKSPACE_TOOLS_DIR}"

# Stage admit_analyzer (already found above)
if [[ -n "${ANALYZER_PATH}" && -f "${ANALYZER_PATH}" ]]; then
  cp -f "${ANALYZER_PATH}" "${WORKSPACE_TOOLS_DIR}/admit_analyzer.py"
  chmod +x "${WORKSPACE_TOOLS_DIR}/admit_analyzer.py" || true
  echo "Staged admit_analyzer.py"
fi

# Stage other frequently-used scripts (when they exist)
STAGED_COUNT=0
if [[ -n "${TOOLS_DIR}" && -d "${TOOLS_DIR}" ]]; then
  for script in \
    search_stdlib.sh \
    find_golfable.py \
    analyze_assert_usage.py \
    count_tokens.py \
    suggest_tactics.sh \
    extract_typeclass_info.py \
    fill_admit_with_search.py \
    categorize_errors.py \
    suggest_fixes.py \
    check_axioms.py
  do
    if [[ -f "${TOOLS_DIR}/${script}" ]]; then
      cp -f "${TOOLS_DIR}/${script}" "${WORKSPACE_TOOLS_DIR}/${script}"
      chmod +x "${WORKSPACE_TOOLS_DIR}/${script}" || true
      STAGED_COUNT=$((STAGED_COUNT + 1))
    fi
  done
  if [[ ${STAGED_COUNT} -gt 0 ]]; then
    echo "Staged ${STAGED_COUNT} additional tool scripts to ${WORKSPACE_TOOLS_DIR}"
  fi
fi

# Stage reference documentation for subagents at predictable paths
DOC_STAGE=".claude/docs/rocq"
mkdir -p "${DOC_STAGE}"

DOC_STAGED_COUNT=0
# Find references directory (support both layouts)
REFS_DIR=""
for candidate in \
  "${CLAUDE_PLUGIN_ROOT}/skills/rocq-theorem-proving/references" \
  "${CLAUDE_PLUGIN_ROOT}/references"
do
  if [[ -d "$candidate" ]]; then
    REFS_DIR="$candidate"
    break
  fi
done

if [[ -n "${REFS_DIR}" && -d "${REFS_DIR}" ]]; then
  for doc in proof-golfing.md admit-filling.md axiom-elimination.md; do
    if [[ -f "${REFS_DIR}/${doc}" ]]; then
      cp -f "${REFS_DIR}/${doc}" "${DOC_STAGE}/${doc}"
      DOC_STAGED_COUNT=$((DOC_STAGED_COUNT + 1))
    fi
  done
  if [[ ${DOC_STAGED_COUNT} -gt 0 ]]; then
    echo "Staged ${DOC_STAGED_COUNT} reference docs to ${DOC_STAGE}"
  fi

  # Export doc stage location for reference
  if [[ -n "${ENV_OUT}" ]]; then
    printf 'export ROCQ_DOC_HOME="%s"\n' "${DOC_STAGE}" >> "${ENV_OUT}"
  fi
fi

# Persist variables for the rest of the session (so slash-commands can use them).
persist() {
  local kv="$1"
  if [[ -n "${ENV_OUT}" ]]; then
    printf '%s\n' "${kv}" >> "${ENV_OUT}"
  fi
}

# Always expose the plugin root (handy for other commands you may add)
persist "export ROCQ_PLUGIN_ROOT=\"${CLAUDE_PLUGIN_ROOT}\""

# Expose Rocq/Coq installation info
if [[ -n "${COQC_BIN}" ]]; then
  persist "export ROCQ_COQC_BIN=\"${COQC_BIN}\""
  COQC_VERSION="$("${COQC_BIN}" --version | head -n1 || echo "unknown")"
  persist "export ROCQ_VERSION=\"${COQC_VERSION}\""
fi

# Expose build system info
if [[ -n "${BUILD_SYSTEM}" ]]; then
  persist "export ROCQ_BUILD_SYSTEM=\"${BUILD_SYSTEM}\""
fi
if [[ -n "${DUNE_BIN}" ]]; then
  persist "export ROCQ_DUNE_BIN=\"${DUNE_BIN}\""
fi

# Expose LSP info
if [[ -n "${COQLSP_BIN}" ]]; then
  persist "export ROCQ_LSP_BIN=\"${COQLSP_BIN}\""
fi

# Expose python if found
if [[ -n "${PYTHON_BIN}" ]]; then
  persist "export ROCQ_PYTHON_BIN=\"${PYTHON_BIN}\""
fi

# Expose tools directory and analyzer (if found)
if [[ -n "${TOOLS_DIR}" ]]; then
  persist "export ROCQ_TOOLS_DIR=\"${TOOLS_DIR}\""
fi
if [[ -n "${ANALYZER_PATH}" ]]; then
  persist "export ROCQ_ADMIT_ANALYZER=\"${ANALYZER_PATH}\""
fi

# Optional: write a small status line (shows up in debug logs)
echo "Rocq bootstrap: PLUGIN_ROOT=${CLAUDE_PLUGIN_ROOT} COQC=${COQC_BIN:-none} BUILD=${BUILD_SYSTEM:-none} PYTHON=${PYTHON_BIN:-none}"
exit 0
