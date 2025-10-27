#!/usr/bin/env bash
# Bootstrap env for the session so commands can reference plugin scripts reliably.

set -euo pipefail

# --- Sanity: hooks get this; commands do not. Fail fast if missing.
: "${CLAUDE_PLUGIN_ROOT:?missing CLAUDE_PLUGIN_ROOT in hook context}"

# Optional: where Claude tells us to persist env vars for the whole session.
ENV_OUT="${CLAUDE_ENV_FILE:-}"

# Resolve python (prefer python3, fall back to python).
PYTHON_BIN="$(command -v python3 || true)"
if [[ -z "${PYTHON_BIN}" ]]; then
  PYTHON_BIN="$(command -v python || true)"
fi
if [[ -z "${PYTHON_BIN}" ]]; then
  echo "WARN: No python interpreter found in PATH; commands that need Python will fail." >&2
fi

# Candidate locations for the analyzer (support both layouts):
#   (A) plugin-level:   plugins/lean4-theorem-proving/scripts/sorry_analyzer.py
#   (B) skill-scoped:   plugins/lean4-theorem-proving/skills/lean4-theorem-proving/scripts/sorry_analyzer.py
CANDIDATES=(
  "${CLAUDE_PLUGIN_ROOT}/scripts/sorry_analyzer.py"
  "${CLAUDE_PLUGIN_ROOT}/skills/lean4-theorem-proving/scripts/sorry_analyzer.py"
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

# Persist variables for the rest of the session (so slash-commands can use them).
persist() {
  local kv="$1"
  if [[ -n "${ENV_OUT}" ]]; then
    printf '%s\n' "${kv}" >> "${ENV_OUT}"
  fi
}

# Always expose the plugin root (handy for other commands you may add)
persist "export LEAN4_PLUGIN_ROOT=\"${CLAUDE_PLUGIN_ROOT}\""

# Expose python if found
if [[ -n "${PYTHON_BIN}" ]]; then
  persist "export LEAN4_PYTHON_BIN=\"${PYTHON_BIN}\""
fi

# Expose tools directory and analyzer (if found)
if [[ -n "${TOOLS_DIR}" ]]; then
  persist "export LEAN4_TOOLS_DIR=\"${TOOLS_DIR}\""
fi
if [[ -n "${ANALYZER_PATH}" ]]; then
  persist "export LEAN4_SORRY_ANALYZER=\"${ANALYZER_PATH}\""
fi

# Optional: write a small status line (shows up in debug logs)
echo "Lean4 bootstrap: PLUGIN_ROOT=${CLAUDE_PLUGIN_ROOT} PYTHON=${PYTHON_BIN:-none} ANALYZER=${ANALYZER_PATH:-none}"
exit 0
