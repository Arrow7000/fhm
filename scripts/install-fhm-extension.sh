#!/usr/bin/env bash
# Symlink this extension into Cursor's (or VS Code's) extensions folder.
#
# Usage:
#   scripts/install-fhm-extension.sh           # Cursor
#   scripts/install-fhm-extension.sh code      # VS Code
#   scripts/install-fhm-extension.sh cursor --reload-hint
#
# After install: Developer: Reload Window (or restart Cursor).
# Highlighting works immediately. Parse squiggles need:
#   lake build fhm
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
EXT_SRC="$ROOT/editors/vscode"
APP="${1:-cursor}"

case "$APP" in
  cursor)
    EXT_DIR="${CURSOR_EXTENSIONS_DIR:-$HOME/.cursor/extensions}"
    ;;
  code|vscode)
    EXT_DIR="${VSCODE_EXTENSIONS_DIR:-$HOME/.vscode/extensions}"
    ;;
  *)
    echo "usage: $0 [cursor|code]" >&2
    exit 2
    ;;
esac

# Read publisher.name-version from package.json without requiring node jq.
NAME="$(sed -n 's/.*"name"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$EXT_SRC/package.json" | head -1)"
PUBLISHER="$(sed -n 's/.*"publisher"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$EXT_SRC/package.json" | head -1)"
VERSION="$(sed -n 's/.*"version"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' "$EXT_SRC/package.json" | head -1)"
TARGET="$EXT_DIR/${PUBLISHER}.${NAME}-${VERSION}"

mkdir -p "$EXT_DIR"

if [[ -e "$TARGET" && ! -L "$TARGET" ]]; then
  echo "error: $TARGET exists and is not a symlink — remove it first" >&2
  exit 1
fi

ln -sfn "$EXT_SRC" "$TARGET"
echo "linked $TARGET -> $EXT_SRC"
echo
echo "Next: reload the window (Cmd+Shift+P → Developer: Reload Window)."
echo "Edit editors/vscode/ or regenerate the grammar; reload again to pick up changes."
echo "Parse diagnostics: lake build fhm (binary at .lake/build/bin/fhm)."
