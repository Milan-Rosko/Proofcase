#!/usr/bin/env bash
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
THEORIES_DIR="$ROOT/theories"

if [[ ! -d "$THEORIES_DIR" ]]; then
  echo "No theories directory found at: $THEORIES_DIR"
  exit 0
fi

removed=0
while IFS= read -r -d '' f; do
  rm -f -- "$f"
  removed=$((removed + 1))
done < <(
  find "$THEORIES_DIR" -type f \
    \( -name '*.vo' -o -name '*.aux' -o -name '*.vos' -o -name '*.vok' -o -name '*.glob' \) \
    -print0
)

echo "Removed $removed artifact file(s) from $THEORIES_DIR"
