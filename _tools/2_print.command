#!/usr/bin/env bash

set -Eeuo pipefail

die() { echo "Error: $*" >&2; exit 2; }

TTY="/dev/tty"
have_tty() { [[ -r "$TTY" && -w "$TTY" ]]; }
is_interactive_stdin() { [[ -t 0 ]]; }

pause() {
  if have_tty; then
    printf "\nPress Enter to close..." >"$TTY"
    IFS= read -r _ <"$TTY" || true
  elif is_interactive_stdin; then
    printf "\nPress Enter to close..." >&2
    IFS= read -r _ || true
  fi
}

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/.." && pwd)"
cd "$ROOT"

trap 'rc=$?; ((rc!=0)) && echo >&2 && echo "Print failed (exit status: $rc)." >&2; pause; exit $rc' EXIT

DUMP_ROOT="$HERE/Dump"
BUILD="$DUMP_ROOT/print"
mkdir -p "$BUILD"

OUT="$BUILD/v.context.txt"
LISTING="$BUILD/selected_files.txt"

SELECT_PATH="$ROOT/_tools/_Select"
[[ -f "$SELECT_PATH" ]] || die "Select file not found. Expected: _tools/_Select"

echo "Output:"
echo "  OUT:     $OUT"
echo "  LISTING: $LISTING"
echo "Source:"
echo "  $(basename "$SELECT_PATH"): $SELECT_PATH"
echo

SELECTED_FILES=()

append_if_exists() {
  local rel="$1"
  [[ -z "$rel" ]] && return 0
  rel="${rel#./}"
  local src="$ROOT/$rel"
  [[ -f "$src" ]] || die "Listed file not found: $src"
  SELECTED_FILES+=("$rel")
}

normalize_select_line() {
  local line="$1"
  line="${line%$'\r'}"
  line="$(printf "%s" "$line" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')"
  [[ -z "$line" ]] && return 1
  [[ "$line" =~ ^# ]] && return 1

  if [[ "$line" =~ ^\(\*[[:space:]]*(.*)[[:space:]]*\*\)$ ]]; then
    line="${BASH_REMATCH[1]}"
    line="$(printf "%s" "$line" | sed -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//')"
  fi

  [[ "$line" =~ ^[-]{2,} ]] && return 1
  [[ "$line" =~ \.v$ ]] || return 1
  printf "%s\n" "$line"
}

while IFS= read -r raw || [[ -n "$raw" ]]; do
  if norm="$(normalize_select_line "$raw")"; then
    append_if_exists "$norm"
  fi
done <"$SELECT_PATH"

COUNT="${#SELECTED_FILES[@]}"
if [[ "$COUNT" -eq 0 ]]; then
  die "No .v files selected from $(basename "$SELECT_PATH")"
fi

: >"$LISTING"
for f in "${SELECTED_FILES[@]}"; do
  printf "%s\n" "$f" >>"$LISTING"
done

echo "Selected files: $COUNT"
echo

UTC_NOW="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
: >"$OUT"

{
  echo "(* Note. This is a concatenation for establishing context. *)"
  echo "(* Source: $(basename "$SELECT_PATH") *)"
  echo "(* Generated (UTC): $UTC_NOW *)"
  echo
  echo "(* ---- BEGIN $(basename "$SELECT_PATH") ---- *)"
  while IFS= read -r src_line || [[ -n "$src_line" ]]; do
    src_line="${src_line%$'\r'}"
    printf "(* %s *)\n" "$src_line"
  done <"$SELECT_PATH"
  echo "(* ---- END $(basename "$SELECT_PATH") ---- *)"
  echo
} >>"$OUT"

append_file() {
  local rel="$1"
  local src="$ROOT/$rel"
  [[ -f "$src" ]] || die "Selected file missing at concat time: $src"
  printf "\n\n(* ---- %s ---- *)\n\n" "$rel" >>"$OUT"
  cat -- "$src" >>"$OUT"
}

for rel in "${SELECTED_FILES[@]}"; do
  append_file "$rel"
done

echo "Done. Wrote $OUT"
exit 0
