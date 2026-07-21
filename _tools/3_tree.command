#!/usr/bin/env bash
set -euo pipefail

# -----------------------------------------------------------------------------
# Rocq/Coq dependency tree generator (selected files only).
# Outputs to _tools/Dump/tree.
# -----------------------------------------------------------------------------

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "${HERE}/.." && pwd)"
cd "$ROOT"

DUMP_ROOT="${ROOT}/_tools/Dump"
OUT_DIR="${OUT_DIR:-$DUMP_ROOT/tree}"
mkdir -p "$OUT_DIR"

COQPROJECT="${COQPROJECT:-$ROOT/_CoqProject}"
SELECT_PATH="$ROOT/_tools/_Select"
if [[ ! -f "$SELECT_PATH" ]]; then
  SELECT_PATH="$ROOT/_tools/_TextslectFLT"
fi

DEPS_RAW="$OUT_DIR/deps.raw"
DOT="$OUT_DIR/deps.dot"
EDGES="$OUT_DIR/deps.edges"
TSORT_OUT="$OUT_DIR/deps.tsort"
HTML="$OUT_DIR/deps.html"

COQDEP_BIN="$(command -v coqdep || true)"
if [[ -z "$COQDEP_BIN" ]] && command -v opam >/dev/null 2>&1; then
  OPAM_BIN="$(opam var bin --safe 2>/dev/null || true)"
  [[ -n "$OPAM_BIN" && -x "$OPAM_BIN/coqdep" ]] && COQDEP_BIN="$OPAM_BIN/coqdep"
fi
if [[ -z "$COQDEP_BIN" ]]; then
  for candidate in \
    "$HOME/.opam/rocq-native/bin/coqdep" \
    "$HOME/.opam/rocq/bin/coqdep" \
    "$HOME/.opam/default/bin/coqdep"; do
    if [[ -x "$candidate" ]]; then
      COQDEP_BIN="$candidate"
      break
    fi
  done
fi

if [[ -z "$COQDEP_BIN" ]]; then
  echo "ERROR: coqdep not found in PATH."
  echo "Make sure Rocq/Coq is installed and coqdep is available."
  exit 1
fi

if [[ ! -f "$COQPROJECT" ]]; then
  echo "ERROR: _CoqProject not found at: $COQPROJECT"
  exit 1
fi

if [[ ! -f "$SELECT_PATH" ]]; then
  echo "ERROR: select file not found at: $SELECT_PATH"
  exit 1
fi

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

VFILES=()
while IFS= read -r raw || [[ -n "$raw" ]]; do
  if rel="$(normalize_select_line "$raw")"; then
    abs="$ROOT/${rel#./}"
    if [[ ! -f "$abs" ]]; then
      echo "ERROR: selected file not found: $abs"
      exit 1
    fi
    VFILES+=("${rel#./}")
  fi
done <"$SELECT_PATH"

if [[ "${#VFILES[@]}" -eq 0 ]]; then
  echo "ERROR: no .v files selected from: $SELECT_PATH"
  exit 1
fi

echo "Using source list: $SELECT_PATH"
echo "Selected files:    ${#VFILES[@]}"
echo "COQPROJECT:        $COQPROJECT"
echo "OUT_DIR:           $OUT_DIR"

echo "Running coqdep..."
# Read only load-path directives from _CoqProject. Passing `-f` would also add
# every project source a second time alongside VFILES; on paths containing
# spaces, coqdep's escaped absolute paths then corrupt the graph parser.
COQDEP_ARGS=()
while read -r directive physical logical _rest; do
  case "$directive" in
    -Q|-R)
      COQDEP_ARGS+=("$directive" "$physical" "$logical")
      ;;
  esac
done < "$COQPROJECT"
NEED_F001_Q=0
for vf in "${VFILES[@]}"; do
  case "$vf" in
    formalizations/F001/*) NEED_F001_Q=1 ;;
  esac
done
if (( NEED_F001_Q == 1 )) && ! grep -Eq '^[[:space:]]*-Q[[:space:]]+formalizations/F001[[:space:]]+F001([[:space:]]|$)' "$COQPROJECT"; then
  COQDEP_ARGS+=(-Q "$ROOT/formalizations/F001" F001)
fi

"$COQDEP_BIN" "${COQDEP_ARGS[@]}" "${VFILES[@]}" > "$DEPS_RAW"

ROOT_LEN=${#ROOT}
ROOT_LEN=$((ROOT_LEN + 1))

perl -pe 's/\\\n/ /g' "$DEPS_RAW" | \
awk -v root="$ROOT" -v root_len="$ROOT_LEN" '
function normalize(path) {
    sub(/\.vo$/, ".v", path)
    sub(/\.glob$/, ".v", path)
    return path
}

function prettify(path) {
    if (index(path, root) == 1) {
        path = substr(path, root_len + 1)
    }
    return path
}

BEGIN {
    print "digraph RocqDeps {" > "'"$DOT"'"
    print "  rankdir=TB;" > "'"$DOT"'"
    print "  node [shape=box, fontsize=10, style=filled, fillcolor=\"white\"];" > "'"$DOT"'"
    print "  edge [fontsize=9];" > "'"$DOT"'"
    print "" > "'"$DOT"'"
}

{
    n = split($0, chunks, ":")
    if (n < 2) next

    left = chunks[1]
    right = ""
    for (i = 2; i <= n; i++) right = right (i == 2 ? "" : ":") chunks[i]

    split(left, targets, " ")
    src = ""
    for (i in targets) {
        if (targets[i] ~ /\.vo$/) {
            src = normalize(targets[i])
            break
        }
    }
    if (src == "") src = normalize(targets[1])

    if (!(src in seen_nodes)) {
        lbl = prettify(src)
        print "  \"" src "\" [label=\"" lbl "\"];" > "'"$DOT"'"
        seen_nodes[src] = 1
    }

    split(right, deps, " ")
    for (i in deps) {
        d = normalize(deps[i])
        if (d !~ /\.v$/) continue
        if (src == d) continue
        if (index(d, "/") == 1 && index(d, root) != 1) continue

        edge_key = src "->" d
        if (!(edge_key in seen_edges)) {
            print "  \"" src "\" -> \"" d "\";" > "'"$DOT"'"
            print src "\t" d > "'"$EDGES"'"
            seen_edges[edge_key] = 1
        }

        if (!(d in seen_nodes)) {
            lbl = prettify(d)
            print "  \"" d "\" [label=\"" lbl "\"];" > "'"$DOT"'"
            seen_nodes[d] = 1
        }
    }
}

END {
    print "}" > "'"$DOT"'"
}
'

if [[ -s "$EDGES" ]]; then
  awk -F'\t' '{print $2, $1}' "$EDGES" | tsort > "$TSORT_OUT"
else
  echo "No edges found for tsort." > "$TSORT_OUT"
fi

if command -v dot >/dev/null 2>&1; then
  dot -Tsvg "$DOT" -o "$OUT_DIR/deps.svg"
  echo "Wrote: $OUT_DIR/deps.svg"
else
  echo "Graphviz not found (dot). Skipping SVG render."
fi

cat >"$HTML" <<'EOF'
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>deps.svg</title>
  <style>
    html, body { margin: 0; padding: 0; width: 100%; height: 100%; }
    .wrap {
      width: 100%;
      min-height: 100%;
      overflow: auto;
      background: #fff;
    }
    img {
      display: block;
      width: 100%;
      height: auto;
      max-width: 100%;
    }
  </style>
</head>
<body>
  <div class="wrap">
    <img src="deps.svg" alt="Dependency graph" />
  </div>
</body>
</html>
EOF

echo "Wrote: $DEPS_RAW"
echo "Wrote: $DOT"
echo "Wrote: $EDGES"
echo "Wrote: $TSORT_OUT"
echo "Wrote: $HTML"
