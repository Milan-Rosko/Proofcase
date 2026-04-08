#!/usr/bin/env bash

set -Eeuo pipefail

die() {
  echo "Error: $*" >&2
  exit 2
}

HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/.." && pwd)"

SHADOW="${ROOT}/scratch/shadow"
COQPROJ_SHADOW="${SHADOW}/_CoqProject"

DUMP_DIR="${HERE}/Dump/assumptions"
APPENDIX_DIR="${ROOT}/theories/P002/appendix/assumptions"
mkdir -p "${DUMP_DIR}" "${APPENDIX_DIR}"

THEOREMS=(
  "N_CubicEqSat_RE_complete_QED"
  "H10Nd3n_equals_U_in_RA_QED"
  "H10Nd3n_equals_U_QED"
)

COQC="$(command -v coqc || true)"
if [[ -z "${COQC}" ]] && command -v opam >/dev/null 2>&1; then
  OPAM_BIN="$(opam var bin --switch=rocq-native --safe 2>/dev/null || true)"
  if [[ -n "${OPAM_BIN}" && -x "${OPAM_BIN}/coqc" ]]; then
    COQC="${OPAM_BIN}/coqc"
  fi
fi

if [[ -z "${COQC}" ]]; then
  CANDIDATE_BINS=()
  [[ -d "${HOME}/.opam/rocq-native/bin" ]] && CANDIDATE_BINS+=("${HOME}/.opam/rocq-native/bin")
  [[ -d "${HOME}/.opam/default/bin" ]] && CANDIDATE_BINS+=("${HOME}/.opam/default/bin")
  for d in "${HOME}"/.opam/*/bin; do
    [[ -d "$d" ]] || continue
    CANDIDATE_BINS+=("$d")
  done
  for d in "${CANDIDATE_BINS[@]}"; do
    if [[ -x "${d}/coqc" ]]; then
      COQC="${d}/coqc"
      break
    fi
  done
fi

[[ -n "${COQC}" ]] || die "coqc not found. Run with an opam switch that has Rocq installed."

TOOL_BIN_DIR="$(dirname "${COQC}")"
case ":${PATH}:" in
  *":${TOOL_BIN_DIR}:"*) ;;
  *) export PATH="${TOOL_BIN_DIR}:${PATH}" ;;
esac

[[ -d "${SHADOW}" ]] || die "Missing shadow build directory: ${SHADOW}. Run _tools/1_compile.command first."
[[ -f "${COQPROJ_SHADOW}" ]] || die "Missing ${COQPROJ_SHADOW}. Run _tools/1_compile.command first."

if [[ ! -f "${SHADOW}/theories/P002/P002_99_QED.vo" ]]; then
  die "Missing compiled P002_99_QED.vo in shadow. Run _tools/1_compile.command first."
fi

QFLAGS=()
while read -r qpath qname; do
  [[ -n "${qpath}" && -n "${qname}" ]] || continue
  QFLAGS+=("-Q" "${qpath}" "${qname}")
done < <(awk '/^[[:space:]]*-Q[[:space:]]+/ { print $2, $3 }' "${COQPROJ_SHADOW}")

[[ "${#QFLAGS[@]}" -gt 0 ]] || die "No -Q mappings found in ${COQPROJ_SHADOW}."

TMP_DIR="$(mktemp -d "${ROOT}/scratch/assumptions.XXXXXX")"
trap 'rm -rf "${TMP_DIR}"' EXIT

UTC_NOW="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"
MANIFEST="${DUMP_DIR}/manifest.txt"

{
  echo "Assumption reports"
  echo "Generated (UTC): ${UTC_NOW}"
  echo "coqc: ${COQC}"
  echo
} > "${MANIFEST}"

for THM in "${THEOREMS[@]}"; do
  VFILE="${TMP_DIR}/${THM}.v"
  OUTFILE="${DUMP_DIR}/${THM}.txt"
  APPFILE="${APPENDIX_DIR}/${THM}.txt"

  cat > "${VFILE}" <<EOF
From P002 Require Import P002_99_QED.
Print Assumptions ${THM}.
EOF

  (
    cd "${SHADOW}"
    "${COQC}" -q -native-compiler no "${QFLAGS[@]}" "${VFILE}"
  ) > "${OUTFILE}" 2>&1

  [[ -s "${OUTFILE}" ]] || die "Empty assumptions output for ${THM}."

  cp -f "${OUTFILE}" "${APPFILE}"

  HASH="$(shasum -a 256 "${OUTFILE}" | awk '{print $1}')"
  {
    echo "${THM}"
    echo "  dump: ${OUTFILE}"
    echo "  appendix: ${APPFILE}"
    echo "  sha256: ${HASH}"
    echo
  } >> "${MANIFEST}"
done

echo "Assumption gates generated:"
for THM in "${THEOREMS[@]}"; do
  echo "  - ${DUMP_DIR}/${THM}.txt"
done
echo "Manifest:"
echo "  - ${MANIFEST}"
