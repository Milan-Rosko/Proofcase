#!/usr/bin/env bash
set -euo pipefail

# -----------------------------------------------------------------------------
# Options:
# - CLEAN=1  : force full rebuild (make clean before all)
# - CACHE=1  : incremental cached build in shadow (default: 1)
# - CACHE=0  : cold shadow sync (removes prior compiled artifacts)
# - GUARD=1  : fail if any build artifacts (.glob/.vo/...) appear under repo theories/
# - JOBS=N   : parallel jobs for make (default: auto-detect CPU count)
# - CERT_HASHES=1 : include per-file SHA-256 hashes in success.txt (default: 0 for speed)
# -----------------------------------------------------------------------------
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "${HERE}/.." && pwd)"

ROOT_CP="$ROOT/_CoqProject"
THEORIES_CP="$ROOT/theories/_CoqProject"
COQPROJECT_OVERRIDE="${COQPROJECT_OVERRIDE:-}"

if [[ -n "$COQPROJECT_OVERRIDE" ]]; then
  if [[ "$COQPROJECT_OVERRIDE" = /* ]]; then
    COQPROJ="$COQPROJECT_OVERRIDE"
  else
    COQPROJ="$ROOT/$COQPROJECT_OVERRIDE"
  fi
  if [[ ! -f "$COQPROJ" ]]; then
    echo "COQPROJECT_OVERRIDE is set but file does not exist:"
    echo "  - $COQPROJ"
    exit 1
  fi
  ORIGIN="override"
elif [[ -f "$ROOT_CP" ]]; then
  COQPROJ="$ROOT_CP"
  ORIGIN="root"
elif [[ -f "$THEORIES_CP" ]]; then
  COQPROJ="$THEORIES_CP"
  ORIGIN="theories"
else
  echo "Checked for:"
  echo "  - $ROOT_CP"
  echo "  - $THEORIES_CP"
  echo "No _CoqProject found in either location."
  exit 1
fi

BUILD="${ROOT}/scratch"
SHADOW="${BUILD}/shadow"
BUILD_LOG="${BUILD}/build.log"

COQPROJECT_SRC="${COQPROJ}"
COQPROJECT_SHADOW="${SHADOW}/_CoqProject"

COQ_MAKEFILE="$(command -v coq_makefile || true)"
COQC="$(command -v coqc || true)"
COQDEP_BIN="$(command -v coqdep || true)"
MAKE_BIN="$(command -v gnumake || command -v make || true)"

# If tools are not in PATH (common when opam env is not loaded), try OPAM's bin dir.
if [[ -z "${COQ_MAKEFILE}" || -z "${COQC}" || -z "${COQDEP_BIN}" ]]; then
  if command -v opam >/dev/null 2>&1; then
    OPAM_BIN="$(opam var bin --safe 2>/dev/null || true)"
    if [[ -n "${OPAM_BIN}" ]]; then
      [[ -z "${COQ_MAKEFILE}" && -x "${OPAM_BIN}/coq_makefile" ]] && COQ_MAKEFILE="${OPAM_BIN}/coq_makefile"
      [[ -z "${COQC}" && -x "${OPAM_BIN}/coqc" ]] && COQC="${OPAM_BIN}/coqc"
      [[ -z "${COQDEP_BIN}" && -x "${OPAM_BIN}/coqdep" ]] && COQDEP_BIN="${OPAM_BIN}/coqdep"
    fi
  fi
fi

# If opam is not available in PATH, probe common local opam switch bins directly.
if [[ -z "${COQ_MAKEFILE}" || -z "${COQC}" || -z "${COQDEP_BIN}" ]]; then
  CANDIDATE_OPAM_BINS=()
  [[ -d "${HOME}/.opam/rocq-native/bin" ]] && CANDIDATE_OPAM_BINS+=("${HOME}/.opam/rocq-native/bin")
  [[ -d "${HOME}/.opam/default/bin" ]] && CANDIDATE_OPAM_BINS+=("${HOME}/.opam/default/bin")
  for d in "${HOME}"/.opam/*/bin; do
    [[ -d "$d" ]] || continue
    CANDIDATE_OPAM_BINS+=("$d")
  done

  for OPAM_BIN in "${CANDIDATE_OPAM_BINS[@]}"; do
    [[ -z "${COQ_MAKEFILE}" && -x "${OPAM_BIN}/coq_makefile" ]] && COQ_MAKEFILE="${OPAM_BIN}/coq_makefile"
    [[ -z "${COQC}" && -x "${OPAM_BIN}/coqc" ]] && COQC="${OPAM_BIN}/coqc"
    [[ -z "${COQDEP_BIN}" && -x "${OPAM_BIN}/coqdep" ]] && COQDEP_BIN="${OPAM_BIN}/coqdep"
    if [[ -n "${COQ_MAKEFILE}" && -n "${COQC}" && -n "${COQDEP_BIN}" ]]; then
      break
    fi
  done
fi

# Fail early with a clear message instead of hitting "command not found" later.
if [[ -z "${COQ_MAKEFILE}" || -z "${COQC}" || -z "${COQDEP_BIN}" || -z "${MAKE_BIN}" ]]; then
  echo "Missing required build tool(s):"
  [[ -z "${COQ_MAKEFILE}" ]] && echo "  - coq_makefile"
  [[ -z "${COQC}" ]] && echo "  - coqc"
  [[ -z "${COQDEP_BIN}" ]] && echo "  - coqdep"
  [[ -z "${MAKE_BIN}" ]] && echo "  - gnumake/make"
  echo
  echo "Hint: load your opam environment first:"
  echo "  eval \"\$(opam env)\""
  exit 1
fi

# Ensure companion executables (notably `rocq`) from the selected toolchain are reachable.
TOOL_BIN_DIR="$(dirname "${COQC}")"
case ":${PATH}:" in
  *":${TOOL_BIN_DIR}:"*) ;;
  *) export PATH="${TOOL_BIN_DIR}:${PATH}" ;;
esac

CLEAN="${CLEAN:-0}"
CACHE="${CACHE:-1}"
GUARD="${GUARD:-1}"
JOBS="${JOBS:-}"
CERT_HASHES="${CERT_HASHES:-0}"

if [[ -z "${JOBS}" ]]; then
  if command -v getconf >/dev/null 2>&1; then
    JOBS="$(getconf _NPROCESSORS_ONLN 2>/dev/null || true)"
  fi
  if [[ -z "${JOBS}" ]] && command -v sysctl >/dev/null 2>&1; then
    JOBS="$(sysctl -n hw.ncpu 2>/dev/null || true)"
  fi
  [[ -z "${JOBS}" ]] && JOBS="4"
fi

# One certificate, written under _tools/Dump
CERT_FILE="${HERE}/Dump/success.txt"

mkdir -p "${BUILD}" "${SHADOW}" "$(dirname "${CERT_FILE}")"
: > "${BUILD_LOG}"
rm -f "${CERT_FILE}"

# -----------------------------------------------------------------------------
# Prepare shadow sources
# -----------------------------------------------------------------------------
RSYNC_CACHE_PROTECT=(
  --filter='P *.vo'
  --filter='P *.vos'
  --filter='P *.vok'
  --filter='P *.glob'
  --filter='P .*.aux'
)

if command -v rsync >/dev/null 2>&1; then
  mkdir -p "${SHADOW}/theories"
  if [ "${CACHE}" = "1" ]; then
    rsync -a --delete "${RSYNC_CACHE_PROTECT[@]}" "${ROOT}/theories/" "${SHADOW}/theories/" >/dev/null 2>&1 || true
  else
    rsync -a --delete "${ROOT}/theories/" "${SHADOW}/theories/" >/dev/null 2>&1 || true
  fi
  if [[ -d "${ROOT}/formalizations" ]]; then
    mkdir -p "${SHADOW}/formalizations"
    if [ "${CACHE}" = "1" ]; then
      rsync -a --delete "${RSYNC_CACHE_PROTECT[@]}" "${ROOT}/formalizations/" "${SHADOW}/formalizations/" >/dev/null 2>&1 || true
    else
      rsync -a --delete "${ROOT}/formalizations/" "${SHADOW}/formalizations/" >/dev/null 2>&1 || true
    fi
  fi
else
  if [ "${CACHE}" = "1" ]; then
    mkdir -p "${SHADOW}/theories"
    cp -R "${ROOT}/theories/." "${SHADOW}/theories/"
    if [[ -d "${ROOT}/formalizations" ]]; then
      mkdir -p "${SHADOW}/formalizations"
      cp -R "${ROOT}/formalizations/." "${SHADOW}/formalizations/"
    fi
  else
    rm -rf "${SHADOW}/theories"
    cp -R "${ROOT}/theories" "${SHADOW}/theories"
    if [[ -d "${ROOT}/formalizations" ]]; then
      rm -rf "${SHADOW}/formalizations"
      cp -R "${ROOT}/formalizations" "${SHADOW}/formalizations"
    fi
  fi
fi

cp -f "${COQPROJECT_SRC}" "${COQPROJECT_SHADOW}"

cd "${SHADOW}"

# Coq's -output-directory mirrors compiled object paths, but extraction and
# Redirect targets may also write into source-relative appendix folders. Mirror
# source directories up front so artifact paths such as
# output/theories/P002/appendix/_artifacts/... exist before coqc reaches them.
while IFS= read -r d; do
  mkdir -p "output/${d}"
done < <(find theories -type d -print)

# Report redirects are generated into output/. Clear old reports so removed
# redirect commands cannot leave stale acceptance artifacts behind.
rm -rf \
  "output/theories/M001/_appendix/_assumptions" \
  "output/theories/M001/_appendix/_assumptions_classical" \
  "output/theories/M001/_appendix/_assumptions_constructive" \
  "output/theories/L001/_appendix/_artifacts" \
  "output/theories/L001/_appendix/_assumptions" \
  "output/theories/L001/_appendix/_assumptions_classical" \
  "output/theories/L001/_appendix/_assumptions_constructive"

# -----------------------------------------------------------------------------
# Build
# -----------------------------------------------------------------------------
"${COQ_MAKEFILE}" -f "_CoqProject" -o "Makefile.coq" | tee -a "${BUILD_LOG}"

# Pre-generate dependency graph to avoid intermittent missing-rule failures
# for .Makefile.coq.d in some make/loadpath states.
"${COQDEP_BIN}" -vos -dyndep var -f "_CoqProject" > ".Makefile.coq.d"

if [ "${CLEAN}" = "1" ]; then
  "${MAKE_BIN}" -f Makefile.coq clean | tee -a "${BUILD_LOG}"
fi

"${MAKE_BIN}" -f Makefile.coq -j "${JOBS}" all | tee -a "${BUILD_LOG}"

# -----------------------------------------------------------------------------
# Source-tree build-artifact guard
# -----------------------------------------------------------------------------
if [[ "${GUARD}" = "1" ]]; then
  SOURCE_TREE_ARTIFACTS="$(mktemp "${BUILD}/source-tree-artifacts.XXXXXX")"
  find "${ROOT}/theories" -type f \( \
    -name '*.vo' -o \
    -name '*.vos' -o \
    -name '*.vok' -o \
    -name '*.vio' -o \
    -name '*.glob' -o \
    -name '*.aux' -o \
    -name '.*.aux' \
  \) -print | sort > "${SOURCE_TREE_ARTIFACTS}"

  if [[ -s "${SOURCE_TREE_ARTIFACTS}" ]]; then
    echo "Build artifacts found under source theories/ while GUARD=1:" | tee -a "${BUILD_LOG}"
    sed "s|${ROOT}/||" "${SOURCE_TREE_ARTIFACTS}" | tee -a "${BUILD_LOG}"
    rm -f "${SOURCE_TREE_ARTIFACTS}"
    exit 1
  fi

  rm -f "${SOURCE_TREE_ARTIFACTS}"
fi

# -----------------------------------------------------------------------------
# Constructive M001 assumption-report guard
# -----------------------------------------------------------------------------
M001_CONSTRUCTIVE_ASSUMPTIONS="output/theories/M001/_appendix/_assumptions"
M001_ARTIFACT_SOURCE="${SHADOW}/theories/M001/M001_97_Artifacts.v"
M001_REQUIRED_CONSTRUCTIVE_REPORTS=(
  "regulator_theory_deduction_checked"
  "regulator_theory_reductio_checked"
  "regulator_theory_not_checked_derivable_precompose_lemma"
  "regulator_theory_syntactic_adequacy_lemma"
)
M001_ASSUMPTION_GUARD_ENABLED=0
if grep -Eq '(^|[[:space:]])theories/M001/M001_97_Artifacts\.v([[:space:]]|$)' "${COQPROJECT_SHADOW}"; then
  M001_ASSUMPTION_GUARD_ENABLED=1
fi

regulator_theory_assumption_reports_present() {
  for report in "${M001_REQUIRED_CONSTRUCTIVE_REPORTS[@]}"; do
    if [[ ! -s "${M001_CONSTRUCTIVE_ASSUMPTIONS}/${report}.out" ]]; then
      return 1
    fi
  done
  return 0
}

if [[ "${M001_ASSUMPTION_GUARD_ENABLED}" = "1" ]]; then
  if ! regulator_theory_assumption_reports_present; then
    # Stale-cache recovery: when the assumption-report directory was wiped before
    # the build but `M001_97_Artifacts.vo` was a cache hit, the `Redirect`
    # outputs are not regenerated. Force a single re-emission and retry.
    if [[ -f "${M001_ARTIFACT_SOURCE}" ]]; then
      touch "${M001_ARTIFACT_SOURCE}"
      "${MAKE_BIN}" -f Makefile.coq -j "${JOBS}" \
        "theories/M001/M001_97_Artifacts.vo" | tee -a "${BUILD_LOG}"
    fi
  fi

  for report in "${M001_REQUIRED_CONSTRUCTIVE_REPORTS[@]}"; do
    if [[ ! -s "${M001_CONSTRUCTIVE_ASSUMPTIONS}/${report}.out" ]]; then
      echo "Missing or empty constructive M001 assumption report: ${M001_CONSTRUCTIVE_ASSUMPTIONS}/${report}.out" | tee -a "${BUILD_LOG}"
      exit 1
    fi
  done

  if grep -R \
    -e "^Axioms:" \
    -e "ClassicalEpsilon" \
    -e "constructive_indefinite_description" \
    -e "excluded_middle" \
    -e "classic" \
    "${M001_CONSTRUCTIVE_ASSUMPTIONS}" | tee -a "${BUILD_LOG}"; then
    echo "Constructive M001 assumption reports contain forbidden classical or axiom dependencies." | tee -a "${BUILD_LOG}"
    exit 1
  fi
fi

# -----------------------------------------------------------------------------
# Constructive L001 assumption-report guard
# -----------------------------------------------------------------------------
L001_CONSTRUCTIVE_ASSUMPTIONS="output/theories/L001/_appendix/_assumptions_constructive"
L001_ARTIFACT_SOURCE="${SHADOW}/theories/L001/L001_97_Artifacts.v"
L001_REQUIRED_CONSTRUCTIVE_REPORTS=(
  "certified_aporetic_lemma_contract"
  "aporetic_lemma_qed"
)
L001_ASSUMPTION_GUARD_ENABLED=0
if grep -Eq '(^|[[:space:]])theories/L001/L001_97_Artifacts\.v([[:space:]]|$)' "${COQPROJECT_SHADOW}"; then
  L001_ASSUMPTION_GUARD_ENABLED=1
fi

aporetic_assumption_reports_present() {
  for report in "${L001_REQUIRED_CONSTRUCTIVE_REPORTS[@]}"; do
    if [[ ! -s "${L001_CONSTRUCTIVE_ASSUMPTIONS}/${report}.out" ]]; then
      return 1
    fi
  done
  return 0
}

if [[ "${L001_ASSUMPTION_GUARD_ENABLED}" = "1" ]]; then
  if ! aporetic_assumption_reports_present; then
    # Stale-cache recovery mirrors the M001 guard: when the report directory was
    # wiped but the artifact file was a cache hit, force one re-emission pass.
    if [[ -f "${L001_ARTIFACT_SOURCE}" ]]; then
      touch "${L001_ARTIFACT_SOURCE}"
      "${MAKE_BIN}" -f Makefile.coq -j "${JOBS}" \
        "theories/L001/L001_97_Artifacts.vo" | tee -a "${BUILD_LOG}"
    fi
  fi

  for report in "${L001_REQUIRED_CONSTRUCTIVE_REPORTS[@]}"; do
    if [[ ! -s "${L001_CONSTRUCTIVE_ASSUMPTIONS}/${report}.out" ]]; then
      echo "Missing or empty constructive L001 assumption report: ${L001_CONSTRUCTIVE_ASSUMPTIONS}/${report}.out" | tee -a "${BUILD_LOG}"
      exit 1
    fi
  done

  if grep -R \
    -e "^Axioms:" \
    -e "ClassicalEpsilon" \
    -e "constructive_indefinite_description" \
    -e "excluded_middle" \
    -e "classic" \
    "${L001_CONSTRUCTIVE_ASSUMPTIONS}" | tee -a "${BUILD_LOG}"; then
    echo "Constructive L001 assumption reports contain forbidden classical or axiom dependencies." | tee -a "${BUILD_LOG}"
    exit 1
  fi
fi

# -----------------------------------------------------------------------------
# M001 extracted-artifact freshness guard
# -----------------------------------------------------------------------------
M001_ARTIFACT_GUARD_ENABLED=0
if grep -Eq '(^|[[:space:]])theories/M001/M001_97_Artifacts\.v([[:space:]]|$)' "${COQPROJECT_SHADOW}"; then
  M001_ARTIFACT_GUARD_ENABLED=1
fi

if [[ "${M001_ARTIFACT_GUARD_ENABLED}" = "1" ]]; then
  for artifact in regulator_theory_checker.ml regulator_theory_checker.mli; do
    generated="output/theories/M001/_appendix/_artifacts/${artifact}"
    checked_in="${ROOT}/theories/M001/_appendix/_artifacts/${artifact}"

    if [[ ! -s "${generated}" ]]; then
      echo "Missing or empty generated M001 extracted artifact: ${generated}" | tee -a "${BUILD_LOG}"
      exit 1
    fi

    if [[ ! -s "${checked_in}" ]]; then
      echo "Missing or empty source M001 extracted artifact: ${checked_in}" | tee -a "${BUILD_LOG}"
      exit 1
    fi

    if ! cmp -s "${generated}" "${checked_in}"; then
      echo "Stale source M001 extracted artifact: ${checked_in}" | tee -a "${BUILD_LOG}"
      echo "Generated artifact differs from: ${generated}" | tee -a "${BUILD_LOG}"
      exit 1
    fi
  done
fi

# -----------------------------------------------------------------------------
# Axiom Listing
# -----------------------------------------------------------------------------
THEORIES_PATH="${SHADOW}/theories"
if command -v rg >/dev/null 2>&1; then
  ALL_AXIOM_FILES_RAW="$(rg -l --glob '*.v' --no-messages "^\s*Axioms?\b" "${THEORIES_PATH}" || true)"
else
  ALL_AXIOM_FILES_RAW="$(find "${THEORIES_PATH}" -name '*.v' -exec grep -l -E "^[[:space:]]*Axioms?\b" {} + 2>/dev/null || true)"
fi
ALL_AXIOM_FILES="$(echo "${ALL_AXIOM_FILES_RAW}" | sed "s|${SHADOW}/||g" | sort -u)"
# -----------------------------------------------------------------------------
# Generate Certificate
# -----------------------------------------------------------------------------
UTC_NOW="$(date -u +"%Y-%m-%dT%H:%M:%SZ")"

hash_file() {
  # This converts the hex hash to binary and then to Base64
  # It shrinks the character count by about 30% without losing a single bit of data
  shasum -a 256 "$1" | awk '{print $1}' | xxd -r -p | base64
}

SELECTED_LIST=""
COUNT="0"
if [ "${CERT_HASHES}" = "1" ]; then
  SELECTED_LIST="$(mktemp "${BUILD}/selected.XXXXXX")"
  sed -e 's/\r$//' -e 's/[[:space:]]*#.*$//' -e 's/^[[:space:]]*//' -e 's/[[:space:]]*$//' -e '/^$/d' -e '/^-/d' "${COQPROJECT_SHADOW}" | sort -u > "${SELECTED_LIST}"
  COUNT="$(grep -c . "${SELECTED_LIST}" || true)"
fi

{
  echo "(successful 'makefile' run.) "
  echo 
  echo " . . . . . . . . .....*************************.                           "
  echo ". . . . . ... ..... ....***************************.                       "
  echo " . . . . . . . . . . .. ... .. ... .....**************                     "
  echo ". . . . . .. .. .. .....********************************                   "
  echo " . . . . ... ..... ......********************************                  "
  echo ". . . . . . . . . . .. .... .... ....*********************                 "
  echo " . . . . . . ... .... .....**********************   *******                "
  echo ". . . . . . . .  .... ....*********************************.               "
  echo " . . . . .. .. ..... ....***********************************               "
  echo ". . . ... ... ..... .....***********************************               "
  echo " . . . .. ... ..... .....***********************************               "
  echo ". . . . .. ... ..... .....******************          *****                "
  echo " . . . . .. ... ..... .....***************              ***                "
  echo ". . . . . .. ... ..... .....************                 *                 "
  echo " . . . . . .. ... ..... .....*********                                     "
  echo ". . . . . . .. ... ..... ......******                                      "
  echo " . . . . . . ... ........ .......**                                        "
  echo "---------------------------------------------------------------------------"
  echo 
  echo "                    Date (UTC): $UTC_NOW,"
  echo
  if [ -n "${COQC}" ]; then
  echo "                   Rocq version: $(${COQC} --version 2>/dev/null | head -n 1)"
  echo "              _CoqProject source: ${ORIGIN}"
  echo "                _CoqProject path: ${COQPROJ}"
  if [ "${CACHE}" = "1" ]; then
    echo "                   Method: isolated shadow, scratch folder (cached)"
  else
    echo "                   Method: isolated shadow, scratch folder (cold sync)"
  fi
  echo "                   Build jobs: ${JOBS}"
  fi
  echo
  echo "---------------------------------------------------------------------------"
  echo
  echo "Axioms:"
  echo
  if [ -n "${ALL_AXIOM_FILES}" ]; then
    printf "%s\n" "${ALL_AXIOM_FILES}"
  fi
  echo "---------------------------------------------------------------------------"
  echo
  echo "_CoqProject file contents:"
  echo
  echo "=== BEGIN ==="
  echo 
  while IFS= read -r cp_line || [[ -n "$cp_line" ]]; do
    # Trim CR (in case of Windows line endings).
    cp_line="${cp_line%$'\r'}"
    printf "   %s \n" "$cp_line"
  done < "$COQPROJ"
  echo 
  echo "=== END ==="
  echo
  echo "---------------------------------------------------------------------------"
  echo
  if [ "${CERT_HASHES}" = "1" ]; then
    echo "Hash(es) (Short SHA-256) of ${COUNT} Files:"
  else
    echo "Hash(es): skipped (set CERT_HASHES=1 to enable)"
  fi
  echo
  echo "---------------------------------------------------------------------------"
  if [ "${CERT_HASHES}" = "1" ]; then
    while IFS= read -r f; do
      [ -z "${f}" ] && continue
      if [ -f "${ROOT}/${f}" ]; then
        printf "   %s\n" "$(hash_file "${ROOT}/${f}")"
      fi
    done < "${SELECTED_LIST}"
  fi
  echo
  echo "------------------------"
  echo

} > "${CERT_FILE}"

if [ -n "${SELECTED_LIST}" ]; then
  rm -f "${SELECTED_LIST}"
fi

echo "" | tee -a "${BUILD_LOG}"
echo "Build process finished." | tee -a "${BUILD_LOG}"
echo "Certificate written to: ${CERT_FILE}" | tee -a "${BUILD_LOG}"
