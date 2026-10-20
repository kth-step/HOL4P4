#!/bin/bash
# Import of P4 programs into HOL4P4 via petr4's JSON export.
#
#   p4_from_json.sh fetch-tests [PETR4_CLONE]
#   p4_from_json.sh export DIR [INCLUDE_DIR]
#   p4_from_json.sh convert FILE.json [--mode MODE] [--arch ARCH] [--log FILE] [--keep-info]
#   p4_from_json.sh convert-dir DIR [-j N] [--mode MODE] [--log FILE] [--keep-info]
#   p4_from_json.sh validate [-j N]
#
# Run with no arguments for details. Works from any directory.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$(readlink -f "$0")")" && pwd)"
HEAP="$SCRIPT_DIR/p4_from_json-heap"
DEFAULT_LOG="$SCRIPT_DIR/p4_from_json.log"
PETR4_REPO="https://github.com/verified-network-toolchain/petr4.git"
PETR4_TESTS_TAG="0.1.2"   # the version of the petr4 examples the validation tests come from
VALIDATE_EXPECTED="53 OK, 0 FAIL, 42 EXCLUDED"   # the import results of validate

usage() {
 cat <<USAGE
Usage: p4_from_json.sh COMMAND ...

  fetch-tests [PETR4_CLONE]
      Copy the common include files into p4include/ and the .p4/.stf test
      pairs into validation_tests/, taken from the examples of petr4
      $PETR4_TESTS_TAG. Reads them from PETR4_CLONE if given, otherwise clones a
      temporary copy.
  export DIR [INCLUDE_DIR]
      Run petr4 on every .p4 file in DIR, writing FILE.json next to it.
      INCLUDE_DIR defaults to p4include/.
  convert FILE.json [--mode MODE] [--arch ARCH] [--log FILE] [--keep-info]
      Transform one JSON file into a HOL4P4 Script.sml next to it.
      MODE: concrete | stf | symbolic (default: stf if FILE.stf exists,
      otherwise concrete). ARCH: vss | ebpf | v1model (default: detected from
      the program). --keep-info keeps petr4's source-position fields.
      Results are appended to the log (default: $DEFAULT_LOG).
  convert-dir DIR [-j N] [--mode MODE] [--log FILE] [--keep-info]
      Convert every JSON file in DIR, N at a time (default 1). Starts the log
      afresh and prints a summary.
  validate [-j N]
      export + convert-dir on validation_tests/, then Holmake there. Fails
      unless the import gives $VALIDATE_EXPECTED.
USAGE
}

die() { echo "p4_from_json.sh: $*" >&2; exit 1; }

# ---------------------------------------------------------------------------
cmd_fetch_tests() {
 local clone="${1:-}" tmp="" good="examples/checker_tests/good" n=0 f stf base
 if [ -z "$clone" ]; then
  tmp="$(mktemp -d)"
  echo "Cloning petr4 $PETR4_TESTS_TAG..."
  git clone -q --depth 1 --branch "$PETR4_TESTS_TAG" "$PETR4_REPO" "$tmp/petr4"
  clone="$tmp/petr4"
 fi
 git -C "$clone" rev-parse --verify -q "$PETR4_TESTS_TAG^{commit}" >/dev/null \
  || die "$clone has no tag $PETR4_TESTS_TAG (try: git -C $clone fetch --tags)"
 mkdir -p "$SCRIPT_DIR/p4include" "$SCRIPT_DIR/validation_tests"
 for f in examples/core.p4 examples/ebpf_model.p4 examples/v1model.p4 \
          "$good/arith-inline-skeleton.p4" "$good/arith-skeleton.p4" "$good/ebpf_headers.p4"; do
  git -C "$clone" show "$PETR4_TESTS_TAG:$f" > "$SCRIPT_DIR/p4include/$(basename "$f")"
 done
 # Adds the static_assert declarations of the P4-16 specification's core.p4 before the final #endif
 f="$SCRIPT_DIR/p4include/core.p4"
 { head -n -1 "$f"
   printf '%s\n' "/// Static assertions (from the core.p4 of the P4-16 specification)" \
     "extern bool static_assert(bool check, string message);" "extern bool static_assert(bool check);" ""
   tail -n 1 "$f"; } > "$f.tmp" && mv "$f.tmp" "$f"
 # Only those .p4 test files which have an accompanying .stf file
 for stf in $(git -C "$clone" ls-tree --name-only "$PETR4_TESTS_TAG" "$good/" | grep '\.stf$'); do
  base="${stf%.stf}"
  git -C "$clone" show "$PETR4_TESTS_TAG:$stf" > "$SCRIPT_DIR/validation_tests/$(basename "$stf")"
  git -C "$clone" show "$PETR4_TESTS_TAG:$base.p4" > "$SCRIPT_DIR/validation_tests/$(basename "$base").p4"
  n=$((n+1))
 done
 [ -n "$tmp" ] && rm -rf "$tmp"
 echo "Copied 6 include files to p4include/ and $n .p4/.stf pairs to validation_tests/ (petr4 $PETR4_TESTS_TAG)."
}

# ---------------------------------------------------------------------------
cmd_export() {
 local dir="${1:?export: missing directory}" inc="${2:-$SCRIPT_DIR/p4include}" f n=0 failed=0
 command -v petr4 >/dev/null || die "petr4 not found on PATH"
 [ -d "$dir" ] || die "$dir is not a directory"
 for f in "$dir"/*.p4; do
  [ -e "$f" ] || die "no .p4 files in $dir"
  if petr4 typecheck -json -I "$inc" "$f" > "${f%.p4}.json"; then
   n=$((n+1))
  else
   echo "Warning: petr4 failed on $f" >&2; failed=$((failed+1))
  fi
 done
 echo "Exported $n programs to JSON ($failed failed)."
}

# ---------------------------------------------------------------------------
# Parses the options shared by convert and convert-dir into globals.
MODE="" ARCH="" LOG="" KEEP_INFO="" JOBS=1
parse_convert_opts() {
 POSITIONAL=()
 while [ $# -gt 0 ]; do
  case "$1" in
   --mode) MODE="${2:?--mode needs a value}"; shift 2 ;;
   --arch) ARCH="${2:?--arch needs a value}"; shift 2 ;;
   --log) LOG="$(readlink -f "${2:?--log needs a value}")"; shift 2 ;;
   --keep-info) KEEP_INFO=1; shift ;;
   -j) JOBS="${2:?-j needs a number}"; shift 2 ;;
   -*) die "unknown option $1" ;;
   *) POSITIONAL+=("$1"); shift ;;
  esac
 done
 LOG="${LOG:-$DEFAULT_LOG}"
 case "$MODE" in ""|concrete|stf|symbolic) ;; *) die "unknown mode $MODE" ;; esac
 case "$ARCH" in ""|vss|ebpf|v1model) ;; *) die "unknown architecture $ARCH" ;; esac
}

buildheap_bin() {
 local holmake; holmake="$(command -v Holmake)" || die "Holmake not found on PATH"
 echo "$(dirname "$holmake")/buildheap"
}

convert_one() {
 local json; json="$(readlink -f "$1")"
 [ -f "$json" ] || die "$1 does not exist"
 [ -f "$HEAP" ] || die "$HEAP is missing: run Holmake in $SCRIPT_DIR first"
 local base; base="$(basename "$json" .json)"
 rm -f "$(dirname "$json")/${base//-/_}Script.sml"
 local -a opts=()
 [ -n "$MODE" ] && opts+=("mode=$MODE")
 [ -n "$ARCH" ] && opts+=("arch=$ARCH")
 [ -n "$KEEP_INFO" ] && opts+=("keep-info")
 (cd "$SCRIPT_DIR" && "$(buildheap_bin)" --gcthreads=1 --holstate="$HEAP" petr4_to_hol4p4 "$json" "$LOG" "${opts[@]+"${opts[@]}"}")
}

cmd_convert() {
 parse_convert_opts "$@"
 [ ${#POSITIONAL[@]} -eq 1 ] || die "convert takes exactly one JSON file"
 convert_one "${POSITIONAL[0]}"
}

cmd_convert_dir() {
 parse_convert_opts "$@"
 [ ${#POSITIONAL[@]} -eq 1 ] || die "convert-dir takes exactly one directory"
 local dir="${POSITIONAL[0]}" f n=0 ok fail excl
 [ -d "$dir" ] || die "$dir is not a directory"
 rm -f "$LOG"; touch "$LOG"
 for f in "$dir"/*.json; do
  [ -e "$f" ] || die "no .json files in $dir"
  if [ -s "$f" ]; then
   echo "Converting $f..."
   n=$((n+1))
   convert_one "$f" &
   while [ "$(jobs -rp | wc -l)" -ge "$JOBS" ]; do wait -n || true; done
  else
   echo "Warning: $f is empty - did export fail?" >&2
  fi
 done
 wait || true
 ok=$(grep -c '^OK' "$LOG" || true); fail=$(grep -c '^FAIL' "$LOG" || true); excl=$(grep -c '^EXCLUDED' "$LOG" || true)
 echo "Done: $ok OK, $fail FAIL, $excl EXCLUDED, $((n-ok-fail-excl)) crashed without a log entry (see $LOG)."
}

# ---------------------------------------------------------------------------
cmd_validate() {
 local tests="$SCRIPT_DIR/validation_tests" counts
 ls "$tests"/*.p4 >/dev/null 2>&1 || die "no tests in $tests: run 'p4_from_json.sh fetch-tests' first"
 cmd_export "$tests"
 cmd_convert_dir "$tests" "$@"
 counts="$(grep -c '^OK' "$LOG" || true) OK, $(grep -c '^FAIL' "$LOG" || true) FAIL, $(grep -c '^EXCLUDED' "$LOG" || true) EXCLUDED"
 (cd "$tests" && Holmake)
 [ "$counts" = "$VALIDATE_EXPECTED" ] || die "expected $VALIDATE_EXPECTED, but got $counts (see $LOG)"
}

# ---------------------------------------------------------------------------
[ $# -ge 1 ] || { usage; exit 1; }
cmd="$1"; shift
case "$cmd" in
 fetch-tests) cmd_fetch_tests "$@" ;;
 export)      cmd_export "$@" ;;
 convert)     cmd_convert "$@" ;;
 convert-dir) cmd_convert_dir "$@" ;;
 validate)    cmd_validate "$@" ;;
 -h|--help|help) usage ;;
 *) die "unknown command $cmd (try: p4_from_json.sh help)" ;;
esac
