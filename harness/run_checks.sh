#!/bin/zsh
# Type-check every formalization against Mathlib and emit a structural probe.
# Usage: run_checks.sh [parallelism]
set -u
PAR=${1:-6}
SRC=/Users/panda/Desktop/Lean/quick-test/formalizations
TMPL=/Users/panda/Desktop/Lean/quick-test/harness/probe.lean.tmpl
WORK=/Users/panda/Desktop/Lean/quick-test/harness/work
OUT=/Users/panda/Desktop/Lean/quick-test/harness/out
LEANPROJ=/Users/panda/Desktop/Lean/primes

mkdir -p "$WORK" "$OUT"

check_one() {
  local f="$1"
  local id="${f##*Thm2_}"; id="${id%.lean}"
  local probe="$WORK/P_$id.lean"
  cat "$f" > "$probe"
  sed "s/AGENTNS/Agent$id/" "$TMPL" >> "$probe"
  cd "$LEANPROJ" || exit 1
  local start=$SECONDS
  lake env lean "$probe" > "$OUT/$id.log" 2>&1
  local rc=$?
  echo "$id rc=$rc t=$((SECONDS-start))s" >> "$OUT/_status.txt"
}

if [[ "${1:-}" == "--one" ]]; then check_one "$2"; exit; fi

: > "$OUT/_status.txt"
ls "$SRC"/Thm2_*.lean | xargs -P "$PAR" -I{} zsh "$0" --one {}
echo "DONE $(wc -l < "$OUT/_status.txt") files"
