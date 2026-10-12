#!/usr/bin/env bash
set -euo pipefail

repo_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
: "${TLA_TOOLS_JAR:?Set TLA_TOOLS_JAR to a pinned tla2tools.jar}"
: "${TLAPM_BIN:?Set TLAPM_BIN to the real tlapm binary, not a detached symlink}"

cd "$repo_dir/tla"
set -x

for module in TemporalPredicates GenericMachines GenericMachineModel Mutex; do
  java -cp "$TLA_TOOLS_JAR" tla2sany.SANY "$module.tla"
done

"$TLAPM_BIN" TemporalRules.tla
"$TLAPM_BIN" TemporalSetRules.tla
"$TLAPM_BIN" TemporalMacroRules.tla
"$TLAPM_BIN" TemporalFoldRules.tla
"$TLAPM_BIN" TemporalMacroChainRules.tla
"$TLAPM_BIN" TemporalActionRules.tla

java -XX:+UseParallelGC -cp "$TLA_TOOLS_JAR" tlc2.TLC \
  -workers 1 -deadlock -config GenericMachineModel.cfg GenericMachineModel.tla

java -XX:+UseParallelGC -cp "$TLA_TOOLS_JAR" tlc2.TLC \
  -workers 1 -deadlock -config Mutex.cfg Mutex.tla

unfair_log="$(mktemp)"
trap 'rm -f "$unfair_log"' EXIT
if java -XX:+UseParallelGC -cp "$TLA_TOOLS_JAR" tlc2.TLC \
  -workers 1 -deadlock -config MutexUnfair.cfg Mutex.tla >"$unfair_log" 2>&1; then
  echo 'Unfair mutex unexpectedly passed eventual termination' >&2
  exit 1
fi
if ! grep -q 'Temporal property EventuallyDone was violated' "$unfair_log"; then
  cat "$unfair_log" >&2
  echo 'Unfair mutex failed without the expected liveness counterexample' >&2
  exit 1
fi
echo 'Unfair mutex produced the expected liveness counterexample.'
