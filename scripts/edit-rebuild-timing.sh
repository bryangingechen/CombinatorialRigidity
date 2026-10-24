#!/usr/bin/env bash
# What one edit to a file costs the next `lake build`: the modules it rebuilds, their summed
# time, the critical path and the wall time.
#
# Usage, from the repository root, with the tree built:
#
#     scripts/edit-rebuild-timing.sh <file.lean> statement <runs> <log-dir>
#     scripts/edit-rebuild-timing.sh <file.lean> proof <runs> <log-dir> <anchor>
#
# `statement` appends a new theorem to the file, which changes its public `.olean`, as an edit to
# a statement, a definition's body or an attribute does. `proof` inserts a `have` on the line
# after the first line containing the fixed string <anchor>, which must end a theorem's statement
# (`... :=`) or sit inside its proof, so the edit reaches that proof alone. Each run's nudge has
# unique content, so Lake's artifact cache cannot serve it. Each run builds the nudged tree with
# `lake build`, keeps the log as <log-dir>/<mode>-<i>.log, restores the file and prints the wall
# time and `scripts/build-critical-path.py`'s summary. A last `lake build` returns the tree to
# the restored file, from the cache.
#
# Written 2026-10-24 for Phase 41a's item P5, the measurement of the `module` conversion
# (`notes/PERFORMANCE.md` *The conversion, layers 19–38*).
set -euo pipefail

file=$1 mode=$2 runs=$3 logdir=$4 anchor=${5:-}
mkdir -p "$logdir"
backup="$logdir/$(basename "$file").orig"
cp "$file" "$backup"
trap 'cp "$backup" "$file"' EXIT

for i in $(seq 1 "$runs"); do
  n=$((RANDOM * 32768 + RANDOM))
  case $mode in
    statement)
      printf '\ntheorem timingNudge%s : (%s : Nat) = %s := rfl\n' "$n" "$n" "$n" >> "$file" ;;
    proof)
      line=$(grep -nF -m1 -- "$anchor" "$file" | cut -d: -f1)
      [ -n "$line" ] || { echo "anchor not found: $anchor" >&2; exit 1; }
      sed -i '' "${line}a\\
  have _timingNudge : (${n} : Nat) = ${n} := rfl
" "$file" ;;
    *) echo "mode must be statement or proof" >&2; exit 1 ;;
  esac
  log="$logdir/$mode-$i.log"
  start=$(date +%s)
  lake build > "$log" 2>&1 || { cp "$backup" "$file"; echo "build failed, see $log" >&2; exit 1; }
  end=$(date +%s)
  cp "$backup" "$file"
  echo "== $mode run $i: wall $((end - start)) s"
  python3 scripts/build-critical-path.py "$log" | head -3
done

lake build > "$logdir/restore.log" 2>&1
echo "== restored: $(grep -c 'Built ' "$logdir/restore.log" || true) modules rebuilt"
