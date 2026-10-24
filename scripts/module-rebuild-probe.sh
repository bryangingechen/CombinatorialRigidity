#!/usr/bin/env bash
# Which importers does a proof-only edit of a `module` file rebuild?
#
# Writes four throwaway files under CombinatorialRigidity/ScratchP2/: a `module` file A, a
# `module` file B and a non-`module` file C that each import A, and a `module` file D that
# imports B. It builds them, edits A four ways, and after each edit prints the modules Lake
# rebuilt. A module Lake does not list was up to date. The files and their build outputs are
# removed on exit.
#
# Lake keys a `module` importer on the imported file's public `.olean` alone, and a non-`module`
# importer on all of its artifacts, the private `.olean` with the proofs included
# (`Lake/Build/Module.lean`: `addImport`, `computeMetaExportInfo`). Expected, on v4.36.0-rc1:
#   1. proof-only edit, axioms unchanged:   A, C          (B and D spared)
#   2. proof-only edit adding a line:       A, C          (declaration ranges are not public)
#   3. proof-only edit changing the axioms: A, B, C, D    (the public `.olean` lists each
#                                                          theorem's axioms)
#   4. statement edit:                      A, B, C, D
#
# Usage, from the repository root: scripts/module-rebuild-probe.sh
# Written 2026-10-24 for Phase 41a's item P2 (notes/PERFORMANCE.md *Build critical path*).
set -euo pipefail
cd "$(dirname "$0")/.."
DIR=CombinatorialRigidity/ScratchP2
OUT=.lake/build/lib/lean/CombinatorialRigidity/ScratchP2
IR=.lake/build/ir/CombinatorialRigidity/ScratchP2
[ -e "$DIR" ] && { echo "$DIR exists; remove it first" >&2; exit 1; }
trap 'rm -rf "$DIR" "$OUT" "$IR"' EXIT
mkdir -p "$DIR"
NONCE="n$(date +%s)$RANDOM"   # unique content, so no module is replayed from Lake's cache

cat > "$DIR/A.lean" <<'EOF'
module

public import Mathlib.Order.Basic

public section

namespace ScratchP2

theorem t1 (n : Nat) : n < n + 1 := by
  exact Nat.lt_succ_self n

theorem t2 (n : Nat) : n ≤ n + 1 := by
  omega

end ScratchP2
EOF
cat > "$DIR/B.lean" <<EOF
module

public import CombinatorialRigidity.ScratchP2.A

public section

theorem ScratchP2.useB : 5 < 5 + 1 := ScratchP2.t1 5
theorem ScratchP2.$NONCE.b : True := trivial
EOF
cat > "$DIR/C.lean" <<EOF
import CombinatorialRigidity.ScratchP2.A

theorem ScratchP2.useC : 5 < 5 + 1 := ScratchP2.t1 5
theorem ScratchP2.$NONCE.c : True := trivial
EOF
cat > "$DIR/D.lean" <<EOF
module

public import CombinatorialRigidity.ScratchP2.B

public section

theorem ScratchP2.useD : 5 < 5 + 1 := ScratchP2.useB
theorem ScratchP2.$NONCE.d : True := trivial
EOF

step() {
  echo "== $1"
  local log
  log=$(lake build CombinatorialRigidity.ScratchP2.B CombinatorialRigidity.ScratchP2.C \
    CombinatorialRigidity.ScratchP2.D 2>&1) || { echo "$log" >&2; exit 1; }
  { grep -oE '(Built|Replayed|Fetched).*ScratchP2\.[A-D]' <<<"$log" || true; } \
    | sed 's/.*ScratchP2\./  /' | sort
}
edit() { python3 -c 'import sys; p, a, b = sys.argv[1:]; s = open(p).read(); assert a in s; open(p, "w").write(s.replace(a, b, 1))' "$DIR/A.lean" "$1" "$2"; }

step "0. baseline build"
edit "exact Nat.lt_succ_self n" "exact Nat.lt_add_one n"
step "1. proof-only edit, axioms unchanged (both proofs axiom-free)"
edit "  exact Nat.lt_add_one n" "  have _h : True := trivial
  exact Nat.lt_add_one n"
step "2. proof-only edit adding a line (shifts t2)"
edit "  have _h : True := trivial
  exact Nat.lt_add_one n" "  omega"
step "3. proof-only edit changing the axioms (omega uses propext, Quot.sound)"
edit "n ≤ n + 1" "n ≤ n + 2"
step "4. statement edit"
