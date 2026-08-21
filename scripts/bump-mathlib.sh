#!/usr/bin/env bash
# Sync this project's mathlib pin -- and mathlib's *transitive* pins -- to a
# target mathlib revision, without running `lake update`.
#
#   scripts/bump-mathlib.sh master              # dry run: show the diff
#   scripts/bump-mathlib.sh master --apply      # write the files
#   scripts/bump-mathlib.sh v4.34.0-rc1 --apply # a tag works too
#   scripts/bump-mathlib.sh 653c36f0 --apply    # so does a (short) SHA
#
# WHY THIS EXISTS
# ---------------
# `lake update mathlib` bumps *only* mathlib, leaving `batteries`, `aesop`, and
# the rest at the revisions mathlib *used to* want. `lake exe cache get` hashes
# over the whole dependency set, so the hash misses and the cache fetch fails --
# which is exactly the false positive that kept `hopscotch.yml` reporting a
# phantom regression from 2026-05-15 until the v4.34.0-rc1 bump. Copying
# mathlib's own transitive pins verbatim is the fix. `lake update` is also
# blocked by a PreToolUse hook here after an OOM incident, so this script
# doubles as the sanctioned agent-side route.
#
# Non-mathlib dependencies (`Matroid`, `checkdecls`, and `loogle` which arrives
# transitively via `Matroid`) keep their own pins -- bumping those is a separate,
# deliberate decision.
#
# See `notes/ToolchainBumps.md` *Playbook* for the surrounding process, and
# `CombinatorialRigidity/CLAUDE.md` *Build discipline* for the `lake update` rule.

set -euo pipefail

MATHLIB_REPO="leanprover-community/mathlib4"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

usage() { sed -n '2,26p' "${BASH_SOURCE[0]}" | sed 's/^# \{0,1\}//'; exit 2; }

[[ $# -ge 1 ]] || usage
TARGET="$1"; shift
APPLY=0
while [[ $# -gt 0 ]]; do
  case "$1" in
    --apply) APPLY=1 ;;
    -h|--help) usage ;;
    *) echo "unknown argument: $1" >&2; usage ;;
  esac
  shift
done

echo "resolving ${MATHLIB_REPO}@${TARGET} ..."
SHA="$(curl -fsSL "https://api.github.com/repos/${MATHLIB_REPO}/commits/${TARGET}" \
  | python3 -c 'import json,sys; print(json.load(sys.stdin)["sha"])')"
echo "  -> ${SHA}"

RAW="https://raw.githubusercontent.com/${MATHLIB_REPO}/${SHA}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
curl -fsSL "${RAW}/lake-manifest.json" -o "$TMP/mathlib-manifest.json"
curl -fsSL "${RAW}/lean-toolchain"     -o "$TMP/lean-toolchain"

python3 - "$ROOT" "$TMP" "$SHA" "$APPLY" <<'PYEOF'
import json, sys
from pathlib import Path

root, tmp, sha, apply = Path(sys.argv[1]), Path(sys.argv[2]), sys.argv[3], sys.argv[4] == "1"

ours_path = root / "lake-manifest.json"
ours = json.loads(ours_path.read_text())
theirs = json.loads((tmp / "mathlib-manifest.json").read_text())
upstream = {p["name"]: p for p in theirs["packages"]}

changes = []
for pkg in ours["packages"]:
    name = pkg["name"]
    if name == "mathlib":
        if pkg["rev"] != sha:
            changes.append((name, pkg["rev"], sha))
            pkg["rev"] = sha
        continue
    up = upstream.get(name)
    if up is None:
        continue                      # not a mathlib dep: Matroid, checkdecls, loogle
    for field in ("rev", "inputRev"):
        if pkg.get(field) != up.get(field):
            changes.append((f"{name}.{field}", pkg.get(field), up.get(field)))
            pkg[field] = up.get(field)

# Any mathlib dep we do not carry at all is a new transitive requirement.
missing = [n for n in upstream if n not in {p["name"] for p in ours["packages"]}]

tc_path = root / "lean-toolchain"
tc_new = (tmp / "lean-toolchain").read_text().strip()
tc_old = tc_path.read_text().strip()

def short(v):
    return v[:12] if isinstance(v, str) and len(v) == 40 else repr(v)

if tc_old != tc_new:
    print(f"\nlean-toolchain: {tc_old}  ->  {tc_new}")
else:
    print(f"\nlean-toolchain: {tc_old} (unchanged)")

if changes:
    print("\nlake-manifest.json:")
    for name, was, now in changes:
        print(f"  {name:24s} {short(was)}  ->  {short(now)}")
else:
    print("\nlake-manifest.json: already in sync")

if missing:
    print("\n⚠ mathlib now requires packages we do not carry -- add them by hand:")
    for n in sorted(missing):
        print(f"    {n}: {upstream[n]['url']} @ {short(upstream[n]['rev'])}")

if not apply:
    print("\n(dry run; pass --apply to write)")
    sys.exit(0)

if changes:
    ours_path.write_text(json.dumps(ours, indent=1) + "\n")
if tc_old != tc_new:
    tc_path.write_text(tc_new + "\n")
print("\nwritten.")
PYEOF

if [[ $APPLY -eq 1 ]]; then
  cat <<'MSG'

Next, in order:
  1. `lake env lean --version`  -- materializes every dep; fails loudly if the
     manifest and the lakefile disagree. Do this before any build.
  2. `LAKE_CACHE_DIR=<writable-dir> lake build`  -- the cache dir is MANDATORY
     on macOS here; Lake reports a failed cache write as a *build failure* and
     silently stops covering the tree. Check the log has zero
     `failed to cache artifact` lines.
  3. `LAKE_CACHE_DIR=<writable-dir> lake lint`.
  4. `python3 scripts/sweep-deprecations.py <build-log>` for the rename fallout.
MSG
fi
