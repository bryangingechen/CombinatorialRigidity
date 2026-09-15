#!/usr/bin/env bash
#
# blueprint/verify.sh — full blueprint + checkdecls gate as one command.
#
# Runs `inv bp` (latexmk → PDF + print.bbl → src/web.bbl), `inv web`
# (plastex → blueprint/web/ + regenerated blueprint/lean_decls), and
# `lake exe checkdecls blueprint/lean_decls` (verifies every
# `\lean{...}` pointer resolves to a real Lean declaration). All three
# are the per-commit gates documented in blueprint/CLAUDE.md *Static
# checks before commit* — bundled here so the agent doesn't reassemble
# the cd/PATH/venv invocation by hand each time.
#
# Run from anywhere; the script computes the repo root from its own
# location. Falls back to /Library/TeX/texbin if `xelatex` isn't
# already on PATH (BasicTeX default on macOS); on other platforms the
# fallback is a no-op and the script assumes xelatex is reachable.
#
# Exit codes: 0 on full success, non-zero on the first failing step.
# `checkdecls` prints nothing on success — silence on the final step
# is what "passed" looks like.

set -euo pipefail

SCRIPT_DIR="$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )"
REPO_ROOT="$( cd -- "$SCRIPT_DIR/.." && pwd )"

if ! command -v xelatex >/dev/null 2>&1; then
    if [ -x /Library/TeX/texbin/xelatex ]; then
        export PATH="/Library/TeX/texbin:$PATH"
    else
        echo "verify.sh: xelatex not found on PATH and /Library/TeX/texbin/xelatex does not exist." >&2
        echo "  See blueprint/CLAUDE.md *One-time setup* for installing BasicTeX (macOS) or your distro's xelatex package." >&2
        exit 1
    fi
fi

if [ ! -f "$SCRIPT_DIR/.venv/bin/activate" ]; then
    echo "verify.sh: blueprint/.venv not found." >&2
    echo "  See blueprint/CLAUDE.md *One-time setup* for venv creation." >&2
    exit 1
fi

# shellcheck source=/dev/null
source "$SCRIPT_DIR/.venv/bin/activate"

cd "$SCRIPT_DIR"
echo "==> inv bp"
inv bp

echo
echo "==> inv web"
WEB_LOG="$(mktemp)"
trap 'rm -f "$WEB_LOG"' EXIT
inv web 2>&1 | tee "$WEB_LOG"

# plastex reports a failed plugin load as ONE log line and then carries on
# WITHOUT the `blueprint` package: `\lean`/`\leanok`/`\uses` degrade to
# "unrecognized command" warnings, lean_decls and the dep graph are not
# regenerated, and the checkdecls step below passes vacuously against the
# stale list. That read as "all gates passed" from 2026-07-30 to 2026-09-15
# (notes/FRICTION.md, the `[blueprint] verify.sh reports "all gates passed"`
# entry). Fail hard on the log line, and refuse a lean_decls older than any
# source file.
if grep -q 'ERROR: Loading package' "$WEB_LOG"; then
    echo "verify.sh: plastex failed to load a package (the ERROR line above); lean_decls was NOT regenerated." >&2
    echo "  Usual cause: the venv's pygraphviz is linked against a graphviz dylib Homebrew no longer ships" >&2
    echo "  -- see blueprint/SETUP-AND-PITFALLS.md *Pitfalls* (libcgraph)." >&2
    exit 1
fi
if [ ! -f "$SCRIPT_DIR/lean_decls" ] || \
   [ -n "$(find "$SCRIPT_DIR/src" -name '*.tex' -newer "$SCRIPT_DIR/lean_decls" -print -quit)" ]; then
    echo "verify.sh: blueprint/lean_decls is missing or older than a source .tex file -- inv web did not regenerate it;" >&2
    echo "  refusing to run checkdecls against a stale list." >&2
    exit 1
fi

cd "$REPO_ROOT"
echo
echo "==> lake exe checkdecls blueprint/lean_decls"
lake exe checkdecls blueprint/lean_decls
echo "    (no output = all \\lean{...} names resolve)"

echo
echo "blueprint/verify.sh: all gates passed."
