#!/usr/bin/env python3
"""The critical path of a `lake build`: the longest chain of rebuilt project modules.

Reads the per-module times that a `lake build` log prints (`Built <module> (<t>s)`) and the
project's import graph (the `import` lines of the sources, at the working tree), and prints:
the number of modules rebuilt, the sum of their times (the work, which parallel jobs share) and
the longest chain of rebuilt modules each importing the previous (which no number of jobs
shortens), module by module. When the chain is close to the build's wall time, the build is
chain-bound: fewer or shorter links speed it up, and more parallelism does not.

Usage, from anywhere (sources resolve against the repository root):

    python3 scripts/build-critical-path.py <lake-build-log>

Written 2026-10-24 for the measurement in `notes/PERFORMANCE.md` *Build critical path*.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT = "CombinatorialRigidity"
BUILT = re.compile(rf"Built ({PROJECT}[\w.]*) \((?:(\d+)m ?)?([0-9.]+)?s?\)")
IMPORT = re.compile(rf"^(?:public )?import ({PROJECT}[\w.]*)", re.M)


def module_times(log):
    times = {}
    for mod, mins, secs in BUILT.findall(log):
        times[mod] = 60 * float(mins or 0) + float(secs or 0)
    return times


def imports(mod):
    path = ROOT / (mod.replace(".", "/") + ".lean")
    return IMPORT.findall(path.read_text()) if path.exists() else []


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    times = module_times(Path(sys.argv[1]).read_text())
    if not times:
        sys.exit("no `Built <module> (<t>s)` lines for project modules in the log")
    memo = {}

    def chain(mod):
        if mod not in memo:
            best = (0.0, [])
            for dep in imports(mod):
                if dep in times:
                    best = max(best, chain(dep), key=lambda c: c[0])
            memo[mod] = (best[0] + times[mod], best[1] + [mod])
        return memo[mod]

    length, path = max((chain(m) for m in times), key=lambda c: c[0])
    print(f"modules rebuilt {len(times)}; sum of module times {sum(times.values()):.0f}s; "
          f"critical path {length:.0f}s over {len(path)} modules")
    for mod in path:
        print(f"  {times[mod]:6.0f}s  {mod.removeprefix(PROJECT + '.')}")


if __name__ == "__main__":
    main()
