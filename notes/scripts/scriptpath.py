"""Canonical `sys.path` bootstrap for the Phase-39 PENCIL numerics harness.

Importing this module puts every harness layer on `sys.path`, so any script
under `notes/scripts/<dir>/` can import any other harness module by bare
module name, from any working directory.

**The idiom to copy** (three lines, identical in every harness file; the
first two exist only to solve the chicken-and-egg of finding this file):

    import os, sys
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    import scriptpath  # noqa: F401,E402  -- canonical harness path bootstrap

Every harness file sits at `notes/scripts/<layer>/<name>.py`, so the double
`dirname` is `notes/scripts` uniformly — that is the whole reason the idiom
can be uniform.  Put the three lines directly above the harness imports and
below the stdlib ones.

Deliberately NOT a package: the drivers are cited in `notes/Pencil-informal.md`
and `notes/Phase39-design.md` as `python3 notes/scripts/<dir>/<name>.py <flags>`,
and those exact command lines must keep working.  A package would require
`python3 -m`, which would invalidate every recorded reproduce command.

Order is irrelevant: no two harness modules share a basename, so which layer
directory precedes which cannot change what a bare `import` resolves to.
"""
import os
import sys

ROOT = os.path.dirname(os.path.abspath(__file__))
LAYERS = ('escape', 'kbare', 'w4')

for _d in LAYERS:
    _p = os.path.join(ROOT, _d)
    if _p not in sys.path:
        sys.path.insert(0, _p)
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)
