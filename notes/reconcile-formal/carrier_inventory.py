"""Count the references to `PanelHingeFramework`'s constructors, by module and declaration.

The Phase 41 design recon's inventory (`notes/Phase41-design.md` §2), run at commit `95e2f418`.
It reads the exact constant references that Lean records in the built `.ilean` files, so the
tree must be built first: `lake build --no-build` must report every target up to date. (File
modification times say nothing here: lake decides by content hashes, and a checkout leaves
sources newer than unchanged build outputs.) Counted: the structure's `mk` and the constructors `ofNormals`, `ofParam`,
`withMomentNormals`, `withGraph`, `withNormal`, and the three `reaim*` definitions.

Usage, from the repository root:

    python3 notes/reconcile-formal/carrier_inventory.py [--json OUT]

The last line is the total: modules, declarations, references, and references per constructor.
`--json` also writes the sites (module -> declaration -> [constructor, line]).
"""

import argparse
import collections
import glob
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "CombinatorialRigidity.Molecular.PanelHingeFramework."
CTORS = ["mk", "ofNormals", "ofParam", "withMomentNormals", "withGraph", "withNormal"]
REAIM = ("reaim", "reaimSub", "reaimSubLink")


def constructor_of(name):
    """The constructor a constant name refers to, or `None`."""
    if name.startswith(PREFIX) and name[len(PREFIX):] in CTORS:
        return name[len(PREFIX):]
    last = name.split(".")[-1]
    if "PanelHingeFramework" in name and last in REAIM:
        return last
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--json", help="also write the sites to this file")
    args = parser.parse_args()

    sites = collections.defaultdict(lambda: collections.defaultdict(list))
    pattern = str(ROOT / ".lake/build/lib/lean/CombinatorialRigidity/**/*.ilean")
    for ilean in sorted(glob.glob(pattern, recursive=True)):
        with open(ilean) as f:
            data = json.load(f)
        module = data["module"]
        source = ROOT / (module.replace(".", "/") + ".lean")
        if not source.exists():
            continue
        for key, value in data["references"].items():
            ref = json.loads(key)
            if "c" not in ref:
                continue
            ctor = constructor_of(ref["c"]["n"])
            if ctor is None:
                continue
            for usage in value["usages"]:
                decl = usage[4] if len(usage) > 4 else "?"
                sites[module][decl].append((ctor, usage[0] + 1))

    n_decls = n_refs = 0
    per_ctor = collections.Counter()
    for module in sorted(sites):
        decls = sites[module]
        refs = [site for uses in decls.values() for site in uses]
        counts = collections.Counter(ctor for ctor, _ in refs)
        per_ctor.update(counts)
        n_decls += len(decls)
        n_refs += len(refs)
        short = module.replace("CombinatorialRigidity.Molecular.", "")
        print(f"{short}: decls={len(decls)} refs={len(refs)} {dict(sorted(counts.items()))}")
    print(f"modules {len(sites)} decls {n_decls} refs {n_refs}",
          dict(per_ctor.most_common()))

    if args.json:
        with open(args.json, "w") as f:
            json.dump({m: dict(d) for m, d in sites.items()}, f, indent=0)


if __name__ == "__main__":
    main()
