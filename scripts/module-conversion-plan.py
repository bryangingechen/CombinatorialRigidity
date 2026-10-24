#!/usr/bin/env python3
"""The project's non-`module` files, the order that converts them, and what to check in each.

A `module` file cannot import a non-`module` one, so a conversion that keeps every commit
building runs bottom-up: a file can be converted once every project file it imports is a
`module`. This script reads the sources at the working tree and prints:

- the non-`module` files, by directory, with their line counts;
- the conversion layers: layer 0 imports no non-`module` project file, and layer k imports one
  of layer k - 1. A layer converts in any order, or in one commit;
- for each file, the constructs that the module system treats differently and that a converter
  should look at before the build does: `private` declarations (an error when a public
  statement or an exposed body names one, since the project allows no
  `backward.privateInPublic`), metaprograms (`macro`, `elab`, `syntax`, `initialize`, which may
  need `meta`), `#eval` or `native_decide`, and `hidden`: the definitions of an
  already-`module` project file that it does not expose, named in an `unfold`, `delta`, `rw`
  or `simp` list. A non-`module` file sees their bodies and a `module` one does not. Proofs
  that unfold them by `rfl` or `decide` are not counted, and neither are mathlib's.

The converted files themselves get a file-wide `@[expose] public section`, so their own
definitions keep unfolding. Two failure classes no script sees, both met by the trial
conversion of layers 0 to 2 (`notes/PERFORMANCE.md` *The `module` conversion recon*): a
`module` file sees only the public closure of its imports, so a tactic or lemma reached through
an upstream file's private import becomes unknown and needs a direct `import`; and a name can
resolve differently.

Usage, from anywhere (sources resolve against the repository root):

    python3 scripts/module-conversion-plan.py [--layers] [--hazards]
    python3 scripts/module-conversion-plan.py --convert <file.lean>...

With no flag it prints everything. `--convert` applies `CombinatorialRigidity/LEAN-OPS.md`
*Module-system conversion*'s recipe to each file in place: `module` above the imports, each
`import` made `public import`, and a file-wide `@[expose] public section` after the module
docstring, so that every definition keeps unfolding. Written 2026-10-24 for Phase 41a's item
P2, the recon of the molecular chain's `module` conversion (`notes/PERFORMANCE.md` *Build
critical path*).
"""

import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROJECT = "CombinatorialRigidity"
MODULE = re.compile(r"^module\s*(?:--.*)?$", re.M)
IMPORT = re.compile(rf"^(?:public )?(?:meta )?import (?:all )?({PROJECT}[\w.]*)", re.M)
HAZARDS = {
    "private": re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?private\s", re.M),
    "meta": re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)?(?:local |scoped )?"
        r"(?:macro|macro_rules|elab|elab_rules|syntax|declare_syntax_cat|initialize"
        r"|register_simp_attr|register_option)\b",
        re.M,
    ),
    "eval": re.compile(r"#eval\b|\bnative_decide\b"),
}
DEF = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*def\s+([^\s({\[:]+)", re.M)
UNFOLD = re.compile(
    r"\b(?:unfold|delta)\b([^\n]*)"
    r"|\b(?:rw|rwa|erw|simp_rw|nth_rw\s+\d+|simp|simp only|dsimp|dsimp only|simpa)\s*\[([^\]]*)\]"
)
IDENT = re.compile(r"[^\s,←\[\]()]+")


def hidden_defs(text, nonmod):
    """Short names of the definitions that `module` files do not expose."""
    names = set()
    for mod, src in text.items():
        if mod in nonmod or "@[expose] public section" in src:
            continue
        lines = src.splitlines()
        for i, line in enumerate(lines):
            m = DEF.match(line)
            before = lines[i - 1] if i else ""
            if m and "expose" not in line and not (before.startswith("@[") and "expose" in before):
                names.add(m.group(1).rsplit(".", 1)[-1])
    return names


def unfolds(src, names):
    count = 0
    for m in UNFOLD.finditer(src):
        idents = IDENT.findall(m.group(1) or m.group(2) or "")
        count += sum(1 for i in idents if i.rsplit(".", 1)[-1] in names)
    return count


def sources():
    files = {}
    for path in sorted((ROOT / PROJECT).rglob("*.lean")):
        files[".".join(path.relative_to(ROOT).with_suffix("").parts)] = path
    files[PROJECT] = ROOT / f"{PROJECT}.lean"
    return files


def convert(path):
    lines = Path(path).read_text().splitlines(keepends=True)
    if any(MODULE.match(line) for line in lines):
        sys.exit(f"{path} is already a `module`")
    first_import = next(i for i, line in enumerate(lines) if line.startswith("import "))
    doc = next(i for i, line in enumerate(lines) if line.startswith("/-!"))
    doc_end = next(i for i in range(doc, len(lines)) if lines[i].rstrip().endswith("-/"))
    out = lines[:first_import] + ["module\n", "\n"]
    for i in range(first_import, len(lines)):
        line = lines[i]
        out.append("public " + line if line.startswith("import ") else line)
        if i == doc_end:
            out += ["\n", "@[expose] public section\n"]
    Path(path).write_text("".join(out))


def main():
    if sys.argv[1:2] == ["--convert"]:
        for path in sys.argv[2:]:
            convert(path)
        return
    flags = set(sys.argv[1:])
    show_layers = not flags or "--layers" in flags
    show_hazards = not flags or "--hazards" in flags
    files = sources()
    text = {mod: path.read_text() for mod, path in files.items()}
    nonmod = {mod for mod, src in text.items() if not MODULE.search(src)}
    deps = {mod: [i for i in IMPORT.findall(text[mod]) if i in nonmod] for mod in nonmod}
    lines = {mod: len(text[mod].splitlines()) for mod in nonmod}

    print(f"{len(nonmod)} of {len(files)} files are not `module`s, "
          f"{sum(lines.values())} lines.")
    by_dir = defaultdict(list)
    for mod in nonmod:
        parts = mod.split(".")[1:]
        by_dir[".".join(parts[:2]) if len(parts) > 2 else ".".join(parts[:1]) or PROJECT].append(mod)
    for d, mods in sorted(by_dir.items(), key=lambda kv: -len(kv[1])):
        print(f"  {d}: {len(mods)} files, {sum(lines[m] for m in mods)} lines")

    layer = {}

    def depth(mod):
        if mod not in layer:
            layer[mod] = 1 + max((depth(d) for d in deps[mod]), default=-1)
        return layer[mod]

    for mod in nonmod:
        depth(mod)
    layers = defaultdict(list)
    for mod, k in layer.items():
        layers[k].append(mod)

    if show_layers:
        print(f"\n{len(layers)} conversion layers:")
        for k in sorted(layers):
            mods = sorted(layers[k])
            print(f"  layer {k}: {len(mods)} files, {sum(lines[m] for m in mods)} lines")
            for mod in mods:
                print(f"    {mod.removeprefix(PROJECT + '.')} ({lines[mod]})")

    if show_hazards:
        totals = Counter()
        names = hidden_defs(text, nonmod)
        print("\nConstructs to check, by file (only the nonzero counts):")
        for k in sorted(layers):
            for mod in sorted(layers[k]):
                counts = {h: len(p.findall(text[mod])) for h, p in HAZARDS.items()}
                counts["hidden"] = unfolds(text[mod], names)
                totals.update(counts)
                shown = ", ".join(f"{h} {n}" for h, n in counts.items() if n)
                if shown:
                    print(f"  [{k}] {mod.removeprefix(PROJECT + '.')}: {shown}")
        print("Totals: " + ", ".join(f"{h} {totals[h]}" for h in [*HAZARDS, "hidden"])
              + f" (of {len(names)} hidden definitions)")


if __name__ == "__main__":
    main()
