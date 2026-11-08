"""PENCIL-NATURAL recon, track R1 (N1): the module import closures (Phase 43a, banked).

Reads every `.lean` file under `<root>/CombinatorialRigidity` and prints, for each
`Molecule.Pencil.<module>` named on the command line, the size of its project import
closure and which of the `d = 3` generic modules it imports; then the importers of
`Grade.Generic` and `MainComponent.Statements`, and the modules outside both closures that
import a `Pencil` module (the consumer analysis of `notes/PencilNatural.md` §3 N1).
An import is not a use: the kernel closure is `N1Spike.lean`'s.

  python3 notes/pencil-natural/n1_imports.py . Grade.Generic MainComponent.Statements
"""
import re, os, sys
root = sys.argv[1]
imp = {}
for dp, dn, fn in os.walk(os.path.join(root, 'CombinatorialRigidity')):
    for f in fn:
        if f.endswith('.lean'):
            p = os.path.join(dp, f)
            mod = os.path.relpath(p, root)[:-5].replace('/', '.')
            deps = []
            for line in open(p):
                m = re.match(r'\s*(public\s+)?(meta\s+)?import\s+(\S+)', line)
                if m: deps.append(m.group(3))
            imp[mod] = deps
def closure(m):
    seen = set(); st = [m]
    while st:
        x = st.pop()
        for d in imp.get(x, []):
            if d not in seen:
                seen.add(d); st.append(d)
    return seen
P = 'CombinatorialRigidity.Molecular.Molecule.Pencil.'
for a in sys.argv[2:]:
    c = closure(P + a)
    print(a, 'closure size', len([x for x in c if x.startswith('CombinatorialRigidity')]))
    for b in ['MainComponent.Statements', 'X0', 'MainComponent.GenericBase', 'MainComponent.GenericEar', 'MainComponent.GenericTriangle', 'MainComponent.GenericSteer', 'MainComponent.GoodEar', 'MainComponent.CoverageTheoremS', 'Grade.Generic', 'Pair', 'Pair2', 'Statement', 'ArmsAssembly', 'Arms']:
        print('   imports', b, (P+b) in c)
# who imports Grade.Generic / Statements
for t in ['Grade.Generic', 'MainComponent.Statements']:
    print('importers of', t, [m for m in imp if (P+t) in imp[m]])

# reverse closure: modules importing (transitively) any Pencil module, outside closure of Generic+Statements
base = closure(P+'Grade.Generic') | closure(P+'MainComponent.Statements') | {P+'Grade.Generic', P+'MainComponent.Statements'}
pencilmods = {m for m in imp if m.startswith(P)}
outside = [m for m in imp if m not in base and (closure(m) & pencilmods)]
print('outside importers of pencil modules:', outside)
