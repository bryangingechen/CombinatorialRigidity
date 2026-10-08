/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity

/-!
# The Lean half of `scripts/blueprint-deps.py`

`scripts/blueprint-deps.py` runs this file with `lake lean scripts/BlueprintDeps.lean` (never
`lake env lean`, which drops the lakefile's options). It is not part of the `CombinatorialRigidity`
library and `lake build` never compiles it. Two environment variables drive it:

* `BLUEPRINT_DEPS_PINS`: a file with one declaration name per line (the blueprint's `\lean{…}`
  pins and `formalization.yaml`'s main results, written by the Python script);
* `BLUEPRINT_DEPS_OUT`: the JSON-lines file to write.

For every constant declared in a project module (a module named `CombinatorialRigidity` or
`CombinatorialRigidity.*`, the `Mathlib/` and `Matroid/` mirrors included) and for every pinned
constant, it writes one line `{"n", "k", "m", "t", "v"}`: the name, its kind, its module, and the
constants that occur in its type (`t`) and in its value (`v`), each list cut down to the constants
that are project constants or pinned. An inductive type's `v` is its constructors. A pin that names
no constant gets a line `{"missing": name}`. Everything else (the closures, the comparison with
`\uses`) is the Python script's.

**The importer kind matters, and this file is deliberately *not* a `module`.** 65 of the 152
files under `CombinatorialRigidity/` use Lean's module system, and a `module` file that imports
one sees only its exported interface. Measured on 2026-10-07 with two probes importing
`CombinatorialRigidity.Laman` and `CombinatorialRigidity.Sparsity`: in a `module` probe,
`SimpleGraph.IsLaman.two_le_degree` and `SimpleGraph.IsLaman.isSparse` arrive as `axiom`s with no
value, and no private declaration of `Sparsity` is visible; in a non-`module` probe both theorems
have their proofs, and the private declarations, with their `_proof_` and `_simp_` auxiliaries,
are there. A non-`module` file imports at the private level, so it sees every body. A `module`
file could not import the library root anyway, since the root and the other 87 files are not
modules.
-/

open Lean

namespace BlueprintDeps

/-- The constant's kind, as the Python script prints it. -/
def kind : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "def"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

/-- The module that declares `n`, if it is an imported constant. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  (env.getModuleIdxFor? n).map fun idx => env.header.moduleNames[idx.toNat]!

/-- Is `n` declared in a project module? -/
def isProject (env : Environment) (n : Name) : Bool :=
  match moduleOf? env n with
  | some m => (`CombinatorialRigidity).isPrefixOf m
  | none => false

/-- The JSON line for one constant. `keep` cuts the reference lists down. -/
def record (env : Environment) (keep : Name → Bool) (ci : ConstantInfo) : String :=
  let refs (e : Expr) : Array Name := e.getUsedConstants.filter keep
  let value : Array Name := match ci.value? (allowOpaque := true), ci with
    | some v, _ => refs v
    | none, .inductInfo i => i.ctors.toArray.filter keep
    | none, _ => #[]
  let strs (ns : Array Name) : Json := toJson ((ns.map toString).qsort (· < ·))
  (Json.mkObj [("n", toString ci.name), ("k", kind ci),
    ("m", toString ((moduleOf? env ci.name).getD .anonymous)),
    ("t", strs (refs ci.type)), ("v", strs value)]).compress

/-- Read the pins, scan the environment, write the JSON lines. -/
def run : CoreM Unit := do
  let some pinsPath ← IO.getEnv "BLUEPRINT_DEPS_PINS"
    | throwError "BLUEPRINT_DEPS_PINS is not set"
  let some outPath ← IO.getEnv "BLUEPRINT_DEPS_OUT"
    | throwError "BLUEPRINT_DEPS_OUT is not set"
  let pins : NameSet := (← IO.FS.lines pinsPath).foldl (init := {}) fun s l =>
    let l := l.trimAscii.toString
    if l.isEmpty then s else s.insert l.toName
  let env ← getEnv
  let keep (c : Name) : Bool := isProject env c || pins.contains c
  let mut lines : Array String := #[]
  let mut seen : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    if isProject env n then
      lines := lines.push (record env keep ci)
      seen := seen.insert n
  let mut missing : Array String := #[]
  for p in pins do
    unless seen.contains p do
      match env.find? p with
      | some ci => lines := lines.push (record env keep ci)
      | none => missing := missing.push (Json.mkObj [("missing", toString p)]).compress
  let header := Json.mkObj [("tool", "scripts/BlueprintDeps.lean"),
    ("lean", Lean.versionString), ("pins", pins.toList.length), ("constants", lines.size)]
  let body := (lines.qsort (· < ·)).toList ++ (missing.qsort (· < ·)).toList
  IO.FS.writeFile outPath <| "\n".intercalate (header.compress :: body) ++ "\n"

end BlueprintDeps

run_cmd Elab.Command.liftCoreM BlueprintDeps.run
