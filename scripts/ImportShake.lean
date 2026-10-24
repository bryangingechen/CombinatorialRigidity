/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity

/-!
# Unused imports of the project's non-`module` files

`lake shake` minimizes imports from the built `.olean`s, but on this toolchain (Lean v4.36.0-rc1)
it refuses any import closure with a non-`module` file in it ("`lake shake` only works with
`module`s currently"), and 90 of the project's 152 files are not `module`s. This file runs the same
analysis on them. It follows `Lake.CLI.Shake` (Mario Carneiro and Sebastian Ullrich, in the Lean
toolchain), cut down to the one import kind a non-`module` file has.

A module **needs** module `j` when one of its constants mentions a constant of `j` in its type or
value (a reserved name, such as an equation lemma, does not count; an `_simp_…` auxiliary counts as
its base declaration), when it mentions a constant whose attribute `j` records as an indirect use,
or when its elaboration recorded `j` as an extra use (`Lean.getExtraModUses`: notation, macros,
tactics). A module that records an extra reverse use (`Lean.isExtraRevModUse`) is kept wherever
it was reachable. Then, as `lake shake` does by default, each module checked imports exactly the
needs not implied by its other needs: it keeps the imports that are such needs, adds the rest, and
drops every other import. An import line ending in `-- shake: keep` is kept.

The modules are visited in import order, and each later module's reach is computed from the
edited imports of the earlier ones. A module reaches its whole import closure, a `module` file's
private imports included: a non-`module` file imports at the private level
(`scripts/BlueprintDeps.lean`), and a first run that followed only `public import`s proposed
adding imports that the files already reach privately and compile with.

Run it with `lake lean scripts/ImportShake.lean` (never `lake env lean`, which drops the
lakefile's options) after a full `lake build`, since it reads the built `.olean`s through
`import CombinatorialRigidity`. It is not part of the `CombinatorialRigidity` library and
`lake build` never compiles it. Environment variables:

* `IMPORT_SHAKE_OUT`: the report to write (required). Per module with a change, its removals
  and additions; then a summary.
* `IMPORT_SHAKE_ONLY`: comma-separated module-name prefixes (default `CombinatorialRigidity`). A
  non-`module` project file under one of them is minimized; any other non-`module` project file
  only gains the imports it then needs, as `lake shake --only` does.
* `IMPORT_SHAKE_FIX`: when `1`, rewrite the import lines of the files with a change: the kept
  imports in their order, then the added ones, sorted.

As for `lake shake`, the build is the check: a name that elaboration used without leaving a
trace in the `.olean` (an `example`, a `rfl`-lemma that only `dsimp` used, a namespace only
`open`ed) can make a removal wrong, and the fix is an explicit import or a `-- shake: keep`.
Written 2026-10-24 for Phase 41a's item P1 (`notes/PERFORMANCE.md` *Build critical path*).
-/

open Lean

namespace ImportShake

/-- The project's root. -/
def root : Name := `CombinatorialRigidity

/-- The bit of index `i`, for the `Nat` bitsets over module indices. -/
def bit (i : Nat) : Nat := 1 <<< i

/-- Remove the bits of `t` from `s`. -/
def diff (s t : Nat) : Nat := s ^^^ (s &&& t)

/-- The modules a module's constants and recorded uses need, as a bitset (`Lake.Shake.calcNeeds`
for one import kind). `reach` is the module's original transitive closure, which bounds the
indirect uses. -/
def calcNeeds (env : Environment) (indirect : Std.HashMap Name (Array ModuleIdx)) (reach : Nat)
    (i : Nat) : Nat := Id.run do
  let visit (e : Expr) (needs : Nat) : Nat :=
    e.foldConsts needs fun c needs => Id.run do
      if isReservedName env c then return needs
      let c := if c.isStr && c.getString!.startsWith "_simp_" then c.getPrefix else c
      let some j := env.getModuleIdxFor? c | return needs
      let mut needs := needs
      if j.toNat != i then
        needs := needs ||| bit j.toNat
        for k in indirect[c]?.getD #[] do
          if reach.testBit k.toNat then
            needs := needs ||| bit k.toNat
      return needs
  let mut needs := 0
  for ci in env.header.moduleData[i]!.constants do
    needs := visit ci.type needs
    if let some v := ci.value? (allowOpaque := true) then
      needs := visit v needs
  for use in getExtraModUses env (i : ModuleIdx) do
    if let some j := env.getModuleIdx? use.module then
      if j.toNat != i then
        needs := needs ||| bit j.toNat
  return needs

/-- The source file of a project module. -/
def sourcePath (mod : Name) : System.FilePath :=
  System.mkFilePath (mod.components.map toString) |>.addExtension "lean"

/-- The module that an `import` line imports, if the line is one. -/
def importOfLine? (line : String) : Option Name := do
  let line := line.trimAscii.toString
  guard (line.startsWith "import ")
  let rest := (line.drop 7).trimAscii.toString
  let mod := rest.takeWhile (fun c => !c.isWhitespace) |>.toString
  return mod.toName

/-- Rewrite a file's import lines: drop those in `remove`, and add `add` after the last one. -/
def rewrite (path : System.FilePath) (remove add : Array Name) : IO Unit := do
  let lines := ((← IO.FS.readFile path).splitOn "\n").toArray
  let some last := (List.range lines.size).reverse.find? (fun k => (importOfLine? lines[k]!).isSome)
    | throw <| .userError s!"{path}: no import line"
  let mut out : Array String := #[]
  for k in [0:lines.size] do
    let l := lines[k]!
    match importOfLine? l with
    | some m => if !remove.contains m || l.endsWith "-- shake: keep" then out := out.push l
    | none => out := out.push l
    if k == last then
      for m in add.qsort (·.toString < ·.toString) do
        out := out.push s!"import {m}"
  IO.FS.writeFile path ("\n".intercalate out.toList)

/-- Minimize the imports of the project's non-`module` files and write the report. -/
def run : CoreM Unit := do
  let some outPath ← IO.getEnv "IMPORT_SHAKE_OUT"
    | throwError "IMPORT_SHAKE_OUT is not set"
  let only : Array Name := ((← IO.getEnv "IMPORT_SHAKE_ONLY").getD root.toString
    |>.splitOn ",").toArray.filter (!·.isEmpty) |>.map String.toName
  let fix := (← IO.getEnv "IMPORT_SHAKE_FIX") == some "1"
  let env ← getEnv
  let mods := env.header.moduleData
  let names := env.header.moduleNames
  let n := mods.size
  let idx (m : Name) : Nat := (env.getModuleIdx? m).get!.toNat
  let indirect := indirectModUseExt.getState env
  -- `reach[j]`: the modules an importer of `j` reaches through it, `j` excluded; `orig[j]`, the
  -- same before any edit.
  let mut reach : Array Nat := Array.replicate n 0
  let mut orig : Array Nat := Array.replicate n 0
  let mut preserve := 0
  let mut report : Array String := #[]
  let mut removed := 0
  let mut added := 0
  let mut changed := 0
  for i in [0:n] do
    let mod := mods[i]!
    let name := names[i]!
    if isExtraRevModUse env (i : ModuleIdx) then preserve := preserve ||| bit i
    let reachOf (imps : Array Nat) (r : Array Nat) : Nat :=
      imps.foldl (init := 0) fun s j => s ||| bit j ||| r[j]!
    let impIdx := mod.imports.map (idx ·.module)
    let origReach := reachOf impIdx orig
    orig := orig.set! i origReach
    let isProject := root.isPrefixOf name && name != root
    if mod.isModule || !(isProject || name == root) then
      reach := reach.set! i (reachOf impIdx reach)
      continue
    -- A non-`module` project file (or the root, which only gains imports).
    let path := sourcePath name
    let src ← IO.FS.readFile path
    let keep : Array Name := (src.splitOn "\n").toArray.filterMap fun l =>
      if l.endsWith "-- shake: keep" then importOfLine? l else none
    let minimize := isProject && only.any (·.isPrefixOf name)
    let mut deps := calcNeeds env indirect origReach i ||| (preserve &&& origReach)
    for m in keep do deps := deps ||| bit (idx m)
    if !minimize then
      for j in impIdx do deps := deps ||| bit j
    else
      for j in [0:n] do
        if deps.testBit j then deps := diff deps reach[j]!
    let initIdx := idx `Init
    deps := deps ||| bit initIdx
    let mut newReach := 0
    let mut kept : Array Nat := #[]
    for j in impIdx do
      if deps.testBit j then
        newReach := newReach ||| bit j ||| reach[j]!
        kept := kept.push j
    let mut toAdd : Array Nat := #[]
    for j' in [0:n] do
      let j := n - 1 - j'
      if deps.testBit j && !newReach.testBit j then
        toAdd := toAdd.push j
        newReach := newReach ||| bit j ||| reach[j]!
    let toRemove := impIdx.filter (!kept.contains ·)
    reach := reach.set! i newReach
    if toAdd.isEmpty && toRemove.isEmpty then continue
    changed := changed + 1
    removed := removed + toRemove.size
    added := added + toAdd.size
    report := report.push s!"{path}:"
    if !toRemove.isEmpty then
      report := report.push s!"  remove {toRemove.map (names[·]!)}"
    if !toAdd.isEmpty then
      report := report.push s!"  add {toAdd.map (names[·]!)}"
    if fix then
      rewrite path (toRemove.map (names[·]!)) (toAdd.map (names[·]!))
  report := report.push
    s!"{changed} files changed, {removed} imports removed, {added} added \
      (minimized: {only}; fix: {fix})"
  IO.FS.writeFile outPath ("\n".intercalate report.toList ++ "\n")

end ImportShake

run_cmd Elab.Command.liftCoreM ImportShake.run
