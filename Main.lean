/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.PebbleGame.Exec

/-!
# `lake exe pebble-game` — Phase 10 Layer 5 / Phase 11 Layer 5 CLI binary

This file is the entry point for the `lake exe pebble-game` executable
target declared in `lakefile.toml`. It reads a simple edge-list file
and prints the Laman / sparse / non-sparse classification of the
encoded finite simple graph on `Fin n` for some `n` given in the file,
together with the witness data surfaced by Phase 11 Layer 4b's
verdict-bearing `PebbleGameResult`.

The classification + witness extraction is delivered through Phase 11
Layer 4b's verdict-bearing `runPebbleGameExec` (in
`CombinatorialRigidity.PebbleGame.Exec`), which reduces through the
compiled `runPebbleGameWith`-on-`empty` body in polynomial time in
`|V| + |E|`. The same compiled body underlies the `#eval (decide …)`
worked examples in `CombinatorialRigidity/PebbleGame/Examples.lean`
and the `native_decide` tactic; see `blueprint/src/chapter/executable.tex`
*Runtime and backends* for the three-row matrix.

## Input format

One whitespace-separated edge per line. The first non-blank,
non-`#`-commented line is `n m` giving the vertex count `n` and the
edge count `m` (both base-10 non-negative integers). The next `m`
non-blank, non-`#`-commented lines each contain two whitespace-separated
integers `u v` with `0 ≤ u, v < n`. Edges with `u = v` are silently
discarded by `SimpleGraph.fromEdgeSet` (matches the simple-graph
convention); duplicate edges collapse on `Finset` insertion. Vertex
labels outside `[0, n)` are an error.

Blank lines and lines whose first non-whitespace character is `#` are
ignored anywhere in the file.

## Output

A leading verdict line on stdout — one of:

* `LAMAN` — `G` is `(2, 3)`-tight (i.e. `(2, 3)`-sparse with
  `|E| + 3 = 2|V|`).
* `SPARSE_NOT_TIGHT` — `G` is `(2, 3)`-sparse but the edge count does
  not hit the tightness bound.
* `NOT_SPARSE` — `G` violates `(2, 3)`-sparsity at some vertex subset.

followed by **witness lines** (Phase 11 Layer 5):

* On `LAMAN` / `SPARSE_NOT_TIGHT`: one `ARCS u v` line per directed
  arc `(u, v)` of the accepting partial orientation `D` returned by
  `runPebbleGameExec`, in lexicographic order on `(u, v)`. The
  `D.arcs ⊆ V × V` data is the orientation that witnesses `(2, 3)`-
  sparsity: `D.underline = G.edgeFinset` (each edge of `G` appears as
  exactly one arc) and the four pebble-game invariants of
  `Reachable k ℓ D` (cf. `PartialOrientation.Reachable`).
* On `NOT_SPARSE`: one `BLOCKING n` line giving the size of the
  blocking subset `V' ⊆ V`, followed by `n` lines of the form
  `VERTEX w`, one per `w ∈ V'`, in increasing order. The `V'` data
  satisfies `3 ≤ 2 * V'.card` and
  `2 * V'.card < (G.edgesIn ↑V').ncard + 3` (cf. the `.reject`
  constructor of `PebbleGameResult`).

Scripts that only need the trichotomy label can read the first line
and ignore the rest; the witness lines are an additive refinement of
the Phase-10-era trichotomy-only output.

Errors (malformed input, out-of-range labels, declared edge count
mismatch with the actual number of edge lines, …) are reported on
stderr with a non-zero exit status.

## Usage

```
lake exe pebble-game path/to/edge-list.txt
```

Sample input files live in `examples/*.txt`. See also
`CombinatorialRigidity/PebbleGame/Examples.lean` for the in-Lean
`#eval`-style counterpart on the same set of graphs.
-/

namespace CombinatorialRigidity.Cli

open SimpleGraph
open CombinatorialRigidity.PebbleGame

/-- Strip lines that are blank or start (after leading whitespace) with `#`.
The CLI's input format allows `# comment` lines and blank separators. -/
private def stripComments (lines : List String) : List String :=
  lines.filter fun s =>
    let t := s.trimAscii
    !t.isEmpty && !t.startsWith "#"

/-- Parse a single whitespace-separated `Nat` pair `"u v"`. Returns `none`
on malformed input (wrong token count, non-numeric tokens). -/
private def parsePair (s : String) : Option (Nat × Nat) :=
  match s.splitOn.filter (· ≠ "") with
  | [a, b] => do
      let u ← a.toNat?
      let v ← b.toNat?
      return (u, v)
  | _ => none

/-- Build a `Sym2 (Fin n)` from a pair of `Nat`s, returning `none` if
either component is out of range. -/
private def mkEdge (n u v : Nat) : Option (Sym2 (Fin n)) :=
  if hu : u < n then
    if hv : v < n then
      some s(⟨u, hu⟩, ⟨v, hv⟩)
    else none
  else none

/-- **Render the verdict from `runPebbleGameExec` to the CLI output schema.**
Pattern-matches on the Phase 11 Layer 4b `PebbleGameResult G 2 3` verdict
and emits:

* On `.accept D _ _`: the trichotomy label (`LAMAN` if the edge count
  hits the tightness bound `|E| + 3 = 2 * n`, else `SPARSE_NOT_TIGHT`)
  followed by one `ARCS u v` line per arc of `D`, in lexicographic
  order on `(u, v)`. Sorting is via `Finset.sort (· ≤ ·)` against
  `LinearOrder (Lex (Fin n × Fin n))` (the `Lex` wrapping is the
  mathlib-idiomatic way to take the lex order on a product without
  competing with the project-wide `Prod` instance set).
* On `.reject V' _ _`: the `NOT_SPARSE` label, then `BLOCKING <V'.card>`,
  then one `VERTEX w` line per `w ∈ V'`, in increasing order via
  `Finset.sort (· ≤ ·)`.

Reduces through the compiled `runPebbleGameExec` body — the same body
that drives `instDecidableIsLaman` / `#eval (decide G.IsLaman)` and the
worked examples. -/
def classify (n : Nat) (rawEdges : Array (Sym2 (Fin n))) : String := Id.run do
  let G : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (rawEdges.toList.toFinset : Finset _)
  -- Phase 11 Layer 4b: directly invoke the verdict-bearing exec wrapper.
  -- `Fact (3 < 2 * 2)` is shipped as a top-level instance in `PebbleGame/Exec.lean`.
  let verdict : PebbleGameResult G 2 3 := PartialOrientation.runPebbleGameExec G 2 3 (by omega)
  match verdict with
  | .accept D _ _ =>
      let label : String :=
        if G.edgeFinset.card + 3 = 2 * n then "LAMAN" else "SPARSE_NOT_TIGHT"
      -- Sort `D.arcs : Finset (Fin n × Fin n)` lexicographically via `Lex`.
      let sortedArcs : List (Fin n × Fin n) :=
        ((D.arcs.image toLex).sort (· ≤ ·)).map ofLex
      let arcLines : List String :=
        sortedArcs.map fun p => s!"ARCS {p.1.val} {p.2.val}"
      String.intercalate "\n" (label :: arcLines)
  | .reject V' _ _ =>
      let sortedV' : List (Fin n) := V'.sort (· ≤ ·)
      let vertexLines : List String :=
        sortedV'.map fun w => s!"VERTEX {w.val}"
      String.intercalate "\n" ("NOT_SPARSE" :: s!"BLOCKING {V'.card}" :: vertexLines)

/-- **Parse the input file and run the classifier.** Returns `Except`-style
diagnostics on malformed input; on success returns the multi-line
classification + witness string per the schema documented at the top of
the file. -/
def run (input : String) : Except String String := do
  let body := stripComments (input.splitOn "\n")
  match body with
  | [] => .error "empty input: expected a leading `n m` header line"
  | header :: rest =>
    let (n, m) ← match parsePair header with
      | some p => .ok p
      | none =>
        .error s!"malformed header: expected `n m` (vertex count, edge count); \
                  got: {header.trimAscii}"
    if rest.length ≠ m then
      .error s!"declared edge count {m} does not match {rest.length} edge lines"
    else
      let edges ← rest.toArray.mapM fun line =>
        match parsePair line with
        | none =>
          .error s!"malformed edge line: expected `u v`; got: {line.trimAscii}"
        | some (u, v) =>
          match mkEdge n u v with
          | some e => .ok e
          | none =>
            .error s!"edge label out of range (n = {n}, u = {u}, v = {v})"
      .ok (classify n edges)

end CombinatorialRigidity.Cli

/-- **CLI entry point.** Expects exactly one positional argument: a path to
an edge-list file (see file-level docstring for the format). Prints the
classification + witness on stdout and exits `0` on success; prints a
diagnostic on stderr and exits `1` on malformed input or filesystem errors. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let exists? ← System.FilePath.pathExists path
    unless exists? do
      IO.eprintln s!"pebble-game: file not found: {path}"
      return 1
    let contents ← IO.FS.readFile path
    match CombinatorialRigidity.Cli.run contents with
    | .ok result =>
      IO.println result
      return 0
    | .error msg =>
      IO.eprintln s!"pebble-game: {msg}"
      return 1
  | _ =>
    IO.eprintln "usage: pebble-game <edge-list-file>"
    IO.eprintln ""
    IO.eprintln "  Input: a leading `n m` line (vertex count, edge count),"
    IO.eprintln "  then `m` lines of two whitespace-separated `0 ≤ u, v < n`."
    IO.eprintln "  Blank lines and lines starting with `#` are ignored."
    IO.eprintln "  Output: LAMAN / SPARSE_NOT_TIGHT / NOT_SPARSE, then witness lines"
    IO.eprintln "  (ARCS u v on accept; BLOCKING <n> + VERTEX w on reject)."
    return 1
