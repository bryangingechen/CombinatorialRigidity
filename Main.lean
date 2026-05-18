/-
Copyright (c) 2026 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import CombinatorialRigidity.PebbleGame.Exec

/-!
# `lake exe pebble-game` — Phase 10 Layer 5 CLI binary

This file is the entry point for the `lake exe pebble-game` executable
target declared in `lakefile.toml`. It reads a simple edge-list file
and prints the Laman / sparse / non-sparse classification of the
encoded finite simple graph on `Fin n` for some `n` given in the file.

The classification is delivered through Phase 10 Layer 3's
`SimpleGraph.instDecidableIsLaman` and `SimpleGraph.instDecidableIsSparse`
(both in `CombinatorialRigidity.PebbleGame.Exec`), which reduce
through the compiled `runPebbleGameExec` body in polynomial time in
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

Exactly one of these tokens on stdout, followed by a newline:

* `LAMAN` — `G` is `(2, 3)`-tight (i.e. `(2, 3)`-sparse with
  `|E| = 2|V| − 3`).
* `SPARSE_NOT_TIGHT` — `G` is `(2, 3)`-sparse but the edge count does
  not hit the tightness bound.
* `NOT_SPARSE` — `G` violates `(2, 3)`-sparsity at some vertex subset.

Errors (malformed input, out-of-range labels, declared edge count
mismatch with the actual number of edge lines, …) are reported on
stderr with a non-zero exit status.

## Usage

```
lake exe pebble-game path/to/edge-list.txt
```

A sample input file lives in `examples/k4-minus-e.txt`. See also
`CombinatorialRigidity/PebbleGame/Examples.lean` for the in-Lean
`#eval`-style counterpart on the same set of graphs.
-/

namespace CombinatorialRigidity.Cli

open SimpleGraph

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

/-- **Classify a graph by Phase 10's `Decidable` instances.** Builds a
`SimpleGraph (Fin n)` from a list of edges and consults
`instDecidableIsLaman` then `instDecidableIsSparse` to produce one of
`LAMAN` / `SPARSE_NOT_TIGHT` / `NOT_SPARSE`. The classification reduces
through the compiled `runPebbleGameExec` body of
`CombinatorialRigidity.PebbleGame.Exec`. -/
def classify (n : Nat) (rawEdges : Array (Sym2 (Fin n))) : String :=
  let G : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet (rawEdges.toList.toFinset : Finset _)
  if decide G.IsLaman then "LAMAN"
  else if decide (G.IsSparse 2 3) then "SPARSE_NOT_TIGHT"
  else "NOT_SPARSE"

/-- **Parse the input file and run the classifier.** Returns `Except`-style
diagnostics on malformed input; on success returns the classification
string. -/
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
classification on stdout and exits `0` on success; prints a diagnostic on
stderr and exits `1` on malformed input or filesystem errors. -/
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
    IO.eprintln "  Output: LAMAN / SPARSE_NOT_TIGHT / NOT_SPARSE."
    return 1
