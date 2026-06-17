# RENDERING.md — local blueprint build / preview mechanics

**Read-on-demand reference, not session-start orientation.** How to render
the blueprint locally (`inv bp` / `inv web` / `inv serve`, the `PATH`
setup, the citation ordering, the dep-graph check) — needed only when
building or previewing by hand, so extracted here from `CLAUDE.md` to keep
the per-blueprint-commit manual lean (the `../PHASE-BOUNDARIES.md` /
`../REFS.md` discipline). The per-commit gate (`blueprint/verify.sh`) and
`CLAUDE.md` *Static checks before commit* stay in `CLAUDE.md`; this is the
iterative-render how-to. One-time machine setup is in `SETUP-AND-PITFALLS.md`.

## Running builds

From `blueprint/`, with the venv activated. Make sure TeX is on `PATH`
in the current shell. `which xelatex` should print
`/Library/TeX/texbin/xelatex`; if not, run

```sh
export PATH="/Library/TeX/texbin:$PATH"
```

This is the reliable fix. **Don't rely on
`eval "$(/usr/libexec/path_helper)"`** as the only PATH update —
agent-tool Bash invocations (and some non-login shells) do not pick up
`/etc/paths.d/TeX` from path_helper, so `xelatex` stays missing even
after running it. The explicit `export PATH=…` is unconditional.

Every Bash tool call from Claude Code spawns a fresh shell, so `PATH`
does not persist across calls. Prepend the export to the same compound
command as `inv bp` / `inv web` (e.g.,
`export PATH=… && cd blueprint && source .venv/bin/activate && inv bp`),
not as a separate call.

```sh
inv bp         # latexmk drives xelatex → blueprint/print/print.pdf,
               # and copies print.bbl to src/web.bbl for plastex.
inv web        # plastex → blueprint/web/index.html + dep_graph_document.html.
               # Reads src/web.bbl produced by inv bp; if you run inv
               # web standalone with no web.bbl, every \cite{} silently
               # renders as a broken-reference fallback.
inv serve      # preview the web build at http://localhost:8000
```

Run `inv bp` before `inv web` — the order matters for citations. CI's
`leanblueprint pdf` / `leanblueprint web` flow is the same, in the
same order.

When all you want is the per-commit gate (bp + web + checkdecls,
quietly), run `blueprint/verify.sh` from any cwd — see `CLAUDE.md`
*Static checks before commit*. The standalone `inv` targets above remain the
right tool for iterative debugging (rebuild only the web pass, serve
locally, etc.).

After `inv web`, **open `blueprint/web/dep_graph_document.html`** in a
browser. This is the unique value-add over plain LaTeX: every node
should be green (formalized) for completed phases, with edges showing
the `\uses{}` dependencies. A missing or red node is the signal
something's off — a typo in `\lean{...}`, a missing `\leanok`, or a
broken `\uses{...}`.
