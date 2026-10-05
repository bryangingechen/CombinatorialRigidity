# REFS.md — citation detail and the reference PDFs in `.refs/`

Read-on-demand reference (not session-start orientation). The citation rule
itself is the top-level `CLAUDE.md` *Referencing prior work*; this file
carries its detail (the pre-commit scan, the verification bar with its
precedents, the cross-check references) and how to read the local PDFs.

## The citation scan and the verification bar

*(Moved from the top-level `CLAUDE.md` *Referencing prior work* on
2026-10-05.)*

Concretely, **proactively scan your blueprint / notes / commit-
message prose before commit** and ask, for each substantive
mathematical step:

- Whose result is this? (A named theorem, a classical lemma, a
  technique attributed in standard references.)
- Have I cited it? If "no", does this commit cite something else
  that subsumes it (e.g., the blueprint chapter's section preamble),
  or am I silently asserting the result?
- If "yes" — verify the citation per the bar below before commit.

The bar to *add* a citation is low; the bar to *leave the prose
uncited* should be high. When in doubt, cite the standard reference
and let the next reviewer judge whether it's needed.

The verification bar:

Hallucinated section pointers (e.g. *"Whiteley §3"* with no paper
specified) and mis-attributions (crediting a populariser or
surveyor instead of the original prover) are the failure modes — once
written down they propagate through future sessions and read as
authoritative.

The minimum bar:

- **Author + year resolve to a real publication.** Confirm title,
  journal/series, volume, and page range against a primary source
  (DOI landing page, publisher metadata, NASA ADS).
- **"X §N" references hold.** §N must exist in X and contain what
  you claim. A previous-session "Jordán §3.1" was actually about
  M-circuits, not the Henneberg decomposition the prose claimed —
  if you cannot quickly verify, write *"classical"* or *"see X for a
  survey"* without a section number rather than guess one.
- **Attribution names who proved the result.** A survey or textbook
  is fine as a *"presentation we follow"* pointer alongside the
  primary citation, not in place of it. *"Abstract rigidity matroid
  (Whiteley)"* was wrong — Graver 1991 introduced the concept; the
  Servatius SIAM survey explicitly says so.

Jordán 2016 (*Combinatorial Rigidity: Graphs and Matroids in the
Theory of Rigid Frameworks*, MSJ Memoirs 34) is the project's
de-facto cross-check for rigidity-theory attributions; its
bibliography resolves most papers the blueprint or notes would cite.
For **abstract matroid-theory** attributions (matroid union,
submodular/polymatroid, Edmonds partition — Phases 12–15), the
cross-check is Oxley 2011 (*Matroid Theory*, 2nd ed.); Schrijver's
*Combinatorial Optimization* (Vol. B) carries clean modern proofs.
Local PDF copies under `.refs/` (gitignored) are convenient when
present.

## Reading PDFs in `.refs/`

Reference PDFs accumulate under `.refs/` (gitignored). The standard
`Read` tool needs `pdftoppm` (poppler) to extract text; poppler is
**not** installed on this machine and `brew install poppler` has
been failing with a Ruby startup error. Use the `pypdf` library
inside the blueprint Python venv instead — it reads PDFs directly
without external system tools:

```sh
cd blueprint && source .venv/bin/activate
# pypdf is not in requirements.txt; install once per fresh venv.
pip install pypdf >/dev/null

python3 - <<'PY'
import pypdf
r = pypdf.PdfReader('/path/to/.refs/jordan-2016-msj-memoirs.pdf')
print('pages:', len(r.pages))
print(r.pages[0].extract_text()[:4000])      # title + TOC
# Or grep for keywords across the whole PDF:
for i, page in enumerate(r.pages):
    if 'Maxwell' in page.extract_text():
        print(f'page {i+1} mentions Maxwell')
PY
```

Page numbering caveat: printed pages may not start at 1, so *paper
p.N* often corresponds to *pdf page (N − offset)*. Check page 1 to
calibrate. (Jordán's printed pages start at 33, so *Jordán p.N* =
*pdf page (N − 32)*.)

For formal `\cite{}` work in the blueprint, see `blueprint/AUTHORING.md`
*Citations* (bib-entry conventions) and `blueprint/CLAUDE.md` *Static checks
before commit*.
