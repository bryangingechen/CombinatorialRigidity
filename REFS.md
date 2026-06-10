# REFS.md — reading reference PDFs in `.refs/`

Read-on-demand reference (not session-start orientation): how to
read the project's local reference PDFs. The citation discipline
itself — when and how to cite, the verification bar — lives in the
top-level `CLAUDE.md` *Referencing prior work*.

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

For formal `\cite{}` work in the blueprint, see `blueprint/CLAUDE.md`
*Citations* and *Static checks before commit*.
