# Attack <name> — state

<!-- Rewrite this whole file from the template at the end of EVERY session;
never append to the old one. Budgets are lines of content per section
(`python3 notes/harness/check.py --state <this file>`). Overflow goes to
log.md as one line per attempt. Keep the section names exactly. -->

Sessions so far: N · last session: YYYY-MM-DD · baseline HEAD: <sha>

## Statement <!-- budget 10 -->
The statement being attacked, exactly, with every hypothesis, cited by the
consuming declaration's name. If it differs from the brief's, say what
changed and why. A hypothesis the route does not use gets a one-line
reason; "the brief says discard it" is not one.

## Current route and proof sketch <!-- budget 30 -->
The argument as it stands. Enumerate the open obligations O1, O2, … so the
count below has a referent, each with the consumer hypothesis (declaration
name) that makes it necessary; an obligation without one is a review flag.

## Where it breaks <!-- budget 10 -->
Mandatory while the lemma is open. The exact step that does not go through,
specific enough that a fresh reader could attack it tomorrow.

## Tried on this route, and what each rules out <!-- budget 10 -->
Only attempts still relevant to the current route. Older ones live in log.md.

## Next steps <!-- budget 5 -->

## Worries <!-- budget 5 -->
Things I might be wrong about, including claims inherited from the corpus.

## Signals <!-- budget 2 -->
- Sessions since "Where it breaks" last changed: N (renaming an obligation does not reset this)
- Open obligations: N (trend over the last three sessions: falling / flat / rising)
