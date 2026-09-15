Review attack $ARGUMENTS. You are a fresh reader who has not worked on
this lemma; your job is to check, not to continue the work.

**Read** `HARNESS.md` *Evidence*, then `notes/attacks/$ARGUMENTS/brief.md`,
`state.md` and `log.md`, and `git log --follow -- notes/attacks/$ARGUMENTS/state.md`.
Open other files only when a check below needs them.

**Check, adversarially:**
1. *Signals.* Do the two signal lines agree with the state file's git
   history — sessions since "Where it breaks" last changed, and the trend
   of the open-obligation count? Three unchanged sessions is a stuck route;
   a flat or rising count is a treadmill, however many lines moved.
2. *Honesty.* Is "Where it breaks" specific enough that you could attack it
   tomorrow? Does each session shrink the obligation list, or mint a
   successor of equal difficulty?
3. *Evidence.* For each claim the sketch rests on: proved at its owning
   section, or measured on a named population with caps? Any `PROVED` tag
   consumed without the proof being read? Any figure quoted without its
   cap or its semicontinuity direction?
4. *Premature kills.* Any `log.md` entry whose stated reason the current
   state contradicts? Name what could be revived, and why.
5. *Shape.* Was there a session of sweeps with no change to the sketch?
6. *Reach.* Does the route still discharge the statement the brief's
   consumer takes, or has it drifted to a neighbour?

**Report to the PI in at most one page:** a verdict — continue, switch to a
named route, or stop — the evidence for it, and at most three concrete
next moves. Commit nothing; edit nothing; if `HARNESS.md` or the attack
command cost the attack time, add one line to `notes/harness/incidents.md`
and say so.
