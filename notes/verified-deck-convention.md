# The verified-deck convention

How a machine verification and a modular proof deck co-evolve when the
deck itself is a deliverable. Written generally — the odyssey sprint is
the first user, but the intent is to fold this back into the
`proof-engineering` skill as its verification-sync discipline. "Lean"
below stands for any proof assistant; "deck" for a `flow.sh`-style
modular document (per-result source files stitched into one `*.md`).

## 1. Principle: the deck states the proofs that were verified

A verification effort produces two artifacts, and only one of them is
prose someone will read later. At the end, the deck must say what was
actually proven — every load-bearing step either machine-verified as
written, repaired until it was, or explicitly carried as an import.
Two corollaries:

- **Route faithfulness runs both ways.** Verifying *someone else's*
  paper, the formalization follows the paper's routes and deviations
  are findings. Verifying *our own* deck, the deck follows the
  verified proof whenever the verified proof is better — a simpler
  argument discovered during formalization is a deck improvement, not
  a formalization artifact.
- **Findings notes are not a destination.** A findings file records
  *that* something was found and *why*; the fix itself belongs in the
  deck. A soft finding parked in a notes file is drift between what is
  written and what is proven.

## 2. Finding taxonomy → required deck action

| Class | Definition | Deck action |
|---|---|---|
| **hole** | Gate-1 defect: a load-bearing step is false, circular, or needs an idea not on the page | Repair required, immediately, own commit |
| **soft** | The claim is true and locally repairable, but the argument as written does not close (heuristic sentence, skipped compactness step, citation that doesn't carry the step) | Repair required — when found, at latest before the phase ends. The verified argument is the repair |
| **optional** | The deck's route is sound, but verification produced a simpler/cleaner route (fewer imports, no side conditions) | Per-case: **adopt** the verified route when it is simpler or removes an import; **keep** the deck's route only for genuine expository value, and then add a one-line remark naming the verified equivalent |
| **deviation** | The formalization proves a weaker-but-sufficient form (coarser constant, special case that covers all consumers) | Deck unchanged. Recorded in the sprint's deviation register; the deck's verify-comment states the verified form |
| **stale wiring** | Cross-references/comments contradicting the deck's actual dependency graph | Repair when the file is first touched for another reason — unless the fix forces an architecture decision, which is settled deliberately, not patched incidentally |

**Imported facts** (results stated without proof, carried as
hypothesis bundles in the verification) are not verification targets;
the deck does not change for them. But their status must be legible:
each fact's verify-comment says `imported` (hypothesis bundle),
`verified` (proved after all), or `verified-weakened` (deviation
class), and *which parts* consumers actually read — imports stay
minimal and auditable.

## 3. Working-copy protocol

1. The deck is copied into the verification repo as a working copy
   (`<deck>-src/`) **as soon as the first deck-affecting finding
   exists** — not lazily at the first hole. The copy's first commit is
   pristine: no edits ride along. The upstream original is never
   edited by the sprint; porting back is a deliberate end-of-sprint
   step.
2. Edit per-result **source** files only, never the stitched document;
   re-stitch (`flow.sh --md`) after every change so source and
   stitched stay in sync within each commit.
3. One finding, one commit. Subject names the label and the defect
   (`odyssey-src: fix lem:X — <defect>`); body records
   finding → cause → repair. Lean-side and deck-side commits stay
   disjoint, so history reads *verify → finding → deck fix → verify*.
4. Deck repairs pass the same gates as any proof work: the corrected
   argument is numeric-checked **before** the prose is rewritten, and
   the edited result's consumers are re-read (the deck's own
   dependency audit) — a repair that silently changes what a
   downstream result may cite is a new defect.

## 4. Traceability: `LEAN:` lines in verify-comments

Each verified result's `<!-- verify: -->` block gains one line mapping
label → declaration:

```
LEAN: lem:criterion-w = DareSystem.criterion_w
  (LeanForControl/Estimation/Dare/System.lean); axioms clean.
```

Conventions: one line per label (list multiple declarations when a
result splits); `axioms clean` means the standard axioms only, checked
by `#print axioms`; imported facts get `LEAN: imported —
<bundle/hypothesis name>` instead; deviations get `LEAN: verified as
<declaration> (<weakened form>)`. Sync commits are batched **once per
phase** (`lean-sync`), not per lemma — traceability without churn.
These lines are what make the stitched document a *verified* document
in a checkable sense: every label resolves to a declaration or to a
named import.

## 5. What never goes into the deck

Formalization noise: index-type choices, tactic idioms, constant
bookkeeping that doesn't change the mathematical statement, and
weakened-form details beyond the one-line verify-comment. The deck
stays a mathematics document; the Lean tree and the sprint notes carry
the rest.

## 6. End state (definition of done, deck side)

- Every labelled result is one of: **verified** (with `LEAN:` line),
  **imported** (hypothesis bundle, marked), or **out of scope**
  (stated in the deck's own scope note).
- No finding classed hole/soft remains unrepaired; every adopted
  optional finding is reflected in the prose; deviations are marked.
- The stitched document is regenerated and identical to the stitched
  sources.
- The findings file mirrors the deck's change history one-to-one
  (finding ↔ repair commit).

## 7. Feedback into the `proof-engineering` skill

What this convention adds beyond the skill's four gates, for eventual
upstreaming:

- **A fifth gate: verification sync.** A deck with a machine
  verification is not done until deck and verification agree — the
  taxonomy of §2 is the gate's checklist, and "soft findings must be
  repaired in the source, not parked in notes" is its refusal rule.
- The `LEAN:` traceability-line format (§4) as the standard way a deck
  records its verification state next to the authors' own numeric
  checks.
- The both-ways route-faithfulness principle (§1) — the skill
  currently assumes the proof text is the fixed point; when a verifier
  is in the loop, the *verified* proof is.
- The pristine-copy / one-finding-one-commit / re-stitch-per-commit
  protocol (§3) as the skill's repair workflow for decks under
  verification.
