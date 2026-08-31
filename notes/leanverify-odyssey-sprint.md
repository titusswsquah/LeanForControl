# Sprint plan: Lean verification of the odyssey deck

Target: `../2025h_est_claude/10-odyssey/odyssey.md` — the discrete
strong/stabilizing DARE-attraction dichotomy ("Where does the filtering
Riccati recursion land?"). The brief carries a twist the 2026a sprint
did not have: **the proof is believed to still contain holes.** The
sprint therefore interleaves two activities — Lean verification, and
paper-side proof repair under the `proof-engineering` discipline — with
an incremental-commit protocol so every repair is visible in history.

## 0. Source and build

- `odyssey.md` (1133 lines) is **generated**: `flow.sh --md` stitches
  the per-result sources `00-problem.md … 09-payoff.md` +
  `a00-facts.md … a04-subspace.md` between
  `<!-- BEGIN/END FILE -->` markers. Never edit `odyssey.md` directly —
  edit the per-result file and re-stitch. `rflow.sh` splits back.
- Results are referenced by LaTeX-style labels (`lem:structure`,
  `thm:formula`, …), embedded as `<!-- label -->` comments.
- Each result carries `<!-- verify: ... -->` blocks recording the
  authors' Gate-2 numeric checks and dependency audits. Treat these as
  *claims to test*, not evidence (2026a-audit discipline).

## 1. Scope: the deck's result graph

**Main sequence (the squeeze / GAS arc, marginal-inclusive):**

| File | Results | Role |
|---|---|---|
| 00-problem | defs, C1/C2/C2w/C3w, `eq:three-block`, `eq:dichotomy` | frame + target |
| 01-structure | `lem:structure`, `lem:structure-marg` | Σ∞ block structure, `eq:bounded`, antistable positivity, marginal extinction |
| 02-criterion | `lem:criterion-w` | C2w ⟺ Σ_a ≻ 0 |
| 03-supremal | `lem:marginal`, `lem:supremal` | upper anchor (Charybdis) |
| 04-evolution | `lem:loading`, `lem:condfilter`, `lem:jtransform` | lower-anchor engine (discrete J-transform) |
| 05-lowsqueeze | `lem:slaved-seed`, `lem:lowsqueeze` | lower anchor (Scylla), floor-free |
| 06-sufficiency | `thm:sufficiency` | C1+C2w ⇒ attraction (GAS squeeze) |
| 07-necessity | `thm:necessity` | attraction ⇒ C2w |
| 08-main | `thm:main` | the dichotomy (Part 1 strong, Part 2 stabilizing/exponential) |
| 09-payoff | `thm:payoff`, `cor:every-prior` | FIE/TVKF RGES/RGAS payoff |

**Appendix:** a00 (nine facts + two foundational imports), a01
(`app:frame`, `eq:dare-cov`, `eq:prior-pos`), a02 (`eq:comparison`,
`eq:Jrec`/`eq:Jgram`, gap engine `eq:diff-id`/`eq:gap-ric`).

**Arc 1 (closed form, C3w-bound):** a03 (`thm:formula`, `cor:attract`,
`cor:phi`, `cor:necessity`), a04 (`lem:sysinterp`). Note the DAG fact:
**as currently written, `thm:main` (08) routes through the squeeze
(06+07), not through a03/a04** — the a03 verify-comments claiming
"thm:main reads cor:necessity" are stale. Arc 1 is a parallel engine;
it is a later phase here, not on the headline's critical path.

**Foundational imports (the paper's own):** `fact:dare-strong`
(existence/uniqueness/maximality of the strong solution under C1 alone
+ the spectrum `eq:Finf-spec`/`eq:Finf-c3w`; DSGG 1986,
Lancaster–Rodman 1995) and `fact:filter-opt` (KF = MMSE +
data-processing monotonicity).

## 2. Import policy (no axioms)

The repo rule stands: no `axiom`, no `sorry` in the landed tree.
Foundational imports are carried as **hypothesis bundles**, mirroring
how the paper imports them:

- A structure `StrongSolution` (working name) packaging: Σ∞ ⪰ 0 solves
  the DARE, ρ(F∞) ≤ 1, uniqueness among such, and — only where a
  consumer genuinely reads it — the spectrum split `eq:Finf-spec`.
  Anti-cheat rule: each theorem takes the *minimal* fields it uses, so
  the bundle cannot smuggle a conclusion (the 2026a audit's
  "definition correspondence" test applies).
- `fact:filter-opt` entered only through `eq:bounded`
  (`lem:structure`-2). **Resolved (O2.3):** proved by the
  predictor-form Joseph domination against the fixed-gain Lyapunov
  recursion (`Dare/Bounded.lean`) — the MMSE import is eliminated
  from the Lean layer entirely (findings entry 1).
- Where a piece of an import is provable with existing repo machinery
  (e.g. existence of Σ∞ as a monotone Riccati limit on the C3w branch,
  `exists_ric_limit_of_bounded`), prove it and shrink the bundle.

## 3. What the repo already gives (reuse map)

| Deck object | Repo asset |
|---|---|
| `eq:cov-rec`, U, R-map, gains | `Estimation/KalmanFilter.lean`: `dre`, `dreStep`, `measM`, `kfGain`, `errF`, `innovS` (+ `measM_mul_key`, pinv-free algebra) |
| `fact:schur-decay` | `LinearSystems/Schur.lean`: `isSchurStable_iff_exists_pow_norm_le` etc. |
| `fact:psd-bounds` | mathlib (`PosSemidef`, eigenvalue bounds) + `QuadForm.lean` |
| `fact:no-decay`, `fact:gramian`, `fact:poly-growth` | `SpectralGrowth`/`SpectralDynamics`/`PolynomialSampling` + 2026a `gramian_growth` — verdicts in §8 |
| `fact:update-kernel` | close kin of `measM_mul_key`; derive |
| Detectability/stabilizability, PBH | `Detectability.lean`, `Hautus.lean` |
| Riccati convergence, stabilizing closed loop | `RiccatiConvergence.lean` (`exists_ric_limit_of_bounded`, `acl_schur_of_fixed`), `Estimation/GES.lean` |
| Frames/staircase reductions | costogo `FIESystem`, `Estimation/Reduction.lean`, `Staircase.lean` |
| Uniform exp. stability of TV systems (`fact:uniexp` ⇐) | `UniformExpStability.lean` — check coverage |

The executed inventory with verdicts is §8; the facts layer was
indeed substantially cheaper than 2026a's.

## 4. Phases

Three phases. Each work package lands as its own commit, builds green,
and ends with `#print axioms` on the new heads. Commit prefixes: the
Phase-A packages already landed carry the historic `O0`–`O2.x`
numbering; new packages use `OA`/`OB`/`OC` per phase.

- **Phase A — Foundations** (former Phases 0–2: inventory, machinery,
  frame, structure). *Largely landed.* Done: inventory + decisions
  (§8), the a02 machinery layer (`eq:comparison`, gap engine,
  `eq:Jrec`, inversion antitone, `fact:update-kernel`), the
  `DareSystem` three-block frame with `lem:criterion-w`
  (`eq:prior-pos`), `eq:A2-inv`, and `eq:bounded` (`lem:structure`-2,
  `fact:filter-opt` eliminated). **Remaining:** the `StrongSolution`
  hypothesis bundle (§2, risk R7), `lem:structure`-1/-3 (risk R3),
  `lem:structure-marg` (the Stein/no-decay extinction argument), and
  the deferred consumer-driven bits (observable-injection gramian for
  the upper anchor; `eq:dare-cov` only if a transfer layer is built).
- **Phase B — The squeeze** (former Phases 3–5: both anchors +
  assembly). Upper anchor: `lem:marginal` (risk R2 — the likeliest
  first hole), `lem:supremal`. Lower anchor: `lem:slaved-seed`,
  `lem:loading`, `lem:condfilter` (risk R1 — undeclared convergence
  import), `lem:jtransform` (risk R5), `lem:lowsqueeze`. Assembly:
  `thm:sufficiency`, `thm:necessity`, `thm:main`. Confinement gates:
  C3w must appear only in the rate/Part-2 refinement; the GAS chain
  must never read it; the "floor-free" claim is checked mechanically
  by Lean's hypothesis tracking — a selling point of this
  verification. Most of the pre-registered risk mass lives here;
  expect the hole protocol (§5) to fire in this phase.
- **Phase C — Payoff + Arc 1** (former Phases 6–7). `thm:payoff`
  (risk R4), `cor:every-prior`; then, as stretch, the closed-form arc:
  `thm:formula` by the joint induction (denominator nonsingularity +
  one Riccati step), `cor:phi`, `lem:sysinterp` (deflating-subspace
  layer — the heaviest import surface; hypothesis-bundle the
  Lancaster–Rodman complementary-deflating-subspace input). Arc 1 is
  off the headline's critical path; drop it to a follow-up sprint if
  Phases A–B consume the budget.

Vacuity guards land with their phases (2026a lesson): a witness
satisfying C1+C2+C3w, one satisfying C1+C2w¬C3w (marginal present),
and a ¬C2w one where attraction provably fails — the last is `thm:necessity`
exercised, the analogue of `badSystem`.

## 5. The hole protocol (paper-side repair)

Trigger: a Lean attempt shows a step is false, circular, or needs an
idea not on the page (Gate-1 hole) — not a mere slip that local work
closes.

1. **First hole only:** copy the deck into this repo as the working
   copy — `cp -r ../2025h_est_claude/10-odyssey odyssey-src/` — and
   **commit the pristine copy immediately, before touching any
   `*.md`** ("odyssey-src: pristine import of 10-odyssey @ <date>").
   Upstream `2025h_est_claude` is never edited by this sprint.
2. **Fix under proof-engineering:** state the hole precisely (which
   step, why it fails — with the Lean goal or counterexample that
   exposed it); numeric-check the corrected algebra *before* rewriting
   prose (`check_identity.py` harness); edit the per-result source
   file(s) in `odyssey-src/`; re-stitch `./flow.sh --md`; re-run the
   deck's own verify obligations where practical.
3. **Commit the fix** as its own commit: subject names the label and
   the defect ("odyssey-src: fix lem:marginal — uniform coercivity …"),
   body records hole → cause → repair. One hole, one commit (pristine
   copy and fixes never share a commit).
4. **Resume Lean-verifying** against the repaired statement/proof, and
   log the hole in the findings note (§7).

Lean-side commits and paper-side commits stay disjoint so the history
reads as verify → hole → fix → verify.

## 6. Pre-registered risks (attack these cruxes first)

Read before each phase; these are where the chain most likely breaks.

- **R1 (`lem:condfilter`-1).** "P_T → P∞" for the reduced
  (A₁,C₁,G₁)-filter from an *arbitrary* PSD seed is cited to
  `fact:dare-strong`, which contains **no attraction statement** — the
  convergence of the reduced Riccati is an undeclared import (it is
  the stabilizable-case instance of the very dichotomy being proved;
  classical, but someone must prove it). Candidate repo cover:
  `RiccatiConvergence` + GES track; else this is a hole to patch
  (state and prove the stabilizable+detectable attraction lemma, or
  import it explicitly as a named fact with a proof).
- **R2 (`lem:marginal`).** The uniform windowed coercivity
  `eq:marg-coercive` is derived by contradiction from a *single*
  vector with exact zeros — but negating uniformity yields a sequence
  v_T (and Ŵ_T varies with T); the written argument skips the
  compactness/uniformity step. The numeric check is strong; the prose
  proof likely is not. Expect the first hole here.
- **R3 (`lem:structure`-1 / `lem:structure-marg`).** "A kernel
  direction of Σ∞|aa stays unreflected and contributes |λ|>1 to
  spec(F∞)" is a heuristic; Lean needs an actual eigenvector/invariant
  -subspace construction from v ∈ ker(Σ∞|aa).
- **R4 (`thm:payoff`).** The converse "RGAS ⇒ covariance convergence"
  is asserted with no argument. Also `fact:uniexp` is imported as an
  iff; only ⇐ (Schur limit ⇒ UES) is consumed — prove that direction,
  don't import the iff.
- **R5 (`lem:jtransform`/`lem:lowsqueeze`).** Limit identification
  leans on "the asymptotically-autonomous recursion converges to the
  unique fixed point" for `eq:condric`/`eq:cf-rec` — needs a stated
  lemma (TV perturbation of a Stein contraction), plus the claim that
  the Σ∞-blocks satisfy both recursions.
- **R6 (deck consistency, repair-time cleanup).** Stale cross-refs:
  `cor:necessity` prose still flags the necessity direction OPEN while
  a04 proves ⊇; a03 comments claim `thm:main` consumes `cor:necessity`
  (it doesn't — 08 reads 06+07); 07-`thm:necessity` stands alone while
  a04 says it was "folded in". Reconcile in `odyssey-src` when first
  touching those files.
- **R7 (import hygiene).** `eq:Finf-spec` is load-bearing in many
  places; when bundling it as a hypothesis, record at each consumer
  which *part* is read (Schur on e₁⊕a, reflection, marginal fixed), so
  the bundle stays minimal and auditable.

## 7. Bookkeeping

- Findings accumulate in `notes/leanverify-odyssey-findings.md`
  (author-facing, action-only — the `comments-to-authors.md` pattern),
  created at first finding.
- Mapping tables and phase status go into this file as addenda
  (the `leanverify-2026a-program.md` pattern).
- End-of-sprint: adversarial self-audit of the Lean layer (the
  2026a-audit pattern), then PR body in `notes/`.

## 8. Inventory addendum — results and decisions (executed 2026-08-31, opening Phase A)

Inventory of §3, executed. Verdicts against the deck's needs:

| Deck object | Verdict | Detail |
|---|---|---|
| `fact:no-decay` | **covers** | `SpectralGrowth.lean:343 no_decay` (blueprint-tagged) |
| `fact:schur-decay` | **covers** | `Schur.lean`: `IsSchurStable.exists_pow_norm_le`, `exists_pow_mulVec_le`, iff versions |
| `fact:uniexp` (⇐) | **covers** | `UniformExpStability.lean:224 transitionProd_norm_le_of_tendsto` (F→L Schur ⇒ uniform exp bound, uniform in start time; also `revProd` variant) |
| `fact:gramian` (H = I) | **covers** | `SpectralGrowth.lean:319 gramian_growth` (quantitative: `c·T·‖v‖²`) |
| `fact:gramian` (observable-injection form) | missing | needed by `lem:marginal`; build on `PolynomialSampling.sum_sq_norm_eval_ge` |
| `fact:poly-growth` | partial | `pow_mulVec_le_poly` — exponent `n−1` not `m−1`, vector form; consumers only need "some polynomial rate", so this covers with a **recorded deviation** (sharp Jordan exponent not formalized; `thm:payoff`'s defective-case growth statement must be phrased against `n−1`) |
| `fact:schur` (complement) | mathlib | `Matrix.PosDef.fromBlocks₂₂` (PosDef.lean:566); thin ℝ/ᵀ wrapper needed |
| `fact:psd-bounds` | mathlib + `QuadForm.lean` | Löwner⇄quadForm bridge exists both directions |
| `fact:update-kernel` | derive | from `measM_mul_key`/the completed-square in `KalmanFilter.lean:165` — inverse-free route available |
| `eq:comparison` (a02-1) | **MISSING** | no Löwner monotonicity of any Riccati map anywhere in repo; build via Joseph-form gain minimization + `quadForm_le_quadForm_of_posSemidef_sub` bridge |
| Joseph form, information form | missing | `KalmanFilter.lean` is deliberately inverse-free; add a Joseph layer (info form only if a consumer truly needs it) |
| `eq:diff-id`/`eq:gap-ric` (a02-3) | missing | new; the resolvent identities at `KalmanFilter.lean:238–275` are the ingredients |
| `eq:Jrec`/`eq:Jgram` (a02-2) | missing | new; needs inversion-antitone (below) |
| Löwner inversion antitone | missing | mathlib has it only in CStar scoped-order form; prove directly in the repo's `quadForm`/`PosSemidef`-sub idiom |
| Zero-seed Riccati convergence + Schur closed loop | **covers** (control form) | `StagedFacts.lqr_convergence` (stabilizable + Qs-detectable, seed 0); `RiccatiConvergence.lean` |
| Arbitrary-seed convergence | missing | this is what the deck *proves*; not an import |
| Two-block frame + reductions | **covers** | `FIESystem`, `Staircase.lean` (staircase basis, `C2_iff_stairSig₂_posDef`), `Reduction.lean` (`redSys`, transfer theorems) |
| Three-block frame (marginal) | **MISSING** | no `n_m` anywhere; new structure needed |
| Push-through/Woodbury | partial | mathlib `add_mul_mul_inv_eq_sub` unused; repo's inverse-free resolvents preferred |

**Decisions:**

- **D1 (machinery carrier).** The a02 machinery layer is frame-free:
  state it index-generically (as executed in `Dare/Update.lean` —
  generic `ι`, not `GeneralSystem`); the frame structure comes only
  with the `DareSystem` package (landed as O2.2).
- **D2 (three-block frame).** New structure from the frame package on, index
  `Fin n₁ ⊕ (Fin nₐ ⊕ Fin n_m)` (inner sum = the `e₂` block, so
  `A₂ = A_a ⊕ A_m` reuses two-block lemmas at the outer level). The
  C3w regime is `n_m = 0`. Working name `DareSystem`; module dir
  `LeanForControl/Estimation/Dare/`.
- **D3 (comparison route).** `eq:comparison` via the Joseph form:
  define `josephForm K Σ := (1−KC)Σ(1−KC)ᵀ + K R Kᵀ`, prove
  `U(Σ) = josephForm K*(Σ) Σ ⪯ josephForm K Σ` for all `K`
  (completed square), then monotonicity by
  `U(Σ₁) ⪯ josephForm K₂* Σ₁ ⪯ josephForm K₂* Σ₂ = U(Σ₂)`.
- **D4 (R1 sharpened — pre-finding).** The conditional filter of
  `lem:condfilter` is seeded at `P₀ = 0` (the slaved seed has zero
  `e₁` block), so the needed import is **zero-seed** filtering-DRE
  convergence for the reduced (A₁,C₁,G₁) system — monotone-in-horizon
  + bounded + identification, the dual of `lqr_convergence` — NOT
  arbitrary-seed convergence. Still a hole as *written* (the deck
  cites `fact:dare-strong`, which carries no attraction statement);
  the repair is to add the zero-seed convergence claim as a stated,
  provable lemma. Goes to findings when Phase B confirms.
- **D5 (deviation register).** (i) `fact:poly-growth` exponent `n−1`
  in place of the Jordan-sharp `m−1`. (ii) `fact:uniexp` imported as
  ⇐ only. Others as they arise.

**Machinery worklist** (executed in order, each numeric-checked where
nontrivial before writing the Lean; P1.4–P1.5 deferred to consumers):
P1.1 pure-matrix layer: Schur-complement wrapper, inversion antitone,
`fact:update-kernel`, update contraction `U(Σ) ⪯ Σ`.
P1.2 Joseph form + `eq:comparison` (D3).
P1.3 gap engine: `eq:diff-id`, `eq:diff-unroll`, `eq:gap-ric`.
P1.4 observable-injection gramian (`fact:gramian` second form).
P1.5 `eq:dare-cov` similarity covariance (a01-1).

## 9. Status log

**2026-08-31 (session 1).** Landed: O1.1 update layer
(`Dare/Update.lean`: Joseph form, `eq:comparison` = `dareIter_mono`,
contraction, `fact:update-kernel`); O1.2 gap engine
(`Dare/GapEngine.lean`: `eq:diff-id`/`eq:diff-unroll`/`eq:gap-ric`,
via the gain identity `U(Σ)Cᵀ = K(Σ)R`); O1.3 inversion antitone
(`QuadForm.lean`, completed-square proof); O2.1 block-information
layer (`Dare/BlockInfo.lean`: `eq:Jrec`, block update-kernel); O2.2
the `DareSystem` frame + `lem:criterion-w` (`Dare/System.lean`:
kernel-form C1/C2/C2w, `eq:prior-pos`(a)/(b), `eq:A2-inv`). All
sorry-free, standard axioms; Gate-2 numeric checks in scratchpad
preceded each algebra block. P1.4 (observable-injection gramian) and
P1.5 (`eq:dare-cov`) deferred to their consumers (Phase B / transfer
layer) by design.

**2026-08-31 (session 1, continued).** O2.3 landed
(`Dare/Bounded.lean`): `eq:bounded` by the predictor-form Joseph
domination — `R(Σ) ⪯ (A−LC)Σ(A−LC)ᵀ + LRLᵀ + Q_w` for **every** `L`,
completed square about `L* = AΣCᵀS⁻¹` — plus the fixed-gain Lyapunov
comparison and the unrolled uniform bound `exists_dare_bound`. The
`detect_inj` transport caveat was moot: `StagedFacts.detect_inj` is
already index-generic. `fact:filter-opt` is thereby eliminated from
the Lean layer; recorded as findings entry 1
(`notes/leanverify-odyssey-findings.md`, created).

**2026-08-31 (session 2).** Phase-A remainder largely landed:
OA.1a `Dare/KernelInvariance.lean` (kernel `Aᵀ`-invariance +
`Gᵀ`-annihilation at the fixed point; `F∞ᵀ = Aᵀ` on `ker Σ∞`;
Gate-2 `check_r3.py`); OA.1b `Dare/StrongSolution.lean` (the
transport lemma real→ℂ, `mem_spectrum_transpose_iff`, and the
generic corner-kernel spectrum theorem — **risk R3 resolved**, and
the route consumes only `ρ(F∞) ≤ 1`, not `eq:Finf-spec` — findings
entry 2); OA.1c `Dare/Structure.lean` (`IsStrongSolution` bundle
with minimal fields per R7; `strong_corner_posDef` /
`strong_toBlocks_posDef`: `Σ∞|ₐₐ ≻ 0` marginal-inclusive — the
shared core of `lem:structure`-1/-marg and the lever
`thm:necessity` needs); OA.2 (corner layer: `updM_corner_posDef`,
`dareStep_corner_eq/_posDef`; `lem:structure`-3 as
`dare_corner_posDef` under C2w; `strong_corner_fixed` and
`strong_stein` — `eq:Sinf-gram` in relation form, series deferred
to Phase B).

**Phase-A remainder (next):** `lem:structure-marg`'s marginal
extinction `Σ∞|·ₘ = 0` (Stein/no-decay + the unobservable-columns
argument — the meatiest remaining piece, needed by `thm:necessity`'s
marginal case and Phase B's `lem:supremal`); the `F∞` Schur-under-C3w
bundle field lands with its first consumer. Then Phase B.

## 10. Definition-of-done

- Every deck result has a Lean counterpart by the deck's own route, or
  a recorded, justified deviation.
- `lake build` green; `#print axioms` on all heads:
  `[propext, Classical.choice, Quot.sound]`.
- Confinement verified mechanically: C3w confined to the
  exponential branch; the lower anchor floor-free; C2w entering only
  through the seed.
- Every repaired hole: one pristine-copy commit (once), one commit per
  fix, one findings entry.
