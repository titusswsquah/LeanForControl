# Formalizing `costogo.tex` — setup notes and dependency audit

Target: `../2025h_est_claude/costogo.tex` (1284 lines) — *State estimation of
unstabilizable linear systems: the optimization perspective. Part II — the
value-function route.*

Main result (`thm:gas-ges-fi`): the full-information estimator is globally
asymptotically stable **iff** C1 ∧ C2, and globally exponentially stable
**iff** C1 ∧ C2 ∧ C3w.

This file records what the environment provides, what mathlib is missing, and a
suggested order of attack. **No mathematics is formalized yet.**

## Environment

| Piece | Version / status |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.30.0-rc2` (pinned in `lean-toolchain`) |
| mathlib | `v4.30.0-rc2` |
| `lake build` | green, 2916 jobs |
| `lake build :blueprint` | green |
| `leanblueprint web` | green — dep graph + `blueprint/lean_decls` (39 decls) |
| `lake exe checkdecls blueprint/lean_decls` | green |
| doc-gen4 (`cd docbuild && lake build LeanForControl:docs`) | see README |
| Disk | mathlib build tree is ~6.7 GB; doc-gen4 adds several more |

Blueprint Python tooling is pinned in `blueprint/requirements.txt` — read the
graphviz note there before touching it, the failure mode is silent.

## Paper structure → proof obligations

| Label | Statement | Section |
|---|---|---|
| `lem:semiPT` | Kalman filter with singular prior ↔ pseudoinverse-penalty problem | §2 |
| `lem:Sigma2-pd` | positive-definiteness of the reduced prior block | §2 |
| `lem:prelim` | finite-horizon DP solution, horizon-shift identities, uniform bounds | §3 (proof in app. C) |
| `lem:coercive` | detectability ⇒ antistable information bracket | §4 |
| `prop:infhor` | infinite-horizon limit of the reduced estimator | §5 |
| `prop:gas` | GAS ⟺ C1 ∧ C2 | §5 |
| `lem:val-rate` | exponential value convergence characterizes C3w | §6 |
| `thm:ges-fi` | GES ⟺ C1 ∧ C2 ∧ C3w | §6 |
| `thm:gas-ges-fi` | the dichotomy (assembles the two above) | §1 |

## mathlib audit

Checked against the pinned mathlib. **Available:**

- `Matrix.PosDef` / `Matrix.PosSemidef` — `Mathlib/Analysis/Matrix/PosDef.lean`
- Schur complements — `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`
- `spectralRadius` + Gelfand formula — `Mathlib/Analysis/Normed/Algebra/{Spectrum,GelfandFormula}.lean`
- Matrix order (`⪯`) — `Mathlib/Analysis/Matrix/Order.lean`
- LDL, Gram matrices, Rayleigh quotient, eigenvalue machinery
- Cayley–Hamilton / charpoly — already used by `LinearSystems/Hautus.lean`

**Not in mathlib — must be built:**

| Needed | Notes |
|---|---|
| Moore–Penrose pseudoinverse | only `nonsing_inv` exists; `Σ₀^†` is load-bearing throughout |
| Schur-stability predicate (`ρ(A) < 1`) | expressible via `spectralRadius`, but no API |
| Detectability / stabilizability | absent from mathlib **and** from this repo |
| Discrete algebraic Riccati equation, LQR | absent (`fact:lqr`) |
| Controllability/observability Gramians | absent (`fact:gramian`) |
| Jordan-block growth bound `‖Aᵏ‖ ≤ c(1+k)^{m-1}` | `fact:poly-growth` |
| Uniform exp. stability of convergent LTV systems | `fact:uniexp` (Zhou–Zhao 2017) |

The nine `\begin{fact}` environments in appendix A (`app:facts`, line 1067) are
exactly the external dependencies. Seven of the nine are *not* in mathlib.

## What this repo already gives you

`LinearSystems/Hautus.lean` is the closest existing work and is the right
template: `unobservableSubspace`, `isObservable_iff_hautus`,
`isControllable_iff_isObservable_transpose`, and the duality bridge
`controllabilityMatrix_transpose`. Detectability is the natural next definition
and should slot in beside them. Note that file works over `ℂ` (eigenvalues live
in `ℂ`) while the estimator itself is real — the paper does the same, so the
`ℝ`/`ℂ` boundary is a real design decision to make early.

## Suggested order

1. Detectability + stabilizability defs, with Hautus characterizations, reusing
   `Hautus.lean`. This is prerequisite for C1, C2, C3w and is independently
   useful to the repo.
2. Schur stability API on top of `spectralRadius`; then `fact:detect-inj`,
   `fact:no-decay`, `fact:poly-growth`, `fact:eig-orbit`.
3. Moore–Penrose pseudoinverse (or dodge it: the paper's `Σ₀ = M₁ Σ̃₀ M₁'`
   SVD form may be cheaper to carry as data than to derive).
4. `lem:prelim` — the DP induction. Biggest single chunk; appendix C has the
   full induction.
5. `lem:coercive`, then `prop:gas`, `lem:val-rate`, `thm:ges-fi`.

## Repo issues found during setup (pre-existing, on `main`)

1. **README overstates.** It claims "No `sorry`, `admit`, or `axiom`", but
   `contDiffOn_extension` (`LeanForControl/Lyapunov/Defs.lean:342`) is a
   `sorry`. It is a dead stub — nothing references it, and `#print axioms` on
   every headline theorem shows no `sorryAx`.
2. **`lake exe mk_all --check` fails (exit 1).** Ten files under
   `LeanForControl/` are not imported by the root module: `DiniCalculus`,
   `Dini/{DiniDeriv,Dinimono}`, all six `Lyapunov_old/*`, and `ODEs/scratchpad`.
   `.github/workflows/blueprint.yml` sets `mk_all-check: true`, so that
   workflow's build step should be failing on `main`. (The main CI,
   `lean_action_ci.yml`, uses lean-action defaults and does not run this check.)
   If those files are deliberately parked, exclude them rather than importing
   them — several still contain `sorry`s.
