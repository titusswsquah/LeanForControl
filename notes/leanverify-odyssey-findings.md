# Odyssey deck — findings from the Lean verification

Action-only notes to the authors, accumulated as the verification
proceeds (`notes/leanverify-odyssey-sprint.md` §5/§7 protocol). Status
tags: **hole** (Gate-1 defect, deck repair required), **soft**
(argument as written doesn't close, but the claim is true and a local
repair exists), **optional** (verified simplification, no correctness
issue).

## 1. `lem:structure`-2 (`eq:bounded`) — **optional, ADOPTED**
(deck commit 51920f7): the MMSE import is eliminable, and with it a
latent filtered/predicted subtlety

The deck proves `eq:bounded` by citing `fact:filter-opt` (Kalman =
minimum-variance) to dominate `Σ_T` by a fixed-gain observer. The
Lean layer (`Dare/Bounded.lean`, `pjoseph_sub_dareStep` +
`exists_dare_bound`) shows the domination is pure matrix algebra: the
*predictor-form* Joseph completed square

`(A−LC)Σ(A−LC)ᵀ + LRLᵀ + Q_w − R(Σ) = (L−AΣCᵀS⁻¹)S(Σ)(L−AΣCᵀS⁻¹)ᵀ ⪰ 0`

holds for **every** gain `L`, so the fixed-gain Lyapunov recursion
dominates the covariance recursion step by step, with no appeal to
estimator optimality. Two benefits for the text: (i) it removes a
foundational import from a lemma that otherwise needs none; (ii) it
sidesteps the filtered-vs-predicted bookkeeping in the current prose
(the fixed-gain observer's error at `T` uses `y` only through `T−1`;
fine under `fact:filter-opt` as stated, but the reader must check
that measurability detail — the algebraic route has no such detail).
Note the *update-form* Joseph square (gains `A·K`) does **not**
suffice here when `A` is singular; the predictor form does. Worth a
sentence if the proof is rewritten.

## 2. `lem:structure`-1 / `lem:structure-marg` — **soft, REPAIRED**
(deck commit aaf4e2c): the positivity argument as written didn't
close (and needs only `ρ(F∞) ≤ 1`, not `eq:Finf-spec`)

Both proofs argue `Σ∞|ₐₐ ≻ 0` by "a kernel direction is left
unreflected and contributes `|λ| > 1`", citing the imported spectrum
`eq:Finf-spec` (Fact 1). The Lean layer
(`Dare/KernelInvariance.lean` + `Dare/StrongSolution.lean` +
`Dare/Structure.lean::strong_corner_posDef`) shows the step needs
only `ρ(F∞) ≤ 1` and closes by an elementary mechanism worth putting
on the page, since the heuristic as written is not a proof (sprint
risk R3): at the fixed point, `ker Σ∞` is `Aᵀ`-invariant and
`Gᵀ`-annihilated, and **`F∞ᵀ = Aᵀ on `ker Σ∞`** (the filter does not
act on directions it knows exactly — one line from the gain). So a
nontrivial antistable corner kernel is an `F∞ᵀ`-invariant subspace on
which `F∞ᵀ` acts as `Aₐᵀ`, handing `F∞` an eigenvalue of `Aₐ`
verbatim — against `ρ(F∞) ≤ 1`. **Patch (applied):** the heuristic
sentence in `odyssey-src/01-structure.md` (both lemmas) is replaced
by this three-step argument, thinning the reliance on the imported
Fact 1; Gate-2 record `odyssey-src/scratch/check_kernel_invariance.py`.

## 3. `lem:structure-marg`, correction kill — **soft-leaning, ADOPTED**
(deck commit d631937): matrix series convergence + spectral
factorization eliminated

The `Δ|ₘₘ = 0` step asserted "partial sums nondecreasing and bounded
above, so the series converges" — Löwner-order monotone convergence
for matrices, true but uncited and nontrivial — then factored
`Δ|ₘₘ` spectrally to run `fact:no-decay` per eigenvector. The
verified route needs neither: the Stein unroll telescopes *exactly*
in quadratic form, giving summable orbit energy outright, and a PSD
Cauchy–Schwarz floor (`QuadForm.sq_dotProduct_mulVec_le`, proved by
`discrim_le_zero`) reduces the kill to `fact:no-decay` on the single
vector `Δ|ₘₘx`. Lean: `Dare/Marginal.lean::
posSemidef_eq_zero_of_orbit_summable` + `strong_marg_correction_eq_zero`.

## 4. `lem:structure-marg`, column kill — **soft, ADOPTED**
(deck commit 45b0f6f): undeclared `NO(C,A) ⊆ stable` import removed

The `Z = Σ∞|·ₘ = 0` conclusion invoked "detectability confines
`NO(C,A)` to the stable subspace" — a standard fact absent from
`app:facts` (an undeclared import), plus invariant-subspace spectral
reasoning. The verified route: take the stabilizing injection `L`
(`A−LC` Schur), then `CZ = 0` gives the intertwining
`(A−LC)ᵏZ = ZAₘ^{-k'}` — geometric decay on the left against
`fact:no-decay` on the rows kills `Z`, using only declared facts and
with defective marginal Jordan blocks needing no special treatment.
Lean: `Dare/Marginal.lean::strong_marg_extinct`.

## 5. `lem:marginal` — **HOLE, REPAIRED** (deck commits 3e11520 +
041971b): `eq:marg-coercive` mis-shaped, uniformity argument absent

Risk R2, confirmed as a Gate-1 hole. (a) `eq:marg-coercive` windowed
a *single* `Ŵ_T` over rotations, while the unrolled `J`-sum needs
windows of *consecutive, different* increments — the displayed
inequality cannot plug into the recursion it feeds. (b) The
uniformity argument negated a uniform-in-T bound into a single
exact-zero vector with no compactness step, and `Ŵ_T` varies with T.
**Repair** (covariance-side route, Gate-2
`odyssey-src/scratch/check_marginal_route.py`): backward-transported
columns `Y_T = Σ̄_T E₂ A₂^{-T'}`; the transported quadratic is
monotone with per-step innovation decrease (Joseph square at a
rank-one gain), giving `Σ‖CY_T‖² < ∞`; `Y` rides the error map and
dies through the stabilizing injection (Schur kernel × ℓ² input);
power-boundedness of `Aₘ` closes. **Price**: the marginal
eigenvalues must be semisimple — the defective case is now
explicitly OPEN in the deck, with the qualification propagated to
`lem:supremal`, `thm:sufficiency`, `thm:main`-1, and the 00-problem
dichotomy prose (which coheres with `thm:payoff`'s pre-existing
semisimple qualification for RGAS).

## 6. `lem:marginal` proof, PD parenthetical — **soft, REPAIRED**
(same commit): "the update and `GQG'` preserve positive-definiteness"
is false when `ker A' ∩ ker G' ≠ {0}`; only the `e₂`-corner
positivity survives (the `lem:structure`-3 mechanism), which is what
the argument uses. Statement hypothesis weakened to
`Σ̄₀|₂₂ ≻ 0` accordingly.

## 7. `thm:main`-2 converse — **OPEN** (flagged in 08's verify block,
commit 041971b): "exponential ⇒ C3w" needs a marginal-gap rate
*lower* bound

The converse argues "with a marginal block, `Σ_T|mm → 0` only
polynomially, contradicting the exponential rate" — but no result on
the page provides a rate *floor* (the repaired `lem:marginal` gives
decay with no rate; the retired route's polynomial claim is gone).
Candidate repair: a gap-floor argument in the style of the repo's
`GES.exists_gap_floor_of_not_C3w`. Also the parenthetical spectral
route needs "exponential ⇒ ρ(F∞) < 1", likewise unestablished. To be
resolved when 08 enters verification.
