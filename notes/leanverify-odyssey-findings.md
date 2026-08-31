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
