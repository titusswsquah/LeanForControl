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

## 7. `thm:main`-2 converse — **HOLE (false as stated), REPAIRED &
core VERIFIED** (Phase C)

Escalated from OPEN: the per-prior converse of `eq:main-stab`
("Σ_T → Σ∞ exponentially ⇒ C3w") is **false**, not merely unproven.
Counterexample: any prior with *exactly known* marginal block
(zero marginal rows). The recursion preserves zero marginal rows
(verified: `marg_rows_stay_zero`), so the run coincides with the
marginal-free `e₁⊕a` subsystem's run and converges exponentially
despite `nm > 0`. **Repair** (deck commit "repair thm:main Part 2"):
`eq:main-stab` now reads `C1: C3w ⟺ (exponential attraction from
every C2 prior)`, with the counterexample recorded in a remark. The
repaired converse is proved by a new argument — no polynomial floor:
along the *exact* `eq:gap-ric` recursion, the transported marginal
energy `φ_T = ⟨y_T, Δ_T y_T⟩` (transport legitimate because
`Eₘᵀ F∞ = Aₘ Eₘᵀ`, the gain vanishing on the extinct marginal) loses
at most `c‖Δ_T‖φ_T` per step; assuming the `ε = 1` run exponential,
an `ε`-scaled seed keeps `φ_T ≥ ε/2` forever while comparison forces
`φ_T → 0`. **Lean**: `DareSystem.marg_not_exponential`
(`Dare/RateFloor.lean`), axioms clean. The forward rate (C3w ⇒
geometric) remains deck-level. Note: the deck's own candidate repair
(the value-level harmonic floor `exists_gap_floor_of_not_C3w`) exists
verified in the repo's arc1 layer; the new covariance-level argument
avoids needing any floor.

## 8. `lem:marginal` statement — **optional, ADOPTED** (deck commit
571c5a5): the verified proof gives strictly more than first repaired

The Lean proof (`DareSystem.marg_block_norm_tendsto`) needs **no**
hypothesis on the prior beyond PSD: no `Σ̄₀|₂₂ ≻ 0`, no comparison
step, and only *forward* power-boundedness of `Aₘ`
(`c_m = sup‖Aₘᵏ‖ < ∞`, `k ≥ 0`). Statement strengthened accordingly:
"for **any** PSD prior directly". This supersedes the weakened
hypothesis introduced by finding 6 — the corner-positivity hypothesis
is gone entirely, not weakened.

## 9. `lem:supremal` statement — **optional, ADOPTED** (deck commit
2bd7323): the supremal seed needs no block positivity

`Σ̄₀|₂₂ ≻ 0` in the statement was a stale leftover from the
pre-repair `lem:marginal`; the verified proof
(`DareSystem.supremal_tendsto`, `Dare/Supremal.lean`) runs from any
PSD `Σ̄₀ ⪰ Σ∞`. Dropped, along with the stale parenthetical at the
Marginal/cross step. `06-sufficiency` already cited the weaker form.
Note for the record: the Lean takes `eq:Finf-spec` restricted to
`e₁⊕a` as an explicit `IsSchurStable` hypothesis — the same imported
status the display has in the deck (`lem:structure`-1's spectrum
claim); if `eq:Finf-spec` is ever proven on-page, the hypothesis
discharges.

## 10. `thm:sufficiency`, upper-anchor seed — **optional, ADOPTED**
(deck commit for finding 10): `Σ̄₀ = Σ₀ + Σ∞` replaces `cI`

"Take `Σ̄₀ = cI` with `c` large enough that `cI ⪰ max(Σ∞, Σ₀)`"
leaves the existence of such a `c` unproven (standard —
`c ≥ λmax` — but off the page). The seed `Σ₀ + Σ∞` is manifestly
above both, threshold-free, and is what the Lean verifies
(`sufficiency_tendsto`). Enabled by finding 9 (`lem:supremal`
accepts any PSD seed `⪰ Σ∞`).

## Phase B scope notes (not findings)

- The one analytic import in the lower anchor is the `ReducedImport`
  bundle: the reduced-system `fact:dare-strong` (`P_T → P∞` from the
  zero seed) plus the `fact:schur-decay` closed-loop product bound —
  exactly the deck's own citations in `lem:condfilter`-1. Likewise
  `eq:Finf-spec` (restricted to `e₁⊕a`) enters `lem:supremal` /
  `thm:sufficiency` as an `IsSchurStable` hypothesis, matching its
  imported status.
- Exponential-rate qualifiers in `lem:jtransform` / `lem:lowsqueeze` /
  `thm:sufficiency`'s C3w branch are not formalized: the Lean proves
  convergence (the geometric bounds are visible in the displayed
  inequalities but no rate is extracted). Consistent with the deck,
  which claims no rate in the marginal case.
- Limit identification (`lem:jtransform`'s "coefficients match those
  at the fixed point") is implemented constructively: `Σ∞` carries its
  own conditional chart (`strong_decomp`, zero marginal loading by
  `eq:marg-extinct`), and the fixed-point identities are read off
  chart extraction (`strong_chart_fixed`) — same content as the deck's
  uniqueness prose, no uniqueness argument needed.

## 11. `thm:payoff` Part 2, RGAS half — **HOLE (misstatement),
REPAIRED** (Phase C): the error frontier is C2, not C2w

"C1+C2w ⟺ RGAS" conflated the covariance frontier with the error
frontier. An *uninformed* marginal error direction is never corrected
(the optimal gain is zero along it; it rotates undamped), so GAS
fails under C2w-only; informed (C2), the filter learns it and GAS
holds — with or without C3w, semisimple or not. This is the repo's
**verified** arc1 result (`FIESystem.isGAS_iff_C1_and_C2`,
`gas_ges_dichotomy`, and the FIE↔TVKF bridge `isGASkf_iff_isGAS`).
The deck's own wording ("undamped ripples") conceded
non-convergence under the standard σ/KL definition. Repaired:
`eq:payoff-dich` states GES ⟺ C1+C2+C3w and GAS ⟺ C1+C2, plus the
"two frontiers" remark (covariance: C2w; error: C2).

## 12. `thm:payoff` Part 2, RGAS mechanism — **soft (invalid
inference), REPAIRED** (same commit)

"F∞ power-bounded ⇒ Φ(T,k) uniformly bounded" is a non sequitur:
products of time-varying maps converging to a power-bounded limit
need not be bounded (Levinson-type conditions need summable
perturbations, unavailable without C3w). The arc1 route is
variational and never touches transition products; the proof now
cites it. The semisimple/defective distinction re-scoped: it governs
the *limit* map's powers `‖F∞^k‖` (frozen-gain ripples), not the
optimal filter's error. The GATE-2 numerics
(`check_defective_marginal.py`) measured `‖F∞^k‖` — consistent with
the re-scoped claim, silent on the filter products.

## 13. `cor:every-prior` — **soft (wrong side), REPAIRED**
(same commit)

Every-prior "RGAS ⟺ 𝒳ₐ,uc = 0" characterized the *covariance* side.
Corrected: covariance attraction for every prior ⟺ 𝒳ₐ,uc = {0};
error GAS for every prior ⟺ 𝒳u,uc = {0} ⟺ (A,G) stabilizable — and
under the universal quantifier GAS and GES *coincide* (stabilizability
already entails C3w). The interesting antistable-only characterization
survives on the covariance side.

## 14. 08's Spectrum paragraph / `eq:Finf-spec` — **soft (hand-wave),
REPAIRED & VERIFIED** (phase D)

The deck's only argument for "$F_\infty\!\mid_{e_1\oplus a}$ Schur"
was the parenthetical "the $\rho(F_\infty)\le1$ property of the
strong solution realized on each reciprocal pair by the inside
representative" — an appeal to the symplectic reciprocal pairing
that was never derived (and would drag in pencil theory). Verified
replacement, consuming only the `IsStrongSolution` bundle
($\rho\le1$) plus extinction: (i) extinction kills the marginal rows
of the gain, so $F_\infty$ is block upper-triangular for the
$(e_1\oplus a\,|\,m)$ split and the spectrum splits
(`strong_spec_split`); (ii) the compression $F_s$ is Schur by a
**one-step PBH–Stein argument** (`strong_Fs_schur`): $|\mu|>1$
embeds through the invariance $F_\infty E_s = E_s F_s$ against
$\rho\le1$; at $|\mu|=1$ one step of the predictor-Joseph fixed
point (`strong_predictor_stein`) transported along a left
quasi-eigenvector balances exactly (the rotation cancels in
$\mathrm{re}^2{+}\mathrm{im}^2$; the marginal drift is annihilated
by extinction inside the energy — no power induction), forcing
$(AL_\infty)'e = 0$, $G'e = 0$, whence PBH stabilizability kills
$e_1$, antistability kills $a$; (iii) the marginal part supplies the
unit-modulus witness (`strong_exists_unit_eigenvalue`), so
$\rho(F_\infty) = 1$ exactly. Deck repaired: `lem:structure-marg`
states the verified split (the reciprocal identification
$\Lambda_{\mathrm{in}}\sqcup\{\lambda^{-1}\}$ demoted to
`fact:dare-strong`'s pencil statement, an Arc-1 consumer), proof
paragraph added; 08's parenthetical replaced. **The `hFs` import is
discharged**: `sufficiency_tendsto` and `strong_attraction_iff_C2w`
no longer hypothesize `eq:Finf-spec` (`supremal_tendsto` keeps it as
a general-lemma hypothesis, discharged at every consumer).
GATE-2: scratch/check_spectrum_split.py (split exact, max|spec Fs| =
0.63, unit eigenvectors m-supported).

## 15. `A_c` identification — **soft (false as stated), REPAIRED**

The deck defined $A_c$ as "the $e_1$-diagonal block of $F_\infty$"
(00-problem) and 08 asserted $F_\infty$ "block upper-triangular in
the frame". Both are false: the antistable rows of $F_\infty$ couple
back into $e_1$ through the gain ($F_\infty\!\mid_{a,e_1} =
-A_aK_aC_1 \ne 0$), so $F_\infty$ is *not* $(e_1|a)$-triangular and
the $e_1$-diagonal block is not a spectral part. GATE-2 refutation
(scratch/check_Ac_identification.py): $\|F_{a,e_1}\| = 1.17$;
$\operatorname{spec}((F_\infty)_{11}) = \{0.039, 0.482^2\}$ is not
inside $\operatorname{spec}(F_\infty)$, while the reduced
$(A_1,G_1,C_1)$ stabilizing loop's spectrum $\{0.062, 0.130^2\}$ is
— exactly. The only structural triangularity is $(e_1\oplus a\,|\,m)$,
and it comes from **extinction** (the marginal gain rows vanish), not
from the frame. Repairs: $A_c$ redefined as the reduced stabilizing
loop (00-problem); 08's Spectrum paragraph states the extinction
route and flags the surviving $e_1|a$ coupling; 06's rate remark and
09's Part-1 proof cite the verified split vs. the imported reciprocal
identification correctly. The false identification was decorative
(no proof consumed it), hence soft.

## 16. `lem:sysinterp` orbit collapse — the `L⁻/L^≥` split is
eliminable (simplification, deck simplified)

The deck's kernel-identity `⊆` direction (a04) collapsed the backward
`e₁`-orbit ($a_k = A_1'a_{k+1}$, $G_1'a_k = 0$, $a_k \to 0$) by
splitting $e_1 = L^-(A_1') \oplus L^{\ge}(A_1')$, contracting the
stable component, inverting $A_1'$ on the unstable-or-critical part
($(A_1'|_{L^\ge})^{-1}$ — the one partial inverse in the file), and
invoking "inverse-related maps share invariant subspaces" plus the
stabilizability placement $NO(G_1',A_1') \subseteq L^-(A_1')$. All of
this is eliminable: since $G_1'a_{k+1} = 0$ for every $k \ge 0$, one
stabilizing output injection $L_{\mathrm{inj}}$ (from stabilizability
of $(A_1,G_1)$, i.e. detectability of the dual pair — Lean:
`detect_inj S.A₁ᵀ S.G₁ᵀ S.hStab`) rewrites the recursion as
$a_k = (A_1' - L_{\mathrm{inj}}G_1')a_{k+1}$ with a Schur matrix, and
$a_j = (A_1'-L_{\mathrm{inj}}G_1')^m a_{j+m} \to 0$ kills the orbit in
one line — no spectral splitting, no partial inverse, no
invariant-subspace transfer. Verified as `kernel_sub`
(Estimation/Dare/Subspace.lean); deck proof paragraph replaced and the
`A^{-1}`-hygiene line updated (the $(A_1'|_{L\ge})^{-1}$ entry is
retired). The deck's original argument was correct — this is a
simplification finding, not an error.
