# Adversarial audit: the 2026a Lean verification

Independent audit of the `rawlings_quah_mueller_2026a/paper.tex`
formalization on `feat/costogo-fie-stability` @ `6d72e18`, against
`paper.tex` @ `0223cd2`. Read-only: no library code was changed.

Brief: *verify the Lean definitions aren't cheats, and that the*
***proofs*** *— not merely the statements — get there by the paper's
own routes.* Examples (`sec:examples`, `ex_4.m`, `ex_4.py`) were
excluded by the brief. The Lyapunov and ODE tracks are out of scope.

Everything below was re-derived from the sources. Claims in
`leanverify-2026a-program.md` and `pr-body-2026a-phase2.md` were
treated as hypotheses to test, not as evidence.

## Verdict

**The definitions are not cheats, and the proof routes are the
paper's.** One material finding (A1), three minor ones (A2–A4).

## 1. Build and axiom integrity

`lake build` exits 0 (2963 jobs). `#print axioms` was run on 19
declarations chosen to cover the whole new surface — every one returns
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`:

`arrival`, `value_eq_arrV`, `semiPT_error`, `value_succ_innovation`,
`prop_tvkf`, `prop_tvkf_kl`, `isGASkf_of_pointwise`,
`isGASkf_iff_isGAS`, `optTerm_eq_arrC`, `gCost_gap`, `truncation_gap`,
`exists_gap_energy_bound`, `value_isLeast`, `C2_of_isGAS`,
`C1_of_isGAS`, `exists_ioss_lyapunov`, `terminal_sq_bound_of_ioss`,
`sum_sq_bound_of_ioss`, `dre_posSemidef`.

Sorry sweep over *built* modules (`.olean` → source) yields exactly two
hits: `Lyapunov/Defs.lean:342` (pre-existing, Lyapunov track, provably
outside the 2026a dependency cone — the axiom checks above are clean)
and `LinearSystems/StagedFacts.lean:14`, which is prose inside a
docstring, not a term. No `axiom`, `unsafe`, `native_decide`,
`opaque`, or `@[implemented_by]` anywhere. No `Classical.choose` in
any definition.

## 2. Definition correspondence

| Paper | Lean | Status |
|---|---|---|
| `eq:dre` | `dreStep` = `A(MΣ)A' + GQG'`, `M = I − ΣC'S⁻¹C` | literal |
| `eq:Lk` | `kfGain` = `AΣC'S⁻¹` | literal |
| `eq:epssys` | `errF` = `A − LC` | literal |
| `eq:Mk` | `kfErrTrans` (`M(0)=I`, `M(k+1)=F(k)M(k)`) | literal |
| `eq:nommeas` | `nominalY x₀ k = C A^k x₀` | literal |
| ℙ_T (`lem:semiPT`) | `chiTraj`/`chiResid`/`chiCost`/`ChiFeasible` | literal, in the paper's variables |
| `U₂'(χ(0)−x̄₀)=0` | `ChiFeasible` + `chiFeasible_iff_ker` | proven equivalent, SVD-free |
| ℙ_T in error coords | `glq`: `B=−G`, `Qs=C'R⁻¹C`, `Ru=Q⁻¹` | matches, up to the documented global ½ |
| `def:GAS` (KF error) | `IsGASkf` on `kfErrTrans T *ᵥ a` | stated on `M(k)`, not on the optimizer |

Two structural points that would have been the easy places to cheat,
and were not taken:

- **`IsGASkf` is defined on the DRE-side transition `M(k)`**, not on
  `optTerm`. The bridge `isGASkf_iff_isGAS` is then a theorem, and it
  routes through `semiPT_error`.
- **`semiPT_error : optTerm a T = M(T) *ᵥ a` is unconditional** — no
  C1, no C2, no definiteness hypothesis. That is the correct shape for
  `lem:semiPT`, and it is the paper's one previously unproven lemma.

## 3. Route faithfulness

Traced, not assumed:

- **C2 necessity (F4)** runs the paper's chain in order:
  `sum_sq_bound_of_ioss` (`eq:iosssum`) → the `hrhs` block
  (`eq:rhs-bound`, splitting the optimal cost into prior + stage
  costs) → `gramian_growth` (`eq:gramian`) → Cesàro contradiction.
  The pinning identity and the Cauchy–Schwarz step are present as
  written.
- **The IOSS Lyapunov function is constructed, not assumed.**
  `exists_ioss_lyapunov` goes detectability → output injection
  (`detect_inj`) → Schur `F = A − LC` → `P = Σ_k (Fᵀ)^k … F^k`, and
  delivers exactly `eq:iioss-bounds`/`eq:iioss-dec`. The hypotheses of
  `terminal_sq_bound_of_ioss` and `sum_sq_bound_of_ioss` are precisely
  what it emits, so neither summation lemma is vacuous.
- **`gramian_growth` assumes `1 ≤ ‖μ‖`, not `1 < ‖μ‖`.** Unit-circle
  modes are included. This is load-bearing: it is exactly the
  Callier–Winkin separation the paper claims as new, and a strict
  inequality here would have silently hollowed out the result.
- **`value_isLeast` (F6)** states the value as the least cost over
  feasible pairs, so the Riccati recursion is a construction witness
  and appears in no statement. This is a genuine structural anti-cheat.
- **`optInitLim`/`optCtrlLim` use `limUnder`** (junk value if
  divergent), *not* `Classical.choose` applied to a convergence proof.
  So `tendsto_optInit`/`tendsto_optCtrl` had to be earned under C2.
- **`prop_infhor` splits hypotheses exactly as the paper does**:
  `it:zlim` and `it:Vlim` under C2 alone, `it:xTT` adds C1.
- **`gCost_gap` (F1)** is C2-free — hypothesis `hfeas` only.
- **`arrival`** is an `IsLeast` plus an exact feasibility
  characterization, unconditional; `optTerm_eq_arrC` then forces
  `Σ(T)z* = 0` by PSD-kernel reasoning rather than assuming it.

## 4. Independent non-vacuity test

Both existing vacuity guards (`exampleSystem`, `exampleGeneralSystem`)
satisfy C1 ∧ C2, so neither shows the equivalence has teeth in the
negative direction. Nothing in the repo ruled out `IsGASkf` being
trivially true.

The following was written against the library and compiles sorry-free
(axioms `[propext, Classical.choice, Quot.sound]`). It is the paper's
Example-2 phenomenon in miniature: `A=1` (unit-circle mode), `G=0`
(uncontrollable), `C=1` (detectable), `Σ₀=0`.

```lean
noncomputable def bad : GeneralSystem 1 1 1 where
  A := 1;  G := 0;  C := 1;  Sig0 := 0;  Qi := 1;  Ri := 1
  hSig0 := Matrix.PosSemidef.zero
  hQi := Matrix.PosDef.one
  hRi := Matrix.PosDef.one

lemma bad_dre : ∀ k, bad.dre k = 0            -- covariance ≡ 0
lemma bad_M   : ∀ k, bad.kfErrTrans k = 1     -- M(k) ≡ I
lemma bad_C1  : bad.C1                        -- detectable
theorem bad_not_gas : ¬ bad.IsGASkf           -- ‖M(T)a‖ = ‖a‖, never decays

theorem bad_not_C2 : ¬ bad.C2 := fun hC2 =>
  bad_not_gas (bad.prop_tvkf.mpr ⟨bad_C1, hC2⟩)
```

`Σ(k) ≡ 0` was derived from the DRE and `M(k) ≡ I` from `errF`, both
independently of `prop_tvkf`; C1 holds; so `prop_tvkf` *forces* `¬C2`.
This establishes that `IsGASkf` is refutable (not trivially true), that
the equivalence carries content in the negative direction, and that the
definitions reproduce the covariance-converges-but-error-does-not
separation the paper claims is new.

Worth promoting into the library as a permanent guard beside
`Estimation/Instances.lean`; left out here to keep the audit read-only.

## Audit findings

### A1. `prop:modQgas` is not verified as the paper states it

`QFunction.lean::isGAS_of_modQ` narrows the paper's proposition four
ways. Only two are disclosed in the program note:

| Narrowing | Disclosed |
|---|---|
| Assumes `hC1 : S.C1` and `hC2 : S.C2` | **no** |
| `hdec` requires the decrease at *all* `j`; `eq:QunsDecrease` restricts to `0 ≤ j ≤ k−1` | **no** |
| Horizon limits `Q(j|∞)` must exist | yes — finding 8 |
| Quadratic bounds rather than general K∞ | yes — finding 4 |

Both C1 and C2 are load-bearing, via `S.tendsto_traj hC2` and
`S.tendsto_optTerm_sub_limTraj hC1 hC2`. The paper's `prop:modQgas`
carries no hypotheses beyond admitting a modified Q-function.

This does **not** break the headline. `prop_tvkf_optimizer` supplies
C1 ∧ C2 at the call site, `exists_modQ` proves the unrestricted
decrease for the constructed Q, and there is no circularity —
`InfhorGeneral` is imported by `QFunction`, and neither `tendsto_traj`
nor `tendsto_optTerm_sub_limTraj` depends on `isGAS_of_modQ`.

What it does affect is the coverage claim. Both
`pr-body-2026a-phase2.md` and the opening line of
`comments-to-authors.md` say *every* theorem-level claim is
machine-verified "by the paper's own proof routes"; for
`prop:modQgas` that is an overstatement, and both should be softened.

**Recommended action.** `comments-to-authors.md` item 3 (= program-note
finding 8) is the authors-facing version of this, and it currently
proposes patching `def:modQ`/`prop:modQgas` with a convergence clause
only. Widen it: as written, `prop:modQgas` *also* silently imports
C1 ∧ C2 through its appeal to `prop:infhor`, which is stated under
exactly those conditions, and its decrease inequality is used at
indices `eq:QunsDecrease` does not cover. The hypotheses need
restating, not just a convergence clause added.

### A2. `README.md:14` overclaims

> `lake build` green is the source of truth. No `sorry`, `admit`, or
> `axiom`.

The built library contains one `sorry` (`Lyapunov/Defs.lean:342`).
`pr-body-costogo-fie-stability.md` states this correctly; the README
does not. Carried over unfixed from the costogo-track audit.

### A3. Dead code from the pre-F4 route

`GeneralNecessity.lean:299::exists_red_window_growth` occurs exactly
once in the tree — its own definition. It is the superseded
window-coercivity shortcut, left behind when F4 replaced it with the
`eq:iosssum` chain. (`Coercive.lean::exists_window_value_growth` is
*not* dead: it still serves costogo's `Necessity.lean:382`.)

### A4. KL form is a hand-rolled product

`prop_tvkf_kl` uses `β(r,k) = α(k)·r` with `α` antitone and `α → 0`,
but does not require `α > 0`; strictly, `β(·,k)` is not a K∞ function
when `α(k) = 0`. Harmless — any such `α` can be bumped by a positive
null sequence — and the program note already records that mathlib has
no K∞/KL classes. Worth a footnote if `def:GAS` fidelity is ever
challenged.

## Program-note findings re-verified

Checked against `paper.tex` rather than taken on trust:

- **Finding 1 is real.** `lem:unibounded` is stated under C2 alone but
  its deferred proof invokes `eq:cc`, whose hypotheses include a
  detectability condition. The Lean `exists_value_bound_C2` correctly
  requires C2 only, so the formalization proves the paper's
  *statement*, and the suggested fix (restate `eq:cc` for an arbitrary
  stabilizing feedback) is sound — an upper bound never needs the
  LQR-optimal gain.
- **Finding 8 is real**, and A1 above extends it.
- **Finding 4 is endorsed by the paper itself**: `prop:tvkfQuns`
  explicitly permits the K∞-functions to be taken quadratic, so the
  quadratic specialization is faithful *there*. It is only in
  `prop:modQgas`, which quantifies over an arbitrary modified
  Q-function, that the narrowing bites.

## Coverage

All ten labelled results in `paper.tex` have Lean counterparts; there
are none after `prop:infhor`.

| Paper | Lean | Note |
|---|---|---|
| `prop:tvkf` | `prop_tvkf`, `prop_tvkf_kl` | literal KF sentence |
| `lem:semiPT` | `semiPT_error` | unconditional |
| `lem:exist` | `value_isLeast` + `optimal_init_unique`/`optimal_pair_unique` | hypothesis-free |
| `lem:unibounded` | `exists_value_bound_C2` | C2-only (finding 1) |
| `def:modQ` | hypotheses of `exists_modQ`/`isGAS_of_modQ` | see A1 |
| `prop:modQgas` | `isGAS_of_modQ` | **narrowed — see A1** |
| `def:classicalGAS` | `isGAS_of_pointwise` | pointwise → uniform |
| `def:GAS` | `IsGASkf`, `prop_tvkf_kl` | KL as product form (A4) |
| `prop:tvkfQuns` | `exists_modQ` | C1 ∧ C2, quadratic |
| `prop:infhor` | `prop_infhor_zlim`/`_xTT`/`_Vlim` | paper's hypothesis split |

## Not covered by this audit

- `sec:examples` and the numerical scripts (excluded by the brief).
- The Lyapunov and ODE tracks.
- Whether `costogo.tex` has been patched for the `prop:gas` defect
  reported in the earlier costogo-track audit.

## Remediation (applied after the audit; the sections above are the
frozen audit-time record)

- **A1**: coverage claims softened in `pr-body-2026a-phase2.md` and
  the opening of `comments-to-authors.md`; item 3 widened to all
  three hidden hypotheses (horizon limits, C1 ∧ C2, index range).
- **A2**: `README.md` corrected — it now discloses the one parked
  Lyapunov-track `sorry`.
- **A3**: `exists_red_window_growth` deleted; with it
  `Coercive.lean::exists_window_ric_growth`, whose only consumer it
  was. The `GeneralNecessity.lean` module docstring now describes the
  live `eq:iosssum` route.
- **A4**: footnote added to the program note (decision D5).
- **§4 guard promoted**: the audit's `bad` system now lives in
  `Estimation/Instances.lean` as `badSystem`, with
  `badSystem_dre`/`badSystem_kfErrTrans`/`badSystem_C1`/
  `badSystem_not_gas`/`badSystem_not_C2`; `#print axioms` on all five
  reports `[propext, Classical.choice, Quot.sound]`.
