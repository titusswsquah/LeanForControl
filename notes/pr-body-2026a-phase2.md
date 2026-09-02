# PR body: 2026a Phase 2 — route faithfulness + the Kalman-filter bridge

(For the same branch/compare link as before:
https://github.com/titusswsquah/LeanForControl/compare/main...feat/costogo-fie-stability
— this branch now carries the costogo track, 2026a Phase 1, and 2026a
Phase 2. Copy everything below the rule into the PR description, or
use it as a follow-up comment on the open PR.)

---

## 2026a Phase 2: the paper's proofs, and the literal `prop:tvkf`

Completes the program in `notes/leanverify-2026a-program.md`: every
theorem-level claim of `rawlings_quah_mueller_2026a/paper.tex` is now
machine-verified, **by the paper's own proof route** — including
`prop:modQgas`, whose revised statement (horizon limits + the
diagonal transfer `x̂(T|T) − x̂(T|∞) → 0` as explicit hypotheses, no
C1 ∧ C2) is matched literally by `isGAS_of_modQ` since the 2026-09-02
alignment; see the audit note (`notes/leanverify-2026a-audit.md`, A1,
closed by alignment). The headline `prop:tvkf` is
verified as the paper's literal sentence about the time-varying
Kalman filter:

```lean
theorem prop_tvkf : S.IsGASkf ↔ S.C1 ∧ S.C2
```

with `IsGASkf` the σ-form `def:GAS` on the filter error
`ê(k) = M(k)ê(0)` (KL form: `prop_tvkf_kl`).

### Stage 2a — route faithfulness (audit table cleared, F1–F6)

- **F1**: C2-free `gCost_gap` (`eq:gap`) by direct completion of
  squares; `it:zlim` by the paper's Cauchy argument run on the general
  problem (`truncation_gap`, `exists_gap_energy_bound`).
- **F2**: `lem:unibounded` feasibility via the invariant `U₂/E₂`
  independence argument (`antiFeasMat_surjective`,
  `exists_antiFeas_rightInverse`).
- **F3**: `it:xTT` via the active IOSS summation
  (`terminal_sq_bound_of_ioss` on `exists_ioss_lyapunov`).
- **F4**: C2-necessity by the `eq:iosssum` chain (IOSS-Lyapunov sum
  bound, `eq:rhs-bound`/`eq:lhs-bound`, quantitative Gramian growth,
  Cesàro contradiction).
- **F6**: `value_isLeast` — the optimization problem is primary; the
  Riccati construction is a witness.

### Stage 2b — the Kalman-filter bridge

- **`Estimation/KalmanFilter.lean`**: DRE layer — `innovS` (PD),
  `measM`, `dreStep`, `kfGain`, `errF = A − L(k)C`, the `dre`
  recursion with PSD preservation, transition `kfErrTrans` (= `M(k)`).
  All algebra pseudoinverse-free and square-root-free; the key
  identity is `MΣ(1 + CᵀR⁻¹CΣ) = Σ`.
- **`Estimation/Arrival.lean`**: the arrival-cost recursion
  (`lem:arrival` of the gas-lyap draft), image-parameterized: at every
  horizon the terminally constrained FIE problem is feasible exactly on
  the affine set `arrC(T) + im Σ(T)`, with least cost
  `arrV(T) + ‖z‖²_{Σ(T)}`; centers propagate by the KF error
  transition and curvatures by the DRE.
- **`lem:semiPT`** (the paper's one unproven lemma), nominal-error
  form: `semiPT_error : optTerm a T = M(T)a`, via `value_eq_arrV`
  (innovations decomposition) + PSD-kernel forcing. Bonus:
  `value_succ_innovation` (`V⁰_{T+1} = V⁰_T + ‖CM(T)a‖²_{S(T)⁻¹}`).
- **F5**: the KL/σ uniformization column trick on `M(k)` itself
  (`isGASkf_of_pointwise`).

### Guarantees

- Full `lake build` green, zero sorries.
- `#print axioms` on `arrival`, `value_eq_arrV`, `semiPT_error`,
  `value_succ_innovation`, `prop_tvkf`, `prop_tvkf_kl`:
  `[propext, Classical.choice, Quot.sound]` only.
- Findings for the authors (8, incl. the `eq:cc` C1-leak fix and the
  `def:modQ` hidden convergence hypothesis) recorded in
  `notes/leanverify-2026a-program.md`, with Phase 2 notes (pinv-free
  `lem:arrival` worth absorbing into the text; finding 5 closed).

🤖 Generated with [Claude Code](https://claude.com/claude-code)

https://claude.ai/code/session_01GL917HdRfpxs8t3bsTdS1N
