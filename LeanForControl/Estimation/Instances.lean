import LeanForControl.Estimation.FIE
import LeanForControl.Estimation.General
import LeanForControl.Estimation.Arrival
import Architect

/-!
# Instantiability of the estimation hypotheses (vacuity guard)

A concrete `FIESystem` witness: a scalar stabilizable block with unit
noise input, and a scalar antistable block `A₂ = 2`. Its existence
certifies that the standing hypotheses of the `Estimation` track are
jointly satisfiable, so none of the track's theorems is vacuous.

A negative-direction guard (`badSystem`) follows: a system for which
C1 holds but `IsGASkf` fails, certifying that the `prop_tvkf`
equivalence carries content in the negative direction — `IsGASkf` is
refutable, and the equivalence forces `¬C2` on the witness.
-/

namespace Estimation

open Matrix LinearSystems

/-- A concrete witness: `n₁ = n₂ = m = p = 1`, `A₁ = 0`, `A₂ = 2`,
`G₁ = C₁ = 1`, unit weights and priors. -/
noncomputable def exampleSystem : FIESystem 1 1 1 1 where
  A₁ := 0
  A₁₂ := 0
  A₂ := (2 : ℝ) • 1
  G₁ := 1
  C₁ := 1
  C₂ := 0
  Qi := 1
  Ri := 1
  Sig₁ := 1
  Sig₂ := 1
  hQi := Matrix.PosDef.one
  hRi := Matrix.PosDef.one
  hSig₁ := Matrix.PosSemidef.one
  hSig₂ := Matrix.PosSemidef.one
  hStab := by
    intro μ v _ _ hGv
    -- the input matrix is the identity: it excites everything
    rw [complexify_one, Matrix.transpose_one, Matrix.one_mulVec] at hGv
    exact hGv
  hAnti := by
    show ∀ μ ∈ spectrum ℂ
      (complexify ((2:ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))), 1 ≤ ‖μ‖
    intro μ hμ
    -- extract an eigenvector: the only eigenvalue of `2•1` is `2`
    have hspec : μ ∈ spectrum ℂ
        (Matrix.toLin' (complexify ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)))) := by
      rw [Matrix.spectrum_toLin']
      exact hμ
    obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
      hspec).exists_hasEigenvector
    have hAv : complexify ((2 : ℝ) • 1) *ᵥ v = μ • v := by
      have := hv.apply_eq_smul
      rwa [Matrix.toLin'_apply] at this
    have h1 : complexify ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        = (2 : ℂ) • 1 := by
      funext i j
      simp [complexify_apply, Matrix.smul_apply, Matrix.one_apply]
      split <;> simp
    rw [h1] at hAv
    have h2 : (2 : ℂ) • v = μ • v := by
      rw [← hAv, Matrix.smul_mulVec, Matrix.one_mulVec]
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv.2 (funext hall)
    have h3 : (2 : ℂ) * v i = μ * v i := congrFun h2 i
    have h4 : μ = 2 := (mul_right_cancel₀ hi h3).symm
    rw [h4]
    norm_num

/-- A concrete witness in general coordinates: `n = m = p = 1`,
`A = 2`, `G = C = Σ₀ = 1`, unit weights. `GeneralSystem` carries no
structural hypotheses, so this certifies satisfiability of its
weight-positivity assumptions. -/
noncomputable def exampleGeneralSystem : GeneralSystem 1 1 1 where
  A := (2 : ℝ) • 1
  G := 1
  C := 1
  Sig0 := 1
  Qi := 1
  Ri := 1
  hSig0 := Matrix.PosSemidef.one
  hQi := Matrix.PosDef.one
  hRi := Matrix.PosDef.one

/-! ### The negative-direction guard

Both witnesses above satisfy C1 ∧ C2, so they exercise only the
positive direction of `prop_tvkf`. The system below is the paper's
Example-2 phenomenon in miniature: a unit-circle mode (`A = 1`) that
is uncontrollable (`G = 0`) but detectable (`C = 1`), started from the
degenerate prior `Σ₀ = 0`. The covariance iterates are identically
zero — they "converge" — while the filter error never decays
(`M(k) ≡ I`). C1 holds and GAS fails, so `prop_tvkf` *forces* `¬C2`:
the equivalence is refutable, hence not vacuous, in the negative
direction, and the covariance-converges-but-error-does-not separation
is realized inside the library. -/

/-- A detectable but non-GAS system: `A = 1` (unit-circle mode),
`G = 0` (uncontrollable), `C = 1` (detectable), `Σ₀ = 0` (degenerate
prior). -/
noncomputable def badSystem : GeneralSystem 1 1 1 where
  A := 1
  G := 0
  C := 1
  Sig0 := 0
  Qi := 1
  Ri := 1
  hSig0 := Matrix.PosSemidef.zero
  hQi := Matrix.PosDef.one
  hRi := Matrix.PosDef.one

lemma badSystem_A : badSystem.A = 1 := rfl
lemma badSystem_G : badSystem.G = 0 := rfl
lemma badSystem_C : badSystem.C = 1 := rfl

/-- The covariance iterates vanish identically: the DRE "converges". -/
lemma badSystem_dre : ∀ k, badSystem.dre k = 0
  | 0 => rfl
  | k + 1 => by
    rw [GeneralSystem.dre_succ, badSystem_dre k]
    unfold GeneralSystem.dreStep
    rw [badSystem_G]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]

/-- The filter-error transition is the identity at every horizon: the
error does not decay. -/
lemma badSystem_kfErrTrans : ∀ k, badSystem.kfErrTrans k = 1
  | 0 => rfl
  | k + 1 => by
    rw [GeneralSystem.kfErrTrans_succ, badSystem_kfErrTrans k,
      Matrix.mul_one, badSystem_dre]
    unfold GeneralSystem.errF GeneralSystem.kfGain
    rw [badSystem_A]
    simp only [Matrix.mul_zero, Matrix.zero_mul, sub_zero]

/-- C1 holds: `(A, C)` is detectable (indeed observable — `C = I`). -/
lemma badSystem_C1 : badSystem.C1 := by
  intro μ v _ _ hCv
  rwa [badSystem_C, complexify_one, Matrix.one_mulVec] at hCv

/-- GAS fails: `‖M(T)a‖ = ‖a‖` at every horizon, so no vanishing
σ-bound exists. -/
theorem badSystem_not_gas : ¬ badSystem.IsGASkf := by
  rintro ⟨σ, h0, hb⟩
  set a : Fin 1 → ℝ := fun _ => 1 with ha_def
  have ha : a ≠ 0 := fun h => one_ne_zero (congrFun h 0)
  have hapos : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hσ1 : ∀ T, (1 : ℝ) ≤ σ T := by
    intro T
    have h := hb T a
    rw [badSystem_kfErrTrans, Matrix.one_mulVec] at h
    exact le_of_mul_le_mul_right (by rwa [one_mul]) hapos
  obtain ⟨T, hT⟩ := (h0.eventually_lt_const one_pos).exists
  linarith [hσ1 T]

/-- C2 fails — forced by `prop_tvkf` rather than computed: C1 holds
and GAS fails, so the equivalence pins the blame on C2. -/
theorem badSystem_not_C2 : ¬ badSystem.C2 := fun hC2 =>
  badSystem_not_gas (badSystem.prop_tvkf.mpr ⟨badSystem_C1, hC2⟩)

end Estimation
