import LeanForControl.Estimation.Dare.Payoff
import LeanForControl.Estimation.Dare.Semisimple
import Architect

/-!
# Instantiability of the odyssey hypotheses (F4b, vacuity guard)

A concrete `DareSystem` with all three blocks nonempty — a scalar
stabilizable mode (`A₁ = 0`, `G₁ = 1`), a scalar antistable mode
(`Aₐ = 2`), a scalar marginal mode (`Aₘ = 1`) — with unit weights,
priors, and full observation. Every standing hypothesis of the odyssey
line holds at once: the frame hypotheses by construction, C1 by PBH
case analysis, C2 (hence C2w) from the identity prior, and the
semisimple marginal discharges the power bounds. The witness realizes
the whole dichotomy non-vacuously: its covariance is attracted, its
estimator is GAS, and — marginal mode present — it is **not** GES.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

/-- The three-block witness: `n₁ = na = nm = m = p = 1`,
`A₁ = 0`, `Aₐ = 2`, `Aₘ = 1`, `G₁ = C = 1`, unit weights and priors. -/
noncomputable def exampleDare : DareSystem 1 1 1 1 1 where
  A₁ := 0
  A₁₂ := 0
  Aa := (2 : ℝ) • 1
  Am := 1
  G₁ := 1
  C₁ := 1
  C₂ := Matrix.fromCols 1 1
  Q := 1
  R := 1
  Sig₁ := 1
  Sig₂ := 1
  hQ := Matrix.PosDef.one
  hR := Matrix.PosDef.one
  hSig₁ := Matrix.PosSemidef.one
  hSig₂ := Matrix.PosSemidef.one
  hStab := by
    intro μ v _ _ hGv
    rw [complexify_one, Matrix.transpose_one, Matrix.one_mulVec] at hGv
    exact hGv
  hAnti := by
    intro μ hμ
    obtain ⟨v, hv0, hAv⟩ := exists_eigenvector_of_mem_spectrum hμ
    have h1 : complexify ((2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))
        = (2 : ℂ) • 1 := by
      funext i j
      simp [complexify_apply, Matrix.smul_apply, Matrix.one_apply]
      split <;> simp
    rw [h1, Matrix.smul_mulVec, Matrix.one_mulVec] at hAv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv0 (funext hall)
    have h3 : (2 : ℂ) * v i = μ * v i := congrFun hAv i
    have h4 : μ = 2 := (mul_right_cancel₀ hi h3).symm
    rw [h4]
    norm_num
  hMarg := by
    intro μ hμ
    obtain ⟨v, hv0, hAv⟩ := exists_eigenvector_of_mem_spectrum hμ
    rw [complexify_one, Matrix.one_mulVec] at hAv
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hv0 (funext hall)
    have h3 : v i = μ * v i := congrFun hAv i
    have h4 : μ = 1 := by
      have h5 : (1 : ℂ) * v i = μ * v i := by rw [one_mul]; exact h3
      exact (mul_right_cancel₀ hi h5).symm
    rw [h4]
    norm_num

/-- **C1 holds on the witness** — the full pair is detectable (PBH by
scalar case analysis). -/
theorem exampleDare_C1 : exampleDare.C1 := by
  intro μ v hμ hAv hCv
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hμ
    linarith
  -- name the three scalar components
  set a := v (Sum.inl 0) with ha
  set b := v (Sum.inr (Sum.inl 0)) with hb
  set c := v (Sum.inr (Sum.inr 0)) with hc
  -- the three eigen-equations
  have hrow1 : (0 : ℂ) = μ * a := by
    have h := congrFun hAv (Sum.inl 0)
    simpa [DareSystem.fullA, DareSystem.A₂, exampleDare, Matrix.mulVec,
      dotProduct, Fintype.sum_sum_type, complexify_apply,
      Matrix.fromBlocks, ha] using h
  have hrow2 : 2 * b = μ * b := by
    have h := congrFun hAv (Sum.inr (Sum.inl 0))
    simpa [DareSystem.fullA, DareSystem.A₂, exampleDare, Matrix.mulVec,
      dotProduct, Fintype.sum_sum_type, complexify_apply,
      Matrix.fromBlocks, Matrix.smul_apply, Matrix.one_apply, hb]
      using h
  have hrow3 : c = μ * c := by
    have h := congrFun hAv (Sum.inr (Sum.inr 0))
    simpa [DareSystem.fullA, DareSystem.A₂, exampleDare, Matrix.mulVec,
      dotProduct, Fintype.sum_sum_type, complexify_apply,
      Matrix.fromBlocks, Matrix.one_apply, hc] using h
  -- the observation equation
  have hobs : a + b + c = 0 := by
    have h := congrFun hCv 0
    simpa [DareSystem.fullC, exampleDare, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, complexify_apply, Matrix.fromCols,
      Matrix.one_apply, ha, hb, hc, add_assoc] using h
  -- scalar logic
  have ha0 : a = 0 := by
    rcases mul_eq_zero.mp hrow1.symm with h | h
    · exact absurd h hμ0
    · exact h
  have hb0 : b = 0 := by
    by_contra hbne
    have hμ2 : μ = 2 := (mul_right_cancel₀ hbne hrow2).symm
    have hc0 : c = 0 := by
      rw [hμ2] at hrow3
      have h1 : c * (1 - 2) = 0 := by ring_nf; linear_combination hrow3
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · norm_num at h
    rw [ha0, hc0, add_zero, zero_add] at hobs
    exact hbne hobs
  have hc0 : c = 0 := by
    rw [ha0, hb0, zero_add, zero_add] at hobs
    exact hobs
  funext i
  rcases i with i | i
  · rw [Subsingleton.elim i 0]
    exact ha0
  · rcases i with i | i
    · rw [Subsingleton.elim i 0]
      exact hb0
    · rw [Subsingleton.elim i 0]
      exact hc0

/-- **C2 holds on the witness** (identity prior). -/
theorem exampleDare_C2 : exampleDare.C2 :=
  exampleDare.criterion.mpr Matrix.PosDef.one

/-- **The marginal block is semisimple** (it is the identity). -/
theorem exampleDare_semisimple : exampleDare.MargSemisimple := by
  refine ⟨1, fun _ => 1, by simp, ?_⟩
  show complexify (1 : Matrix (Fin 1) (Fin 1) ℝ) = _
  rw [complexify_one, Matrix.diagonal_one, Matrix.mul_one, inv_one,
    Matrix.mul_one]

/-- **The vacuity kill, assembled**: on the witness, every standing
hypothesis is discharged at once — the strong solution exists, the
covariance is attracted (C2w from C2), the estimator is GAS, and (the
marginal mode being present) it is **not** GES. The full dichotomy is
realized, non-vacuously, inside the library. -/
theorem exampleDare_realizes_dichotomy :
    (∃ Sinf, exampleDare.IsStrongSolution Sinf
      ∧ Tendsto (fun T => ‖exampleDare.dare T - Sinf‖) atTop (nhds 0))
    ∧ exampleDare.toFIE.IsGAS
    ∧ ¬exampleDare.toFIE.IsGES := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨Sinf, hS, hiff⟩ :=
      exampleDare.main_strong_attraction_semisimple exampleDare_C1
        exampleDare_semisimple
    exact ⟨Sinf, hS, hiff.mpr (exampleDare.C2w_of_C2 exampleDare_C2)⟩
  · exact exampleDare.payoff_dichotomy.1.mpr
      ⟨exampleDare_C1, exampleDare_C2⟩
  · intro hges
    have h := exampleDare.payoff_dichotomy.2.mp hges
    exact one_ne_zero h.2.2

/-- The witness is also **not exponentially attracted** from some C2
prior — the `thm:main`-2 converse carries content. -/
theorem exampleDare_not_exponential :
    ∃ Sinf, exampleDare.IsStrongSolution Sinf
      ∧ ¬∃ C ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ T : ℕ,
          ‖exampleDare.dareFrom
              (Sinf + DareSystem.embM 1 1 1 * (DareSystem.embM 1 1 1)ᵀ) T - Sinf‖
            ≤ C * ρ ^ T :=
  exampleDare.main_marg_not_exponential_semisimple exampleDare_C1
    ⟨0⟩ exampleDare_semisimple

end Dare
end Estimation
