import LeanForControl.Estimation.FIE
import Architect

/-!
# Instantiability of the estimation hypotheses (vacuity guard)

A concrete `FIESystem` witness: a scalar stabilizable block with unit
noise input, and a scalar antistable block `A₂ = 2`. Its existence
certifies that the standing hypotheses of the `Estimation` track are
jointly satisfiable, so none of the track's theorems is vacuous.
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

end Estimation
