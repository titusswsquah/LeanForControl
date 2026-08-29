import LeanForControl.LinearSystems.QuadForm
import LeanForControl.LinearSystems.SymmPinv
import Architect

/-!
# Constrained PSD quadratic minimization

The workhorse behind every "outer" optimization in the `costogo`
development: the objective `‖ξ - a‖²_{Σ†} + ‖ξ‖²_W` (both weights merely
positive **semi**definite) attains its minimum over the affine feasible
set `ξ ∈ a + range Σ`, by solvability of the stationarity system for
bounded-below quadratics (`Matrix.PosSemidef.exists_mulVec_eq`) and an
exact completion-of-squares gap. The `Estimation` track instantiates it
with `Σ = Σ₁`, `W = P_∞` for the block-1 infinite-horizon problem.
-/

namespace LinearSystems

open Matrix

variable {k : ℕ}

/-- The prior energy of an image point: `(Wz)'W†(Wz) = z'Wz`. -/
theorem quadForm_symmPinv_image {W : Matrix (Fin k) (Fin k) ℝ}
    (hW : W.PosSemidef) (z : Fin k → ℝ) :
    quadForm (symmPinv hW.1) (W *ᵥ z) = quadForm W z := by
  have hWt : Wᵀ = W := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hW.1
  rw [quadForm_mulVec, hWt, self_mul_symmPinv_mul_self hW.1]

/-- **Constrained PSD quadratic minimization**: the objective
`‖ξ-a‖²_{Σ†} + ‖ξ‖²_W` attains its minimum over `ξ ∈ a + range Σ`. -/
theorem exists_min_quadForm_over_range
    {Sm W : Matrix (Fin k) (Fin k) ℝ}
    (hS : Sm.PosSemidef) (hW : W.PosSemidef) (a : Fin k → ℝ) :
    ∃ ξ : Fin k → ℝ, (∃ z, ξ - a = Sm *ᵥ z) ∧
      ∀ ξ' : Fin k → ℝ, (∃ z, ξ' - a = Sm *ᵥ z) →
        quadForm (symmPinv hS.1) (ξ - a) + quadForm W ξ
          ≤ quadForm (symmPinv hS.1) (ξ' - a) + quadForm W ξ' := by
  classical
  have hSt : Smᵀ = Sm := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hS.1
  have hWt : Wᵀ = W := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hW.1
  set L := Sm + Smᵀ * W * Sm with hL
  set sv : Fin k → ℝ := Smᵀ *ᵥ (W *ᵥ a) with hsv
  have hLpsd : L.PosSemidef := by
    refine hS.add ?_
    have h := hW.mul_mul_conjTranspose_same Smᵀ
    rwa [show (Smᵀ)ᴴ = Sm from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]] at h
  have hLt : Lᵀ = L := by
    rw [← conjTranspose_eq_transpose_of_trivial]; exact hLpsd.1
  -- the objective along the parameterization `ξ = a + Σ v`
  have hψ : ∀ v, quadForm (symmPinv hS.1) ((a + Sm *ᵥ v) - a)
        + quadForm W (a + Sm *ᵥ v)
      = quadForm L v + 2 * (sv ⬝ᵥ v) + quadForm W a := by
    intro v
    rw [add_sub_cancel_left, quadForm_symmPinv_image hS,
      quadForm_add_of_isHermitian hW.1, quadForm_mulVec]
    have hcross : a ⬝ᵥ (W *ᵥ (Sm *ᵥ v)) = sv ⬝ᵥ v := by
      rw [Matrix.mulVec_mulVec, dotProduct_mulVec_eq, Matrix.transpose_mul,
        hsv, ← Matrix.mulVec_mulVec, hWt]
    rw [hcross, hL, quadForm_add_matrix]
    ring
  -- bounded below ⟹ the stationarity system is solvable
  have hbdd : ∀ v, 2 * ((-sv) ⬝ᵥ v) ≤ quadForm L v + quadForm W a := by
    intro v
    have h1 : 0 ≤ quadForm (symmPinv hS.1) ((a + Sm *ᵥ v) - a)
        + quadForm W (a + Sm *ᵥ v) :=
      add_nonneg (hS.symmPinv.quadForm_nonneg _) (hW.quadForm_nonneg _)
    rw [hψ v] at h1
    have h2 : (-sv) ⬝ᵥ v = -(sv ⬝ᵥ v) := by simp
    rw [h2]
    linarith
  obtain ⟨v, hv⟩ := hLpsd.exists_mulVec_eq hbdd
  refine ⟨a + Sm *ᵥ v, ⟨v, by rw [add_sub_cancel_left]⟩, ?_⟩
  rintro ξ' ⟨z, hz⟩
  -- the competitor is `a + Σ z`; compare through the parameterization
  have hξ' : ξ' = a + Sm *ᵥ z := by
    have h := hz
    linear_combination (norm := abel) h
  rw [hξ', hψ v, hψ z]
  -- completion of squares: the gap is exactly `quadForm L (z - v) ≥ 0`
  have hgap : quadForm L z + 2 * (sv ⬝ᵥ z)
      = quadForm L v + 2 * (sv ⬝ᵥ v) + quadForm L (z - v) := by
    have hdecomp : z = v + (z - v) := by abel
    conv_lhs => rw [hdecomp]
    rw [quadForm_add_of_isHermitian hLpsd.1, dotProduct_add]
    have hcross : v ⬝ᵥ (L *ᵥ (z - v)) = -(sv ⬝ᵥ (z - v)) := by
      rw [dotProduct_mulVec_eq, hLt, hv]
      simp [dotProduct]
    rw [hcross, dotProduct_sub]
    ring
  have hnn : 0 ≤ quadForm L (z - v) := hLpsd.quadForm_nonneg _
  linarith

end LinearSystems
