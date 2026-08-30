import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Matrix.PosDef
import Architect

/-!
# Pseudoinverse of a real symmetric matrix

The `costogo` development needs the Moore–Penrose pseudoinverse only for
real symmetric (in practice positive semidefinite) matrices — the prior
penalty `‖·‖²_{Σ₀†}` — where it is cheap: diagonalize by the spectral
theorem and invert the nonzero eigenvalues. Junk-value inversion in `ℝ`
(`(0 : ℝ)⁻¹ = 0`) makes the definition uniform.

* `LinearSystems.symmPinv hP` — the pseudoinverse of a symmetric `P`.
* `symmPinv_isHermitian`, `self_mul_symmPinv_mul_self` (`P P† P = P`),
  `symmPinv_mul_self_mul_symmPinv` (`P† P P† = P†`),
  `PosSemidef.symmPinv` (positive semidefiniteness).

Further API (range identities, the quadratic-form bound `eq:rangebound` of
the C2-necessity argument) is added as the `Estimation` track consumes it.
-/

namespace LinearSystems

open Matrix

variable {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}

/-- The Moore–Penrose pseudoinverse of a real symmetric matrix, via the
spectral theorem: invert the nonzero eigenvalues in the eigenbasis. -/
noncomputable def symmPinv (hP : P.IsHermitian) : Matrix (Fin n) (Fin n) ℝ :=
  (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
    diagonal (fun i => (hP.eigenvalues i)⁻¹) *
    star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)

/-- Spectral decomposition of `P` in the `U * D * Uᴴ` form. -/
lemma isHermitian_spectral_eq (hP : P.IsHermitian) :
    P = (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      diagonal hP.eigenvalues *
      star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
  have h := hP.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa using h

lemma star_mul_self_eigenvectorUnitary (hP : P.IsHermitian) :
    star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) = 1 :=
  Unitary.coe_star_mul_self _

/-- The pseudoinverse of a symmetric matrix is symmetric. -/
lemma symmPinv_isHermitian (hP : P.IsHermitian) :
    (symmPinv hP).IsHermitian := by
  unfold symmPinv
  rw [star_eq_conjTranspose]
  exact isHermitian_mul_mul_conjTranspose _
    (isHermitian_diagonal (fun i => (hP.eigenvalues i)⁻¹))

/-- Conjugation by a matrix with `star U * U = 1` is multiplicative. -/
private lemma conj_mul (U A B : Matrix (Fin n) (Fin n) ℝ)
    (hUU : star U * U = 1) :
    (U * A * star U) * (U * B * star U) = U * (A * B) * star U := by
  have h : (U * A * star U) * (U * B * star U)
      = U * A * (star U * U) * (B * star U) := by noncomm_ring
  rw [h, hUU, mul_one]
  noncomm_ring

private lemma conj_mul₃ (U A B C : Matrix (Fin n) (Fin n) ℝ)
    (hUU : star U * U = 1) :
    (U * A * star U) * (U * B * star U) * (U * C * star U)
      = U * (A * B * C) * star U := by
  rw [conj_mul U A B hUU, conj_mul U (A * B) C hUU]

/-- `P` and `P†` commute (both are diagonal in the eigenbasis). -/
lemma self_mul_symmPinv_comm (hP : P.IsHermitian) :
    P * symmPinv hP = symmPinv hP * P := by
  have hUU := star_mul_self_eigenvectorUnitary hP
  have hdiag : diagonal hP.eigenvalues
        * diagonal (fun i => (hP.eigenvalues i)⁻¹)
      = diagonal (fun i => (hP.eigenvalues i)⁻¹)
        * diagonal hP.eigenvalues := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have h1 := conj_mul (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    (diagonal hP.eigenvalues)
    (diagonal (fun i => (hP.eigenvalues i)⁻¹)) hUU
  have h2 := conj_mul (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    (diagonal (fun i => (hP.eigenvalues i)⁻¹))
    (diagonal hP.eigenvalues) hUU
  have h3 : symmPinv hP =
      (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        diagonal (fun i => (hP.eigenvalues i)⁻¹) *
        star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := rfl
  have hspec := isHermitian_spectral_eq hP
  calc P * symmPinv hP
      = ((hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
          diagonal hP.eigenvalues *
          star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *
        ((hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
          diagonal (fun i => (hP.eigenvalues i)⁻¹) *
          star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) := by
        rw [← hspec, ← h3]
    _ = (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        (diagonal hP.eigenvalues
          * diagonal (fun i => (hP.eigenvalues i)⁻¹)) *
        star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := h1
    _ = (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        (diagonal (fun i => (hP.eigenvalues i)⁻¹)
          * diagonal hP.eigenvalues) *
        star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
        rw [hdiag]
    _ = ((hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
          diagonal (fun i => (hP.eigenvalues i)⁻¹) *
          star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) *
        ((hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
          diagonal hP.eigenvalues *
          star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)) :=
        h2.symm
    _ = symmPinv hP * P := by
        rw [← hspec, ← h3]

/-- `P P† P = P`. -/
lemma self_mul_symmPinv_mul_self (hP : P.IsHermitian) :
    P * symmPinv hP * P = P := by
  have hUU := star_mul_self_eigenvectorUnitary hP
  have hdiag : diagonal hP.eigenvalues *
      diagonal (fun i => (hP.eigenvalues i)⁻¹) * diagonal hP.eigenvalues
        = diagonal hP.eigenvalues := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    rcases eq_or_ne (hP.eigenvalues i) 0 with h | h
    · simp [h]
    · field_simp
  have h2 := conj_mul₃ (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    (diagonal hP.eigenvalues) (diagonal (fun i => (hP.eigenvalues i)⁻¹))
    (diagonal hP.eigenvalues) hUU
  rw [hdiag, ← isHermitian_spectral_eq hP] at h2
  have h3 : symmPinv hP =
      (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        diagonal (fun i => (hP.eigenvalues i)⁻¹) *
        star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [h3]
  exact h2

/-- `P† P P† = P†`. -/
lemma symmPinv_mul_self_mul_symmPinv (hP : P.IsHermitian) :
    symmPinv hP * P * symmPinv hP = symmPinv hP := by
  have hUU := star_mul_self_eigenvectorUnitary hP
  have hdiag : diagonal (fun i => (hP.eigenvalues i)⁻¹) *
      diagonal hP.eigenvalues * diagonal (fun i => (hP.eigenvalues i)⁻¹)
        = diagonal (fun i => (hP.eigenvalues i)⁻¹) := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    rcases eq_or_ne (hP.eigenvalues i) 0 with h | h
    · simp [h]
    · field_simp
  have h2 := conj_mul₃ (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
    (diagonal (fun i => (hP.eigenvalues i)⁻¹)) (diagonal hP.eigenvalues)
    (diagonal (fun i => (hP.eigenvalues i)⁻¹)) hUU
  rw [hdiag, ← isHermitian_spectral_eq hP] at h2
  have h3 : symmPinv hP =
      (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
        diagonal (fun i => (hP.eigenvalues i)⁻¹) *
        star (hP.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [h3]
  exact h2

/-- The pseudoinverse of a positive semidefinite matrix is positive
semidefinite. -/
lemma _root_.Matrix.PosSemidef.symmPinv (hP : P.PosSemidef) :
    (LinearSystems.symmPinv hP.1).PosSemidef := by
  have hev : ∀ i, 0 ≤ (hP.1.eigenvalues i)⁻¹ := fun i =>
    inv_nonneg.mpr (hP.eigenvalues_nonneg i)
  have hdiag : (diagonal (fun i => (hP.1.eigenvalues i)⁻¹)).PosSemidef :=
    posSemidef_diagonal_iff.mpr hev
  have h := hdiag.mul_mul_conjTranspose_same
    (hP.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  unfold LinearSystems.symmPinv
  rw [star_eq_conjTranspose]
  exact h

/-- **Range as kernel annihilator** (SVD-free `U₂'v = 0` criterion):
for symmetric PSD `P`, a vector lies in the range of `P` iff it is
orthogonal to the kernel of `P`. -/
lemma mem_range_iff_forall_ker {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosSemidef) (v : Fin n → ℝ) :
    (∃ z, v = P *ᵥ z) ↔ ∀ u, P *ᵥ u = 0 → u ⬝ᵥ v = 0 := by
  have hPt : Pᵀ = P := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hP.1
  constructor
  · rintro ⟨z, rfl⟩ u hu
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hPt, hu,
      zero_dotProduct]
  · intro h
    refine ⟨symmPinv hP.1 *ᵥ v, ?_⟩
    set w := v - P *ᵥ (symmPinv hP.1 *ᵥ v) with hw
    have hPP : P * (P * symmPinv hP.1) = P := by
      rw [self_mul_symmPinv_comm hP.1, ← Matrix.mul_assoc,
        self_mul_symmPinv_mul_self hP.1]
    have hker : P *ᵥ w = 0 := by
      rw [hw, Matrix.mulVec_sub, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec]
      rw [show P * P * symmPinv hP.1 = P from by
        rw [Matrix.mul_assoc]; exact hPP]
      simp
    have h1 : w ⬝ᵥ v = 0 := h w hker
    have h2 : w ⬝ᵥ (P *ᵥ (symmPinv hP.1 *ᵥ v)) = 0 := by
      rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hPt, hker,
        zero_dotProduct]
    have h3 : w ⬝ᵥ w = 0 := by
      have h4 : w ⬝ᵥ v
          = w ⬝ᵥ w + w ⬝ᵥ (P *ᵥ (symmPinv hP.1 *ᵥ v)) := by
        rw [← dotProduct_add]
        congr 1
        rw [hw]
        module
      rw [h1, h2] at h4
      linarith
    have h5 : w = 0 := dotProduct_self_eq_zero.mp h3
    have h6 : v = P *ᵥ (symmPinv hP.1 *ᵥ v) + w := by
      rw [hw]
      module
    rw [h5, add_zero] at h6
    exact h6

end LinearSystems
