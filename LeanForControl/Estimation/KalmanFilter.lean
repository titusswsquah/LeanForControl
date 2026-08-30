import LeanForControl.Estimation.InfhorGeneral
import Architect

/-!
# The time-varying Kalman filter layer (`eq:dre`, `eq:Lk`, `eq:Mk`)

The discrete Riccati iteration on the error covariance, the filter
gains, and the error-transition products, for a `GeneralSystem`
(whose stored data are the *inverse* covariances `Qi = Q⁻¹`,
`Ri = R⁻¹`). Well-posedness (`Σ(k) ⪰ 0`, invertible innovation
covariance) is proven, and the measurement-update algebra needed by
the arrival-cost recursion (`lem:arrival-step`) is developed here:
everything is image-parameterized — no pseudoinverses, no matrix
square roots.
-/

namespace Estimation

open Matrix LinearSystems

namespace GeneralSystem

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-! ### Covariance data -/

/-- The process covariance `Q = Qi⁻¹`. -/
noncomputable def Qcov : Matrix (Fin m) (Fin m) ℝ := S.Qi⁻¹

/-- The measurement covariance `R = Ri⁻¹`. -/
noncomputable def Rcov : Matrix (Fin p) (Fin p) ℝ := S.Ri⁻¹

lemma Qcov_posDef : S.Qcov.PosDef := S.hQi.inv

lemma Rcov_posDef : S.Rcov.PosDef := S.hRi.inv

lemma Qi_mul_Qcov : S.Qi * S.Qcov = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    S.hQi.isUnit)

lemma Qcov_mul_Qi : S.Qcov * S.Qi = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    S.hQi.isUnit)

lemma Ri_mul_Rcov : S.Ri * S.Rcov = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    S.hRi.isUnit)

lemma Rcov_mul_Ri : S.Rcov * S.Ri = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    S.hRi.isUnit)

/-! ### One covariance step -/

variable (Sg : Matrix (Fin n) (Fin n) ℝ)

/-- The innovation covariance `S = CΣC' + R`. -/
noncomputable def innovS : Matrix (Fin p) (Fin p) ℝ :=
  S.C * Sg * S.Cᵀ + S.Rcov

/-- The measurement-update factor `M = I − ΣC'S⁻¹C`. -/
noncomputable def measM : Matrix (Fin n) (Fin n) ℝ :=
  1 - Sg * S.Cᵀ * (S.innovS Sg)⁻¹ * S.C

/-- One step of the covariance recursion (`eq:dre`):
`Σ⁺ = A(MΣ)A' + GQG'`. -/
noncomputable def dreStep : Matrix (Fin n) (Fin n) ℝ :=
  S.A * (S.measM Sg * Sg) * S.Aᵀ + S.G * S.Qcov * S.Gᵀ

/-- The prediction gain `L = AΣC'S⁻¹` (`eq:Lk`). -/
noncomputable def kfGain : Matrix (Fin n) (Fin p) ℝ :=
  S.A * Sg * S.Cᵀ * (S.innovS Sg)⁻¹

/-- The filter-error transition `F = A − LC = A·M`. -/
noncomputable def errF : Matrix (Fin n) (Fin n) ℝ :=
  S.A - S.kfGain Sg * S.C

lemma errF_eq_A_mul_measM : S.errF Sg = S.A * S.measM Sg := by
  unfold errF measM kfGain
  rw [Matrix.mul_sub, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

variable {Sg}

section PSD

/-- The innovation covariance is positive definite. -/
lemma innovS_posDef (hSg : Sg.PosSemidef) : (S.innovS Sg).PosDef := by
  unfold innovS
  have h1 : (S.C * Sg * S.Cᵀ).PosSemidef := by
    have h2 := hSg.mul_mul_conjTranspose_same S.C
    rwa [show S.Cᴴ = S.Cᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h2
  exact Matrix.PosDef.posSemidef_add h1 S.Rcov_posDef

lemma innovS_transpose (hSg : Sg.PosSemidef) :
    (S.innovS Sg)ᵀ = S.innovS Sg :=
  (S.innovS_posDef hSg).1.transpose_eq_self

lemma innovS_mul_inv (hSg : Sg.PosSemidef) :
    S.innovS Sg * (S.innovS Sg)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (S.innovS_posDef hSg).isUnit)

lemma innovS_inv_mul (hSg : Sg.PosSemidef) :
    (S.innovS Sg)⁻¹ * S.innovS Sg = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (S.innovS_posDef hSg).isUnit)

lemma innovS_inv_transpose (hSg : Sg.PosSemidef) :
    ((S.innovS Sg)⁻¹)ᵀ = (S.innovS Sg)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, S.innovS_transpose hSg]

/-- **The key measurement-update identity**
`MΣ · (1 + CᵀRiCΣ) = Σ` — it delivers both support preservation and
the image parameterization of the update, with no pseudoinverse. -/
lemma measM_mul_key (hSg : Sg.PosSemidef) :
    S.measM Sg * Sg * (1 + S.Cᵀ * S.Ri * (S.C * Sg)) = Sg := by
  have hbr : S.Ri - (S.innovS Sg)⁻¹
      - (S.innovS Sg)⁻¹ * (S.C * Sg * S.Cᵀ) * S.Ri = 0 := by
    have h1 : (1 : Matrix (Fin p) (Fin p) ℝ)
        + S.C * Sg * S.Cᵀ * S.Ri = S.innovS Sg * S.Ri := by
      unfold innovS
      rw [Matrix.add_mul, S.Rcov_mul_Ri]
      abel
    calc S.Ri - (S.innovS Sg)⁻¹
          - (S.innovS Sg)⁻¹ * (S.C * Sg * S.Cᵀ) * S.Ri
        = S.Ri - (S.innovS Sg)⁻¹
            * (1 + S.C * Sg * S.Cᵀ * S.Ri) := by
          rw [Matrix.mul_add, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
          abel
      _ = S.Ri - (S.innovS Sg)⁻¹ * (S.innovS Sg * S.Ri) := by
          rw [h1]
      _ = 0 := by
          rw [← Matrix.mul_assoc, S.innovS_inv_mul hSg, Matrix.one_mul,
            sub_self]
  have hexpand : S.measM Sg * Sg * (1 + S.Cᵀ * S.Ri * (S.C * Sg)) - Sg
      = Sg * S.Cᵀ * (S.Ri - (S.innovS Sg)⁻¹
          - (S.innovS Sg)⁻¹ * (S.C * Sg * S.Cᵀ) * S.Ri)
        * (S.C * Sg) := by
    unfold measM
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hbr, Matrix.mul_zero, Matrix.zero_mul] at hexpand
  have h2 := sub_eq_zero.mp hexpand
  exact h2

/-- The measurement update is symmetric: `MΣ = (MΣ)ᵀ`. -/
lemma measM_mul_isHermitian (hSg : Sg.PosSemidef) :
    (S.measM Sg * Sg).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
  have hSgt : Sgᵀ = Sg := hSg.1.transpose_eq_self
  unfold measM
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.transpose_sub, hSgt]
  congr 1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hSgt,
    S.innovS_inv_transpose hSg]
  simp only [Matrix.mul_assoc]

/-- The measurement update stays PSD:
`MΣ = Σ − ΣCᵀS⁻¹CΣ ⪰ 0` (by the completed-square decomposition, no
Schur complements needed). -/
lemma measM_mul_posSemidef (hSg : Sg.PosSemidef) :
    (S.measM Sg * Sg).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (S.measM_mul_isHermitian hSg) fun x => ?_
  rw [star_trivial]
  have hSgt : Sgᵀ = Sg := hSg.1.transpose_eq_self
  set r : Fin p → ℝ := S.C *ᵥ (Sg *ᵥ x) with hr
  set y : Fin p → ℝ := (S.innovS Sg)⁻¹ *ᵥ r with hy
  have hdecomp : x ⬝ᵥ ((S.measM Sg * Sg) *ᵥ x)
      = quadForm Sg (x - S.Cᵀ *ᵥ y) + quadForm S.Rcov y := by
    have h1 : x ⬝ᵥ ((S.measM Sg * Sg) *ᵥ x)
        = quadForm Sg x - r ⬝ᵥ y := by
      unfold measM quadForm
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mulVec,
        dotProduct_sub]
      congr 1
      rw [hy, hr]
      simp only [← Matrix.mulVec_mulVec]
      rw [dotProduct_mulVec_eq, hSgt, dotProduct_mulVec_eq,
        Matrix.transpose_transpose]
    have h2 : quadForm Sg (x - S.Cᵀ *ᵥ y)
        = quadForm Sg x - 2 * (r ⬝ᵥ y)
          + quadForm (S.C * Sg * S.Cᵀ) y := by
      have h3 : x - S.Cᵀ *ᵥ y = x + (-1 : ℝ) • (S.Cᵀ *ᵥ y) := by
        module
      rw [h3, quadForm_add_of_isHermitian hSg.1, quadForm_smul]
      have h4 : x ⬝ᵥ (Sg *ᵥ ((-1 : ℝ) • (S.Cᵀ *ᵥ y)))
          = -(r ⬝ᵥ y) := by
        rw [Matrix.mulVec_smul, dotProduct_smul, hr]
        have h5 : x ⬝ᵥ (Sg *ᵥ (S.Cᵀ *ᵥ y))
            = (S.C *ᵥ (Sg *ᵥ x)) ⬝ᵥ y := by
          rw [dotProduct_mulVec_eq, hSgt, dotProduct_mulVec_eq,
            Matrix.transpose_transpose]
        rw [h5]
        simp
      rw [h4]
      have h6 : quadForm Sg (S.Cᵀ *ᵥ y)
          = quadForm (S.C * Sg * S.Cᵀ) y := by
        rw [quadForm_mulVec, Matrix.transpose_transpose]
      rw [h6]
      ring
    have h7 : quadForm (S.C * Sg * S.Cᵀ) y + quadForm S.Rcov y
        = r ⬝ᵥ y := by
      have h8 : quadForm (S.C * Sg * S.Cᵀ) y + quadForm S.Rcov y
          = quadForm (S.innovS Sg) y := by
        unfold quadForm innovS
        rw [Matrix.add_mulVec, dotProduct_add]
      rw [h8]
      unfold quadForm
      have h9 : S.innovS Sg *ᵥ y = r := by
        rw [hy, Matrix.mulVec_mulVec, S.innovS_mul_inv hSg,
          Matrix.one_mulVec]
      rw [h9, dotProduct_comm]
    linarith [h1, h2, h7]
  rw [hdecomp]
  exact add_nonneg (hSg.quadForm_nonneg _)
    (S.Rcov_posDef.posSemidef.quadForm_nonneg _)

/-- The covariance step preserves positive semidefiniteness. -/
lemma dreStep_posSemidef (hSg : Sg.PosSemidef) :
    (S.dreStep Sg).PosSemidef := by
  unfold dreStep
  have h1 : (S.A * (S.measM Sg * Sg) * S.Aᵀ).PosSemidef := by
    have h2 := (S.measM_mul_posSemidef hSg).mul_mul_conjTranspose_same S.A
    rwa [show S.Aᴴ = S.Aᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h2
  have h3 : (S.G * S.Qcov * S.Gᵀ).PosSemidef := by
    have h4 := S.Qcov_posDef.posSemidef.mul_mul_conjTranspose_same S.G
    rwa [show S.Gᴴ = S.Gᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h4
  exact h1.add h3

end PSD

/-! ### The covariance iterates and the filter-error transition -/

/-- The DRE iterates from `Σ₀` (`eq:dre`). -/
noncomputable def dre : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => S.Sig0
  | k + 1 => S.dreStep (dre k)

@[simp]
lemma dre_zero : S.dre 0 = S.Sig0 := rfl

lemma dre_succ (k : ℕ) : S.dre (k + 1) = S.dreStep (S.dre k) := rfl

/-- The covariance iterates are well defined (`Σ(k) ⪰ 0`). -/
lemma dre_posSemidef : ∀ k, (S.dre k).PosSemidef
  | 0 => S.hSig0
  | k + 1 => S.dreStep_posSemidef (dre_posSemidef k)

/-- The filter-error transition products `M(k)` (`eq:Mk`):
`M(k) = (A − L(k−1)C)···(A − L(0)C)`. -/
noncomputable def kfErrTrans : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | k + 1 => S.errF (S.dre k) * kfErrTrans k

@[simp]
lemma kfErrTrans_zero : S.kfErrTrans 0 = 1 := rfl

lemma kfErrTrans_succ (k : ℕ) :
    S.kfErrTrans (k + 1) = S.errF (S.dre k) * S.kfErrTrans k := rfl

end GeneralSystem

end Estimation
