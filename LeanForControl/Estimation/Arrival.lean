import LeanForControl.Estimation.KalmanFilter
import Architect

/-!
# The arrival-cost recursion and `lem:semiPT`

The support-constrained arrival cost of the full-information problem
(`lem:arrival` of the gas-lyap draft): at every horizon the terminally
constrained problem is feasible exactly on an affine set centered at
the Kalman-filter error iterate with the DRE covariance, and its value
is the accumulated innovation cost plus the covariance-weighted
displacement — all image-parameterized, with no pseudoinverses. The
corollaries are `lem:semiPT` in nominal-error form
(`e*(T|T) = M(T)a`), the innovations decomposition of the value, and
`prop:tvkf` restated for the Kalman filter.
-/

namespace Estimation

open Matrix LinearSystems

namespace GeneralSystem

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-! ### The arrival objects -/

/-- Costs of feasible decisions steering the error to `ξ` at `T`. -/
def arrSet (a : Fin n → ℝ) (T : ℕ) (ξ : Fin n → ℝ) : Set ℝ :=
  {c | ∃ e₀ ω, S.Feasible a e₀ ∧ S.glq.traj e₀ ω T = ξ
    ∧ c = S.gCost a e₀ ω T}

/-- The arrival center: the Kalman-filter error iterate. -/
noncomputable def arrC (a : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => a
  | T + 1 => S.errF (S.dre T) *ᵥ arrC a T

/-- The accumulated innovation cost. -/
noncomputable def arrV (a : Fin n → ℝ) : ℕ → ℝ
  | 0 => 0
  | T + 1 => arrV a T
      + quadForm (S.innovS (S.dre T))⁻¹ (S.C *ᵥ S.arrC a T)

@[simp] lemma arrC_zero (a : Fin n → ℝ) : S.arrC a 0 = a := rfl

lemma arrC_succ (a : Fin n → ℝ) (T : ℕ) :
    S.arrC a (T + 1) = S.errF (S.dre T) *ᵥ S.arrC a T := rfl

@[simp] lemma arrV_zero (a : Fin n → ℝ) : S.arrV a 0 = 0 := rfl

lemma arrV_succ (a : Fin n → ℝ) (T : ℕ) :
    S.arrV a (T + 1) = S.arrV a T
      + quadForm (S.innovS (S.dre T))⁻¹ (S.C *ᵥ S.arrC a T) := rfl

/-! ### The one-step pushforward -/

section OneStep

variable {Sg : Matrix (Fin n) (Fin n) ℝ}

/-- The successor covariance splits the quadratic blockwise. -/
lemma quadForm_dreStep (w : Fin n → ℝ) :
    quadForm (S.dreStep Sg) w
      = quadForm (S.measM Sg * Sg) (S.Aᵀ *ᵥ w)
        + quadForm S.Qcov (S.Gᵀ *ᵥ w) := by
  have h1 : quadForm (S.measM Sg * Sg) (S.Aᵀ *ᵥ w)
      = quadForm (S.A * (S.measM Sg * Sg) * S.Aᵀ) w := by
    rw [quadForm_mulVec, Matrix.transpose_transpose]
  have h2 : quadForm S.Qcov (S.Gᵀ *ᵥ w)
      = quadForm (S.G * S.Qcov * S.Gᵀ) w := by
    rw [quadForm_mulVec, Matrix.transpose_transpose]
  rw [h1, h2]
  unfold dreStep quadForm
  rw [Matrix.add_mulVec, dotProduct_add]

/-- `Qi`-energy of a `Qcov`-image. -/
lemma quadForm_Qi_Qcov (x : Fin m → ℝ) :
    quadForm S.Qi (S.Qcov *ᵥ x) = quadForm S.Qcov x := by
  rw [quadForm_mulVec]
  congr 1
  rw [show S.Qcovᵀ = S.Qcov from S.Qcov_posDef.1.transpose_eq_self,
    Matrix.mul_assoc, S.Qi_mul_Qcov, Matrix.mul_one]

/-- **Pushforward lower bound** (completion of squares with the
explicit multiplier): any decomposition of a successor displacement
costs at least its `Σ⁺`-energy. -/
lemma pushforward_lower (hSg : Sg.PosSemidef) (v : Fin n → ℝ)
    (ω : Fin m → ℝ) (w : Fin n → ℝ)
    (hcon : S.A *ᵥ ((S.measM Sg * Sg) *ᵥ v) - S.G *ᵥ ω
      = S.dreStep Sg *ᵥ w) :
    quadForm (S.dreStep Sg) w
      ≤ quadForm (S.measM Sg * Sg) v + quadForm S.Qi ω := by
  have hMH := S.measM_mul_isHermitian hSg
  -- the completed squares
  have h1 : quadForm (S.measM Sg * Sg) (v - S.Aᵀ *ᵥ w)
      = quadForm (S.measM Sg * Sg) v
        - 2 * (v ⬝ᵥ ((S.measM Sg * Sg) *ᵥ (S.Aᵀ *ᵥ w)))
        + quadForm (S.measM Sg * Sg) (S.Aᵀ *ᵥ w) := by
    have h2 : v - S.Aᵀ *ᵥ w = v + (-1 : ℝ) • (S.Aᵀ *ᵥ w) := by module
    rw [h2, quadForm_add_of_isHermitian hMH, quadForm_smul]
    have h3 : v ⬝ᵥ ((S.measM Sg * Sg) *ᵥ ((-1 : ℝ) • (S.Aᵀ *ᵥ w)))
        = -(v ⬝ᵥ ((S.measM Sg * Sg) *ᵥ (S.Aᵀ *ᵥ w))) := by
      rw [Matrix.mulVec_smul, dotProduct_smul]
      simp
    rw [h3]
    ring
  have h4 : quadForm S.Qi (ω + S.Qcov *ᵥ (S.Gᵀ *ᵥ w))
      = quadForm S.Qi ω + 2 * (ω ⬝ᵥ (S.Gᵀ *ᵥ w))
        + quadForm S.Qcov (S.Gᵀ *ᵥ w) := by
    rw [quadForm_add_of_isHermitian S.hQi.1]
    have h5 : ω ⬝ᵥ (S.Qi *ᵥ (S.Qcov *ᵥ (S.Gᵀ *ᵥ w)))
        = ω ⬝ᵥ (S.Gᵀ *ᵥ w) := by
      rw [Matrix.mulVec_mulVec, S.Qi_mul_Qcov, Matrix.one_mulVec]
    rw [h5, S.quadForm_Qi_Qcov]
  -- cross terms recombine into the constraint pairing
  have h6 : v ⬝ᵥ ((S.measM Sg * Sg) *ᵥ (S.Aᵀ *ᵥ w))
      = w ⬝ᵥ (S.A *ᵥ ((S.measM Sg * Sg) *ᵥ v)) := by
    rw [dotProduct_mulVec_eq, hMH.transpose_eq_self,
      dotProduct_mulVec_eq, Matrix.transpose_transpose,
      dotProduct_comm]
  have h7 : ω ⬝ᵥ (S.Gᵀ *ᵥ w) = w ⬝ᵥ (S.G *ᵥ ω) := by
    rw [dotProduct_mulVec_eq, Matrix.transpose_transpose,
      dotProduct_comm]
  -- nonnegativity of the completed squares
  have h8 : 0 ≤ quadForm (S.measM Sg * Sg) (v - S.Aᵀ *ᵥ w) :=
    (S.measM_mul_posSemidef hSg).quadForm_nonneg _
  have h9 : 0 ≤ quadForm S.Qi (ω + S.Qcov *ᵥ (S.Gᵀ *ᵥ w)) :=
    S.hQi.posSemidef.quadForm_nonneg _
  -- the pairing with the constraint
  have h10 : w ⬝ᵥ (S.A *ᵥ ((S.measM Sg * Sg) *ᵥ v))
      - w ⬝ᵥ (S.G *ᵥ ω) = quadForm (S.dreStep Sg) w := by
    rw [← dotProduct_sub, hcon]
    rfl
  have h11 := S.quadForm_dreStep (Sg := Sg) w
  rw [h6] at h1
  rw [h7] at h4
  linarith

/-- **Pushforward image**: successor displacements land in the range of
the successor covariance. -/
lemma pushforward_mem_range (hSg : Sg.PosSemidef) (v : Fin n → ℝ)
    (ω : Fin m → ℝ) :
    ∃ w, S.A *ᵥ ((S.measM Sg * Sg) *ᵥ v) - S.G *ᵥ ω
      = S.dreStep Sg *ᵥ w := by
  have h1 := mem_range_iff_forall_ker (S.dreStep_posSemidef hSg)
    (S.A *ᵥ ((S.measM Sg * Sg) *ᵥ v) - S.G *ᵥ ω)
  rw [h1]
  intro q hq
  -- a kernel vector of `Σ⁺` kills both blocks
  have h2 : quadForm (S.dreStep Sg) q = 0 := by
    unfold quadForm
    rw [hq, dotProduct_zero]
  rw [S.quadForm_dreStep] at h2
  have h3 : (0:ℝ) ≤ quadForm (S.measM Sg * Sg) (S.Aᵀ *ᵥ q) :=
    (S.measM_mul_posSemidef hSg).quadForm_nonneg _
  have h4 : (0:ℝ) ≤ quadForm S.Qcov (S.Gᵀ *ᵥ q) :=
    S.Qcov_posDef.posSemidef.quadForm_nonneg _
  have h5 : quadForm (S.measM Sg * Sg) (S.Aᵀ *ᵥ q) = 0 := by
    linarith
  have h6 : quadForm S.Qcov (S.Gᵀ *ᵥ q) = 0 := by
    linarith
  have h7 := (S.measM_mul_posSemidef
    hSg).mulVec_eq_zero_of_quadForm_eq_zero h5
  have h8 : S.Gᵀ *ᵥ q = 0 := by
    by_contra hne
    exact absurd h6 (ne_of_gt (S.Qcov_posDef.quadForm_pos hne))
  rw [dotProduct_sub]
  have h9 : q ⬝ᵥ (S.A *ᵥ ((S.measM Sg * Sg) *ᵥ v)) = 0 := by
    rw [dotProduct_mulVec_eq]
    rw [dotProduct_mulVec_eq,
      (S.measM_mul_isHermitian hSg).transpose_eq_self, h7,
      zero_dotProduct]
  have h10 : q ⬝ᵥ (S.G *ᵥ ω) = 0 := by
    rw [dotProduct_mulVec_eq, h8, zero_dotProduct]
  rw [h9, h10, sub_zero]

end OneStep

/-! ### One-step helpers -/

section StepHelpers

variable {Sg : Matrix (Fin n) (Fin n) ℝ}

/-- The update coordinate of a supported point. -/
noncomputable def updCoord (Sg : Matrix (Fin n) (Fin n) ℝ)
    (z e : Fin n → ℝ) : Fin n → ℝ :=
  (1 + S.Cᵀ * S.Ri * (S.C * Sg))
    *ᵥ (z + S.Cᵀ *ᵥ ((S.innovS Sg)⁻¹ *ᵥ (S.C *ᵥ e)))

/-- One-step energy: prior-plus-output cost in update coordinates. -/
lemma one_step_energy (hSg : Sg.PosSemidef) (z e : Fin n → ℝ) :
    quadForm Sg z + quadForm S.Ri (S.C *ᵥ (e + Sg *ᵥ z))
      = quadForm (S.innovS Sg)⁻¹ (S.C *ᵥ e)
        + quadForm (S.measM Sg * Sg) (S.updCoord Sg z e) := by
  have h1 : S.C *ᵥ (e + Sg *ᵥ z) = S.C *ᵥ e + S.C *ᵥ (Sg *ᵥ z) := by
    rw [Matrix.mulVec_add]
  rw [h1, S.meas_square hSg z e]
  congr 1
  unfold updCoord
  rw [S.quadForm_measM_resolvent hSg]

/-- The measurement recentering: `e − Me = ΣCᵀS⁻¹Ce`. -/
lemma measM_recenter (e : Fin n → ℝ) :
    e - S.measM Sg *ᵥ e
      = Sg *ᵥ (S.Cᵀ *ᵥ ((S.innovS Sg)⁻¹ *ᵥ (S.C *ᵥ e))) := by
  unfold measM
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  simp only [← Matrix.mulVec_mulVec]
  module

/-- The displacement identity: a supported point moves under the
dynamics to the recentered image plus an `MΣ`-image displacement. -/
lemma displacement (hSg : Sg.PosSemidef) (z e : Fin n → ℝ) :
    S.A *ᵥ (e + Sg *ᵥ z) - S.errF Sg *ᵥ e
      = S.A *ᵥ ((S.measM Sg * Sg) *ᵥ S.updCoord Sg z e) := by
  have h1 : (S.measM Sg * Sg) *ᵥ S.updCoord Sg z e
      = Sg *ᵥ (z + S.Cᵀ *ᵥ ((S.innovS Sg)⁻¹ *ᵥ (S.C *ᵥ e))) := by
    unfold updCoord
    exact S.measM_mul_key_vec hSg _
  rw [h1, S.errF_eq_A_mul_measM, ← Matrix.mulVec_mulVec]
  rw [show Sg *ᵥ (z + S.Cᵀ *ᵥ ((S.innovS Sg)⁻¹ *ᵥ (S.C *ᵥ e)))
      = Sg *ᵥ z + (e - S.measM Sg *ᵥ e) from by
    rw [S.measM_recenter, Matrix.mulVec_add]]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub]
  module

/-- Witness algebra: the update coordinate of the arrival witness is
`Aᵀw`. -/
lemma updCoord_witness (hSg : Sg.PosSemidef) (e w : Fin n → ℝ) :
    S.updCoord Sg
      ((S.measM Sg)ᵀ *ᵥ (S.Aᵀ *ᵥ w)
        - S.Cᵀ *ᵥ ((S.innovS Sg)⁻¹ *ᵥ (S.C *ᵥ e))) e
      = S.Aᵀ *ᵥ w := by
  unfold updCoord
  rw [show (S.measM Sg)ᵀ *ᵥ (S.Aᵀ *ᵥ w)
      - S.Cᵀ *ᵥ ((S.innovS Sg)⁻¹ *ᵥ (S.C *ᵥ e))
      + S.Cᵀ *ᵥ ((S.innovS Sg)⁻¹ *ᵥ (S.C *ᵥ e))
      = (S.measM Sg)ᵀ *ᵥ (S.Aᵀ *ᵥ w) from by module]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have h1 : (1 + S.Cᵀ * S.Ri * (S.C * Sg)) * (S.measM Sg)ᵀ = 1 := by
    have h2 := S.resolvent_mul_measM_transpose hSg
    rwa [show S.Cᵀ * S.Ri * S.C * Sg = S.Cᵀ * S.Ri * (S.C * Sg) from
      Matrix.mul_assoc _ _ _] at h2
  rw [h1, Matrix.one_mul]

/-- The stage-cost split of the horizon-extended objective. -/
lemma gCost_succ_split (a e₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ)
    (T : ℕ) :
    S.gCost a e₀ ω (T + 1)
      = S.gCost a e₀ ω T
        + (quadForm S.Qi (ω T)
          + quadForm S.Ri (S.C *ᵥ S.glq.traj e₀ ω T)) := by
  unfold gCost LQSystem.cost
  rw [Finset.sum_range_succ]
  have h1 : quadForm S.glq.Qs (S.glq.traj e₀ ω T)
      = quadForm S.Ri (S.C *ᵥ S.glq.traj e₀ ω T) := S.quadForm_glq_Qs _
  have h2 : quadForm S.glq.Ru (ω T) = quadForm S.Qi (ω T) := rfl
  rw [h1, h2]
  ring

/-- The trajectory step in error form. -/
lemma traj_succ_glq (e₀ : Fin n → ℝ) (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    S.glq.traj e₀ ω (T + 1)
      = S.A *ᵥ S.glq.traj e₀ ω T - S.G *ᵥ ω T := by
  rw [LQSystem.traj_succ, glq_A_eq, glq_B_eq, Matrix.neg_mulVec]
  module

end StepHelpers

end GeneralSystem

end Estimation
