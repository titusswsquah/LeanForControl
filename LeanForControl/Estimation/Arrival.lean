import LeanForControl.Estimation.KalmanFilter
import LeanForControl.Estimation.QFunction
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

/-- Action form of the covariance step. -/
lemma dreStep_mulVec {Sg : Matrix (Fin n) (Fin n) ℝ} (w : Fin n → ℝ) :
    S.dreStep Sg *ᵥ w
      = S.A *ᵥ ((S.measM Sg * Sg) *ᵥ (S.Aᵀ *ᵥ w))
        + S.G *ᵥ (S.Qcov *ᵥ (S.Gᵀ *ᵥ w)) := by
  unfold dreStep
  rw [Matrix.add_mulVec]
  simp only [← Matrix.mulVec_mulVec]

/-! ### The arrival recursion (`lem:arrival`) -/

/-- **`lem:arrival`**: at every horizon, the terminally constrained
full-information problem is feasible exactly on the affine set
`arrC + im(dre T)`, and on it the least cost is the accumulated
innovation cost plus the covariance-weighted displacement — the
support-constrained arrival recursion whose center update is the
Kalman filter. -/
theorem arrival (a : Fin n → ℝ) : ∀ T : ℕ,
    (∀ z, IsLeast (S.arrSet a T (S.arrC a T + S.dre T *ᵥ z))
      (S.arrV a T + quadForm (S.dre T) z))
    ∧ (∀ ξ, (S.arrSet a T ξ).Nonempty
        → ∃ z, ξ = S.arrC a T + S.dre T *ᵥ z) := by
  intro T
  induction T with
  | zero =>
    constructor
    · intro z
      constructor
      · refine ⟨a + S.Sig0 *ᵥ z, fun _ => 0, ⟨z, by module⟩, rfl, ?_⟩
        unfold gCost priorPen
        rw [show a + S.Sig0 *ᵥ z - a = S.Sig0 *ᵥ z from by module,
          quadForm_symmPinv_image S.hSig0]
        have h1 : S.glq.cost (a + S.Sig0 *ᵥ z) (fun _ => 0) 0 = 0 :=
          S.glq.cost_zero _ _
        rw [h1]
        show S.arrV a 0 + quadForm (S.dre 0) z = _
        rw [arrV_zero]
        show 0 + quadForm S.Sig0 z = quadForm S.Sig0 z + 0
        ring
      · rintro c ⟨e₀, ω, hfeas, htraj, rfl⟩
        have he₀ : e₀ = S.arrC a 0 + S.dre 0 *ᵥ z := htraj
        unfold gCost priorPen
        have h1 : S.glq.cost e₀ ω 0 = 0 := S.glq.cost_zero _ _
        rw [h1]
        have h2 : e₀ - a = S.Sig0 *ᵥ z := by
          rw [he₀]
          show a + S.Sig0 *ᵥ z - a = S.Sig0 *ᵥ z
          module
        rw [h2, quadForm_symmPinv_image S.hSig0]
        show S.arrV a 0 + quadForm (S.dre 0) z ≤ _
        rw [arrV_zero]
        show 0 + quadForm S.Sig0 z ≤ quadForm S.Sig0 z + 0
        ring_nf
        exact le_refl _
    · rintro ξ ⟨c, e₀, ω, hfeas, htraj, hc⟩
      obtain ⟨z, hz⟩ := hfeas
      refine ⟨z, ?_⟩
      rw [← htraj]
      show e₀ = a + S.Sig0 *ᵥ z
      rw [← hz]
      module
  | succ T ih =>
    obtain ⟨ihLeast, ihSupp⟩ := ih
    have hps := S.dre_posSemidef T
    constructor
    · intro w
      constructor
      · -- membership: extend the horizon-`T` witness
        set zstar : Fin n → ℝ :=
          (S.measM (S.dre T))ᵀ *ᵥ (S.Aᵀ *ᵥ w)
            - S.Cᵀ *ᵥ ((S.innovS (S.dre T))⁻¹
              *ᵥ (S.C *ᵥ S.arrC a T)) with hzstar
        obtain ⟨e₀s, ωs, hfs, htrajs, hcosts⟩ := (ihLeast zstar).1
        set ωT : Fin m → ℝ := -(S.Qcov *ᵥ (S.Gᵀ *ᵥ w)) with hωT
        set ωext : ℕ → Fin m → ℝ :=
          fun j => if j < T then ωs j else ωT with hωext
        have hagree : ∀ j < T, ωext j = ωs j := by
          intro j hj
          rw [hωext]
          simp [hj]
        have htrajT : S.glq.traj e₀s ωext T
            = S.arrC a T + S.dre T *ᵥ zstar := by
          rw [S.glq.traj_congr e₀s hagree, htrajs]
        have hωextT : ωext T = ωT := by
          rw [hωext]
          simp
        refine ⟨e₀s, ωext, hfs, ?_, ?_⟩
        · rw [S.traj_succ_glq, htrajT, hωextT, hωT]
          have h1 := S.displacement hps zstar (S.arrC a T)
          rw [S.updCoord_witness hps] at h1
          have h2 : S.A *ᵥ (S.arrC a T + S.dre T *ᵥ zstar)
              = S.errF (S.dre T) *ᵥ S.arrC a T
                + S.A *ᵥ ((S.measM (S.dre T) * S.dre T)
                  *ᵥ (S.Aᵀ *ᵥ w)) := by
            rw [← h1]
            module
          rw [h2, ← arrC_succ,
            show S.dre (T + 1) = S.dreStep (S.dre T) from rfl,
            S.dreStep_mulVec, Matrix.mulVec_neg]
          module
        · -- the extended cost equals the arrival value
          rw [S.gCost_succ_split]
          have hcc : S.gCost a e₀s ωext T = S.gCost a e₀s ωs T := by
            unfold gCost
            rw [S.glq.cost_congr e₀s hagree]
          rw [hcc, ← hcosts, hωextT, htrajT]
          have hen := S.one_step_energy hps zstar (S.arrC a T)
          rw [S.updCoord_witness hps] at hen
          have hneg : quadForm S.Qi ωT
              = quadForm S.Qcov (S.Gᵀ *ᵥ w) := by
            rw [hωT, show -(S.Qcov *ᵥ (S.Gᵀ *ᵥ w))
                = (-1 : ℝ) • (S.Qcov *ᵥ (S.Gᵀ *ᵥ w)) from by module,
              quadForm_smul, S.quadForm_Qi_Qcov]
            norm_num
          rw [hneg, S.arrV_succ,
            show S.dre (T + 1) = S.dreStep (S.dre T) from rfl,
            S.quadForm_dreStep]
          linarith [hen]
      · -- lower bound through the pushforward
        rintro cval ⟨e₀, ω, hfeas, htraj, rfl⟩
        have hmemT : S.gCost a e₀ ω T
            ∈ S.arrSet a T (S.glq.traj e₀ ω T) :=
          ⟨e₀, ω, hfeas, rfl, rfl⟩
        obtain ⟨zT, hzT⟩ := ihSupp _ ⟨_, hmemT⟩
        have hlow := (ihLeast zT).2 (by rw [← hzT]; exact hmemT)
        have hdisp := S.displacement hps zT (S.arrC a T)
        have hstep := S.traj_succ_glq e₀ ω T
        rw [htraj, hzT] at hstep
        -- hstep : arrC(T+1) + Σ⁺w = A(ct + ΣzT) − Gω(T)
        rw [S.arrC_succ,
          show S.dre (T + 1) = S.dreStep (S.dre T) from rfl] at hstep
        have hcon : S.A *ᵥ ((S.measM (S.dre T) * S.dre T)
              *ᵥ S.updCoord (S.dre T) zT (S.arrC a T))
            - S.G *ᵥ ω T = S.dreStep (S.dre T) *ᵥ w := by
          rw [← hdisp]
          have h9 := sub_eq_iff_eq_add.mp hstep.symm
          rw [h9]
          module
        have hpush := S.pushforward_lower hps _ (ω T) w hcon
        have hen := S.one_step_energy hps zT (S.arrC a T)
        rw [S.gCost_succ_split, hzT]
        have hlow' : S.arrV a T + quadForm (S.dre T) zT
            ≤ S.gCost a e₀ ω T := hlow
        rw [S.arrV_succ,
          show S.dre (T + 1) = S.dreStep (S.dre T) from rfl]
        linarith [hen, hpush, hlow']
    · -- support at `T+1`
      rintro ξp ⟨cval, e₀, ω, hfeas, htraj, -⟩
      have hmemT : S.gCost a e₀ ω T
          ∈ S.arrSet a T (S.glq.traj e₀ ω T) :=
        ⟨e₀, ω, hfeas, rfl, rfl⟩
      obtain ⟨zT, hzT⟩ := ihSupp _ ⟨_, hmemT⟩
      have hps' := hps
      obtain ⟨w, hw⟩ := S.pushforward_mem_range hps
        (S.updCoord (S.dre T) zT (S.arrC a T)) (ω T)
      refine ⟨w, ?_⟩
      have hdisp := S.displacement hps zT (S.arrC a T)
      rw [← htraj, S.traj_succ_glq, hzT, S.arrC_succ,
        show S.dre (T + 1) = S.dreStep (S.dre T) from rfl, ← hw,
        ← hdisp]
      module

/-! ### Corollaries: `lem:semiPT` and the innovations decomposition -/

/-- **The innovations decomposition**: the optimal value is the
accumulated innovation cost of the Kalman filter. -/
theorem value_eq_arrV (a : Fin n → ℝ) (T : ℕ) :
    S.value a T = S.arrV a T := by
  refine le_antisymm ?_ ?_
  · -- the arrival center is attainable at cost `arrV`
    have h1 := (S.arrival a T).1 0
    rw [Matrix.mulVec_zero, add_zero, quadForm_zero, add_zero] at h1
    obtain ⟨e₀, ω, hfeas, htraj, hcost⟩ := h1.1
    calc S.value a T ≤ S.gCost a e₀ ω T := S.value_le_gCost hfeas ω T
      _ = S.arrV a T := hcost.symm
  · -- the optimum lands on the support
    have hmem : S.gCost a (S.optInit a T)
        (S.glq.optCtrl (S.optInit a T) T) T
        ∈ S.arrSet a T (S.glq.traj (S.optInit a T)
          (S.glq.optCtrl (S.optInit a T) T) T) :=
      ⟨_, _, S.optInit_feasible a T, rfl, rfl⟩
    obtain ⟨z, hz⟩ := (S.arrival a T).2 _ ⟨_, hmem⟩
    have h2 := ((S.arrival a T).1 z).2 (by rw [← hz]; exact hmem)
    have h3 := (S.dre_posSemidef T).quadForm_nonneg z
    have h4 := S.gCost_optCtrl a T
    linarith [h2, h4.ge, h4.le]

/-- The optimal terminal error is the arrival center. -/
theorem optTerm_eq_arrC (a : Fin n → ℝ) (T : ℕ) :
    S.optTerm a T = S.arrC a T := by
  have hmem : S.gCost a (S.optInit a T)
      (S.glq.optCtrl (S.optInit a T) T) T
      ∈ S.arrSet a T (S.glq.traj (S.optInit a T)
        (S.glq.optCtrl (S.optInit a T) T) T) :=
    ⟨_, _, S.optInit_feasible a T, rfl, rfl⟩
  obtain ⟨z, hz⟩ := (S.arrival a T).2 _ ⟨_, hmem⟩
  have h2 := ((S.arrival a T).1 z).2 (by rw [← hz]; exact hmem)
  have h4 := S.gCost_optCtrl a T
  have h5 := S.value_eq_arrV a T
  have h6 : quadForm (S.dre T) z ≤ 0 := by linarith
  have h7 : quadForm (S.dre T) z = 0 :=
    le_antisymm h6 ((S.dre_posSemidef T).quadForm_nonneg z)
  have h8 := (S.dre_posSemidef T).mulVec_eq_zero_of_quadForm_eq_zero h7
  rw [S.optTerm_eq_traj, hz, h8, add_zero]

/-- The arrival center is the Kalman-filter error iterate. -/
theorem arrC_eq_kfErrTrans (a : Fin n → ℝ) : ∀ T : ℕ,
    S.arrC a T = S.kfErrTrans T *ᵥ a
  | 0 => by
    rw [arrC_zero, kfErrTrans_zero, Matrix.one_mulVec]
  | T + 1 => by
    rw [arrC_succ, kfErrTrans_succ, arrC_eq_kfErrTrans a T,
      Matrix.mulVec_mulVec]

/-- **`lem:semiPT`, nominal-error form** (`eq:fie-center`): the
horizon-`T` optimal terminal error of the full-information problem is
the time-varying Kalman filter error `M(T)a`. -/
theorem semiPT_error (a : Fin n → ℝ) (T : ℕ) :
    S.optTerm a T = S.kfErrTrans T *ᵥ a := by
  rw [S.optTerm_eq_arrC, S.arrC_eq_kfErrTrans]

/-- The innovations formula for the value increments. -/
theorem value_succ_innovation (a : Fin n → ℝ) (T : ℕ) :
    S.value a (T + 1)
      = S.value a T
        + quadForm (S.innovS (S.dre T))⁻¹
            (S.C *ᵥ (S.kfErrTrans T *ᵥ a)) := by
  rw [S.value_eq_arrV, S.value_eq_arrV, S.arrV_succ,
    S.arrC_eq_kfErrTrans]

/-! ### `prop:tvkf` for the Kalman filter -/

/-- GAS of the time-varying Kalman filter (`def:GAS` for the recursive
filter error `ê(k) = M(k)ê(0)`, σ-form). -/
def IsGASkf : Prop :=
  ∃ σ : ℕ → ℝ, Filter.Tendsto σ Filter.atTop (nhds 0) ∧
    ∀ (T : ℕ) (a : Fin n → ℝ), ‖S.kfErrTrans T *ᵥ a‖ ≤ σ T * ‖a‖

/-- The filter error and the optimizer error coincide (`lem:semiPT`),
so the two stability notions agree. -/
theorem isGASkf_iff_isGAS : S.IsGASkf ↔ S.IsGAS := by
  unfold IsGASkf IsGAS
  constructor
  · rintro ⟨σ, h0, hb⟩
    exact ⟨σ, h0, fun T a => by rw [S.semiPT_error]; exact hb T a⟩
  · rintro ⟨σ, h0, hb⟩
    exact ⟨σ, h0, fun T a => by rw [← S.semiPT_error]; exact hb T a⟩

/-- **`prop:tvkf`**, the paper's literal headline: the time-varying
Kalman filter is asymptotically stable iff C1 ∧ C2. -/
theorem prop_tvkf : S.IsGASkf ↔ S.C1 ∧ S.C2 := by
  rw [S.isGASkf_iff_isGAS]
  exact S.prop_tvkf_optimizer

/-- **F5, the paper's `M(k)` uniformization**: pointwise convergence
of the Kalman-filter error `M(k)a → 0` upgrades to the uniform σ-bound
of `def:GAS`, by linearity of `a ↦ M(k)a` and the standard-basis
column trick — run on the very map the paper's `M(k)` denotes, via
`lem:semiPT`. -/
theorem isGASkf_of_pointwise
    (h : ∀ a : Fin n → ℝ,
      Filter.Tendsto (fun T => ‖S.kfErrTrans T *ᵥ a‖)
        Filter.atTop (nhds 0)) : S.IsGASkf := by
  rw [S.isGASkf_iff_isGAS]
  exact S.isGAS_of_pointwise fun a => by
    simpa only [S.semiPT_error] using h a

/-- `prop:tvkf` in the KL formulation of `def:GAS`, on the filter
error. -/
theorem prop_tvkf_kl :
    (∃ α : ℕ → ℝ, Antitone α ∧ Filter.Tendsto α Filter.atTop (nhds 0) ∧
      ∀ (k : ℕ) (a : Fin n → ℝ), ‖S.kfErrTrans k *ᵥ a‖ ≤ α k * ‖a‖)
      ↔ S.C1 ∧ S.C2 := by
  constructor
  · rintro ⟨α, _hanti, h0, hb⟩
    exact S.prop_tvkf.mp ⟨α, h0, hb⟩
  · intro h
    have h1 := S.prop_tvkf_optimizer_kl.mpr h
    obtain ⟨α, hanti, h0, hb⟩ := h1
    exact ⟨α, hanti, h0, fun k a => by
      rw [← S.semiPT_error]; exact hb k a⟩

end GeneralSystem

end Estimation
