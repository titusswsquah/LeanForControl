import LeanForControl.Estimation.Staircase
import LeanForControl.Estimation.FIE
import Architect

/-!
# Reduction of a general system to the canonical `FIESystem` class

Composes the staircase change of coordinates (`Estimation.Staircase`)
with the prior-decoupling congruence `T₂ = [[1, -K],[0,1]]`,
`K = Σ₁₂ Σ₂⁻¹`, to produce from any `GeneralSystem` an `FIESystem` in
the reduced coordinates of the papers. The transformation matrix is
`Mt = T₂ * W`; under C2 the transformed prior is block-diagonal, so the
general full-information problem and the reduced one coincide under
`e ↦ Mt e`.
-/

namespace Estimation

open Matrix LinearSystems Module

set_option linter.style.show false

namespace GeneralSystem

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-! ### The decoupling congruence and the composed transformation -/

/-- The prior-decoupling gain `K = Σ₁₂ Σ₂⁻¹` (junk if `Σ₂` is
singular; C2 makes it meaningful). -/
noncomputable def decK : Matrix (Fin S.rk1) (Fin S.rk2) ℝ :=
  S.stairSig.toBlocks₁₂ * S.stairSig.toBlocks₂₂⁻¹

/-- The decoupling congruence `T₂`. -/
noncomputable def decT : Matrix (Fin S.rk1 ⊕ Fin S.rk2)
    (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  Matrix.fromBlocks 1 (-S.decK) 0 1

/-- Its inverse. -/
noncomputable def decTinv : Matrix (Fin S.rk1 ⊕ Fin S.rk2)
    (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  Matrix.fromBlocks 1 S.decK 0 1

lemma decT_mul_decTinv : S.decT * S.decTinv = 1 := by
  unfold decT decTinv
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> simp

lemma decTinv_mul_decT : S.decTinv * S.decT = 1 := by
  unfold decT decTinv
  rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> simp

/-- The composed transformation `Mt = T₂ W` to reduced coordinates. -/
noncomputable def redT : Matrix (Fin S.rk1 ⊕ Fin S.rk2) (Fin n) ℝ :=
  S.decT * S.stairW

/-- Its inverse `Winv T₂⁻¹`. -/
noncomputable def redTinv : Matrix (Fin n)
    (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  S.stairWinv * S.decTinv

lemma redT_mul_redTinv : S.redT * S.redTinv = 1 := by
  unfold redT redTinv
  calc S.decT * S.stairW * (S.stairWinv * S.decTinv)
      = S.decT * (S.stairW * S.stairWinv) * S.decTinv := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [stairW_mul_stairWinv, Matrix.mul_one, decT_mul_decTinv]

lemma redTinv_mul_redT : S.redTinv * S.redT = 1 := by
  unfold redT redTinv
  calc S.stairWinv * S.decTinv * (S.decT * S.stairW)
      = S.stairWinv * (S.decTinv * S.decT) * S.stairW := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [decTinv_mul_decT, Matrix.mul_one, stairWinv_mul_stairW]

/-! ### The reduced data -/

/-- The reduced dynamics `T₂ A' T₂⁻¹`. -/
noncomputable def redA : Matrix (Fin S.rk1 ⊕ Fin S.rk2)
    (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  S.decT * S.stairA * S.decTinv

/-- The reduced noise input `T₂ G'`. -/
noncomputable def redG : Matrix (Fin S.rk1 ⊕ Fin S.rk2) (Fin m) ℝ :=
  S.decT * S.stairG

/-- The reduced output map `C' T₂⁻¹`. -/
noncomputable def redC : Matrix (Fin p) (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  S.stairC * S.decTinv

/-- The reduced prior `T₂ Σ' T₂ᵀ`. -/
noncomputable def redSig : Matrix (Fin S.rk1 ⊕ Fin S.rk2)
    (Fin S.rk1 ⊕ Fin S.rk2) ℝ :=
  S.decT * S.stairSig * S.decTᵀ

/-- The staircase dynamics in explicit block form. -/
lemma stairA_blocks_eq :
    S.stairA = Matrix.fromBlocks S.stairA.toBlocks₁₁
      S.stairA.toBlocks₁₂ 0 S.stairA.toBlocks₂₂ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks S.stairA]
  rw [S.stairA_toBlocks₂₁]

/-- The staircase noise input in explicit block form. -/
lemma stairG_blocks_eq :
    S.stairG = Matrix.fromRows S.stairG₁ 0 := by
  ext i j
  rcases i with i | i
  · rfl
  · rw [show S.stairG (Sum.inr i) j = 0 from S.stairG_inr_eq_zero i j]
    rfl

/-- The reduced dynamics blockwise: diagonal blocks unchanged, `(2,1)`
block zero. -/
lemma redA_eq_fromBlocks :
    S.redA = Matrix.fromBlocks S.stairA.toBlocks₁₁
      (S.stairA.toBlocks₁₁ * S.decK + S.stairA.toBlocks₁₂
        - S.decK * S.stairA.toBlocks₂₂)
      0 S.stairA.toBlocks₂₂ := by
  unfold redA decT decTinv
  rw [S.stairA_blocks_eq, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  refine ⟨by simp, ?_, by simp, by simp⟩
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    Matrix.add_mul]
  abel

/-- The reduced noise input blockwise. -/
lemma redG_eq_fromRows : S.redG = Matrix.fromRows S.stairG₁ 0 := by
  unfold redG decT
  rw [S.stairG_blocks_eq, Matrix.fromBlocks_mul_fromRows]
  rw [Matrix.fromRows_inj.eq_iff]
  refine ⟨by simp, by simp⟩

/-- The staircase output map split into column blocks. -/
noncomputable def stairC₁ : Matrix (Fin p) (Fin S.rk1) ℝ :=
  S.stairC.submatrix id Sum.inl

/-- Second column block of the staircase output map. -/
noncomputable def stairC₂ : Matrix (Fin p) (Fin S.rk2) ℝ :=
  S.stairC.submatrix id Sum.inr

lemma stairC_blocks_eq :
    S.stairC = Matrix.fromCols S.stairC₁ S.stairC₂ := by
  ext i j
  rcases j with j | j <;> rfl

/-- The reduced output map blockwise. -/
lemma redC_eq_fromCols :
    S.redC = Matrix.fromCols S.stairC₁ (S.stairC₁ * S.decK + S.stairC₂) := by
  unfold redC decTinv
  rw [S.stairC_blocks_eq, Matrix.fromCols_mul_fromBlocks]
  rw [Matrix.fromCols_inj.eq_iff]
  constructor
  · simp
  · simp

/-- The staircase prior in explicit block form. -/
lemma stairSig_blocks_eq :
    S.stairSig = Matrix.fromBlocks S.stairSig.toBlocks₁₁
      S.stairSig.toBlocks₁₂ S.stairSig.toBlocks₂₁
      S.stairSig.toBlocks₂₂ :=
  (Matrix.fromBlocks_toBlocks S.stairSig).symm

/-- The reduced prior blockwise. -/
lemma redSig_eq_fromBlocks :
    S.redSig = Matrix.fromBlocks
      (S.stairSig.toBlocks₁₁ - S.decK * S.stairSig.toBlocks₂₁
        - S.stairSig.toBlocks₁₂ * S.decKᵀ
        + S.decK * S.stairSig.toBlocks₂₂ * S.decKᵀ)
      (S.stairSig.toBlocks₁₂ - S.decK * S.stairSig.toBlocks₂₂)
      (S.stairSig.toBlocks₂₁ - S.stairSig.toBlocks₂₂ * S.decKᵀ)
      S.stairSig.toBlocks₂₂ := by
  unfold redSig decT
  rw [S.stairSig_blocks_eq, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul,
      Matrix.mul_neg, Matrix.transpose_one, Matrix.transpose_neg,
      Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, Matrix.add_mul, Matrix.sub_mul,
      Matrix.neg_mul, Matrix.mul_assoc]
    abel
  · simp [sub_eq_add_neg]
  · simp [Matrix.add_mul, sub_eq_add_neg]
  · simp

/-- The reduced prior is a congruence of the original prior. -/
lemma redSig_eq_congruence :
    S.redSig = S.redT * S.Sig0 * S.redTᵀ := by
  unfold redSig redT stairSig
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

lemma redSig_posSemidef : S.redSig.PosSemidef := by
  rw [redSig_eq_congruence]
  have h := S.hSig0.mul_mul_conjTranspose_same S.redT
  rwa [show S.redTᴴ = S.redTᵀ from
    Matrix.conjTranspose_eq_transpose_of_trivial _] at h

/-! ### The reduced `FIESystem` -/

/-- The reduced system: a member of the canonical `FIESystem` class
built from any `GeneralSystem` (no conditions needed for membership;
C2 additionally decouples the prior blocks). -/
noncomputable def redSys : FIESystem S.rk1 S.rk2 m p where
  A₁ := S.stairA.toBlocks₁₁
  A₁₂ := S.stairA.toBlocks₁₁ * S.decK + S.stairA.toBlocks₁₂
    - S.decK * S.stairA.toBlocks₂₂
  A₂ := S.stairA.toBlocks₂₂
  G₁ := S.stairG₁
  C₁ := S.stairC₁
  C₂ := S.stairC₁ * S.decK + S.stairC₂
  Qi := S.Qi
  Ri := S.Ri
  Sig₁ := S.redSig.toBlocks₁₁
  Sig₂ := S.stairSig.toBlocks₂₂
  hQi := S.hQi
  hRi := S.hRi
  hSig₁ := S.redSig_posSemidef.submatrix Sum.inl
  hSig₂ := S.stairSig_posSemidef.submatrix Sum.inr
  hStab := S.stair_stabilizable
  hAnti := S.stairA₂_antistable

/-- The reduced system's full dynamics is the transformed matrix. -/
lemma redSys_fullA : S.redSys.fullA = S.redA := by
  rw [redA_eq_fromBlocks]
  rfl

/-- The reduced system's full noise input is the transformed matrix. -/
lemma redSys_fullG : S.redSys.fullG = S.redG := by
  rw [redG_eq_fromRows]
  rfl

/-- The reduced system's full output map is the transformed matrix. -/
lemma redSys_fullC : S.redSys.fullC = S.redC := by
  rw [redC_eq_fromCols]
  rfl

/-! ### Transformation identities -/

lemma stairA_eq : S.stairA = S.stairW * S.A * S.stairWinv := by
  have h := S.stairA_conj
  calc S.stairA = S.stairA * (S.stairW * S.stairWinv) := by
        rw [stairW_mul_stairWinv, Matrix.mul_one]
    _ = (S.stairA * S.stairW) * S.stairWinv := by
        rw [Matrix.mul_assoc]
    _ = (S.stairW * S.A) * S.stairWinv := by rw [h]
    _ = S.stairW * S.A * S.stairWinv := rfl

lemma stairC_eq_mul : S.stairC = S.C * S.stairWinv := S.stairC_eq

lemma redA_eq : S.redA = S.redT * S.A * S.redTinv := by
  unfold redA redT redTinv
  rw [S.stairA_eq]
  simp only [Matrix.mul_assoc]

lemma redG_mul_eq : S.redG = S.redT * S.G := by
  unfold redG redT
  rw [S.stairG_eq, Matrix.mul_assoc]

lemma redC_mul_eq : S.redC = S.C * S.redTinv := by
  unfold redC redTinv
  rw [S.stairC_eq]
  simp only [Matrix.mul_assoc]

/-! ### Prior decoupling under C2 -/

lemma redSig_toBlocks₂₂_eq :
    S.redSig.toBlocks₂₂ = S.stairSig.toBlocks₂₂ := by
  rw [redSig_eq_fromBlocks, Matrix.toBlocks_fromBlocks₂₂]

lemma redSig_toBlocks₁₂_eq_zero (hC2 : S.C2) :
    S.redSig.toBlocks₁₂ = 0 := by
  have hPD := (S.C2_iff_stairSig₂_posDef).mp hC2
  rw [redSig_eq_fromBlocks, Matrix.toBlocks_fromBlocks₁₂]
  unfold decK
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr hPD.det_pos.ne'), Matrix.mul_one, sub_self]

lemma redSig_toBlocks₂₁_eq_zero (hC2 : S.C2) :
    S.redSig.toBlocks₂₁ = 0 := by
  have hherm := S.redSig_posSemidef.1
  have h12 := S.redSig_toBlocks₁₂_eq_zero hC2
  ext i j
  have h := congrFun (congrFun hherm (Sum.inl j)) (Sum.inr i)
  simp only [Matrix.conjTranspose_apply, star_trivial] at h
  have h2 := congrFun (congrFun h12 j) i
  simp only [Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.zero_apply] at h2
  show S.redSig (Sum.inr i) (Sum.inl j) = 0
  rw [h, h2]

/-- Under C2 the reduced prior is exactly the block-diagonal `Jmat` of
the reduced system. -/
lemma redSys_Jmat_eq (hC2 : S.C2) : S.redSys.Jmat = S.redSig := by
  show Matrix.fromBlocks S.redSig.toBlocks₁₁ 0 0
    S.stairSig.toBlocks₂₂ = S.redSig
  rw [← S.redSig_toBlocks₂₂_eq, ← S.redSig_toBlocks₁₂_eq_zero hC2,
    ← S.redSig_toBlocks₂₁_eq_zero hC2, Matrix.fromBlocks_toBlocks]

/-! ### Cancellation helpers -/

variable {α : Type*} [Fintype α]

lemma redTinv_redT_cancel (X : Matrix (Fin n) α ℝ) :
    S.redTinv * (S.redT * X) = X := by
  rw [← Matrix.mul_assoc, redTinv_mul_redT, Matrix.one_mul]

lemma redT_redTinv_cancel (X : Matrix (Fin S.rk1 ⊕ Fin S.rk2) α ℝ) :
    S.redT * (S.redTinv * X) = X := by
  rw [← Matrix.mul_assoc, redT_mul_redTinv, Matrix.one_mul]

lemma redTt_redTinvt_cancel (X : Matrix (Fin n) α ℝ) :
    S.redTᵀ * (S.redTinvᵀ * X) = X := by
  rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, redTinv_mul_redT,
    Matrix.transpose_one, Matrix.one_mul]

lemma redTinvt_redTt_cancel
    (X : Matrix (Fin S.rk1 ⊕ Fin S.rk2) α ℝ) :
    S.redTinvᵀ * (S.redTᵀ * X) = X := by
  rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, redT_mul_redTinv,
    Matrix.transpose_one, Matrix.one_mul]

/-! ### The LQ layer under the transformation -/

lemma redSys_lq_A : S.redSys.lq.A = S.redT * S.glq.A * S.redTinv := by
  show S.redSys.fullA = S.redT * S.A * S.redTinv
  rw [redSys_fullA, redA_eq]

lemma redSys_lq_B : S.redSys.lq.B = S.redT * S.glq.B := by
  show -S.redSys.fullG = S.redT * (-S.G)
  rw [redSys_fullG, redG_mul_eq, Matrix.mul_neg]

lemma redSys_lq_Qs :
    S.redSys.lq.Qs = S.redTinvᵀ * S.glq.Qs * S.redTinv := by
  show S.redSys.fullCᵀ * S.Ri * S.redSys.fullC
    = S.redTinvᵀ * (S.Cᵀ * S.Ri * S.C) * S.redTinv
  rw [redSys_fullC, redC_mul_eq]
  simp only [Matrix.transpose_mul, Matrix.mul_assoc]

lemma redSys_lq_Ru : S.redSys.lq.Ru = S.glq.Ru := rfl

/-- Dynamics intertwining at the vector level. -/
lemma red_dyn_mulVec (x : Fin n → ℝ) :
    S.redSys.lq.A *ᵥ (S.redT *ᵥ x) = S.redT *ᵥ (S.glq.A *ᵥ x) := by
  rw [redSys_lq_A, Matrix.mulVec_mulVec]
  have h : S.redT * S.glq.A * S.redTinv * S.redT = S.redT * S.glq.A := by
    rw [Matrix.mul_assoc (S.redT * S.glq.A), redTinv_mul_redT,
      Matrix.mul_one]
  rw [h, ← Matrix.mulVec_mulVec]

/-- Trajectories correspond under the transformation. -/
lemma red_traj (x₀ : Fin n → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) :
    S.redSys.lq.traj (S.redT *ᵥ x₀) u k
      = S.redT *ᵥ S.glq.traj x₀ u k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [LQSystem.traj_succ, LQSystem.traj_succ, ih, red_dyn_mulVec,
      redSys_lq_B, ← Matrix.mulVec_mulVec, Matrix.mulVec_add]

/-- Stage state-costs correspond. -/
lemma red_quadForm_Qs (x : Fin n → ℝ) :
    quadForm S.redSys.lq.Qs (S.redT *ᵥ x) = quadForm S.glq.Qs x := by
  rw [quadForm_mulVec, redSys_lq_Qs]
  congr 1
  calc S.redTᵀ * (S.redTinvᵀ * S.glq.Qs * S.redTinv) * S.redT
      = S.redTᵀ * (S.redTinvᵀ * (S.glq.Qs * (S.redTinv * S.redT))) := by
        simp only [Matrix.mul_assoc]
    _ = S.glq.Qs := by
        rw [redTinv_mul_redT, Matrix.mul_one, redTt_redTinvt_cancel]

/-- Costs correspond. -/
lemma red_cost (x₀ : Fin n → ℝ) (u : ℕ → Fin m → ℝ) (T : ℕ) :
    S.redSys.lq.cost (S.redT *ᵥ x₀) u T = S.glq.cost x₀ u T := by
  unfold LQSystem.cost
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [red_traj, red_quadForm_Qs]
  rfl

/-! ### Riccati similarity and the optimal trajectory -/

lemma red_step (P : Matrix (Fin n) (Fin n) ℝ) :
    S.redSys.lq.step (S.redTinvᵀ * P * S.redTinv)
      = S.redTinvᵀ * S.glq.step P * S.redTinv := by
  unfold LQSystem.step LQSystem.gainΓ
  rw [redSys_lq_A, redSys_lq_B, redSys_lq_Qs, redSys_lq_Ru]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, redTinv_redT_cancel, redTt_redTinvt_cancel,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul]

lemma red_ric (T : ℕ) :
    S.redSys.lq.ric T = S.redTinvᵀ * S.glq.ric T * S.redTinv := by
  induction T with
  | zero =>
    rw [LQSystem.ric_zero, LQSystem.ric_zero, Matrix.mul_zero,
      Matrix.zero_mul]
  | succ T ih =>
    rw [LQSystem.ric_succ, LQSystem.ric_succ, ih, red_step]

lemma red_gainK (P : Matrix (Fin n) (Fin n) ℝ) :
    S.redSys.lq.gainK (S.redTinvᵀ * P * S.redTinv)
      = S.glq.gainK P * S.redTinv := by
  unfold LQSystem.gainK LQSystem.gainΓ
  rw [redSys_lq_A, redSys_lq_B, redSys_lq_Ru]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc, redTinv_redT_cancel, redTt_redTinvt_cancel]

lemma red_Acl (P : Matrix (Fin n) (Fin n) ℝ) :
    S.redSys.lq.Acl (S.redTinvᵀ * P * S.redTinv)
      = S.redT * S.glq.Acl P * S.redTinv := by
  unfold LQSystem.Acl
  rw [red_gainK, redSys_lq_A, redSys_lq_B]
  rw [Matrix.mul_sub, Matrix.sub_mul]
  simp only [Matrix.mul_assoc]

/-- Optimal closed-loop trajectories correspond. -/
lemma red_optTraj (x₀ : Fin n → ℝ) (T k : ℕ) :
    S.redSys.lq.optTraj (S.redT *ᵥ x₀) T k
      = S.redT *ᵥ S.glq.optTraj x₀ T k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show S.redSys.lq.Acl (S.redSys.lq.ric (T - 1 - k))
        *ᵥ S.redSys.lq.optTraj (S.redT *ᵥ x₀) T k
      = S.redT *ᵥ (S.glq.Acl (S.glq.ric (T - 1 - k))
        *ᵥ S.glq.optTraj x₀ T k)
    rw [ih, red_ric, red_Acl, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.mul_assoc (S.redT * S.glq.Acl (S.glq.ric (T - 1 - k))),
      redTinv_mul_redT, Matrix.mul_one]

/-! ### Vector-level cancellations -/

lemma redTinv_redT_mulVec (x : Fin n → ℝ) :
    S.redTinv *ᵥ (S.redT *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, redTinv_mul_redT, Matrix.one_mulVec]

lemma redT_redTinv_mulVec (y : Fin S.rk1 ⊕ Fin S.rk2 → ℝ) :
    S.redT *ᵥ (S.redTinv *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, redT_mul_redTinv, Matrix.one_mulVec]

/-- Sandwich pairing for the pseudoinverse on the range. -/
private lemma pinv_pairing {k : ℕ} {W : Matrix (Fin k) (Fin k) ℝ}
    (hW : W.PosSemidef) (z w : Fin k → ℝ) :
    (symmPinv hW.1 *ᵥ (W *ᵥ z)) ⬝ᵥ (W *ᵥ w) = (W *ᵥ z) ⬝ᵥ w := by
  have hWt : Wᵀ = W := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hW.1
  rw [dotProduct_mulVec_eq, hWt, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, self_mul_symmPinv_mul_self hW.1]

/-! ### Feasibility and penalty transfer (under C2) -/

/-- The transported prior deviation, parameterized on the reduced
prior's range. -/
lemma red_sub_param {a e₀ z : Fin n → ℝ}
    (hz : e₀ - a = S.Sig0 *ᵥ z) :
    S.redT *ᵥ e₀ - S.redT *ᵥ a
      = S.redSig *ᵥ (S.redTinvᵀ *ᵥ z) := by
  rw [← Matrix.mulVec_sub, hz, redSig_eq_congruence]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  rw [Matrix.mul_assoc (S.redT * S.Sig0), ← Matrix.transpose_mul,
    redTinv_mul_redT, Matrix.transpose_one, Matrix.mul_one]

lemma red_feasible (hC2 : S.C2) {a e₀ : Fin n → ℝ}
    (h : S.Feasible a e₀) :
    S.redSys.Feasible (S.redT *ᵥ a) (S.redT *ᵥ e₀) := by
  obtain ⟨z, hz⟩ := h
  rw [FIESystem.feasible_iff]
  exact ⟨S.redTinvᵀ *ᵥ z, by
    rw [S.redSys_Jmat_eq hC2, S.red_sub_param hz]⟩

lemma red_feasible_rev (hC2 : S.C2)
    {a' e₀' : Fin S.rk1 ⊕ Fin S.rk2 → ℝ}
    (h : S.redSys.Feasible a' e₀') :
    S.Feasible (S.redTinv *ᵥ a') (S.redTinv *ᵥ e₀') := by
  obtain ⟨v, hv⟩ := (S.redSys.feasible_iff a' e₀').mp h
  rw [S.redSys_Jmat_eq hC2, redSig_eq_congruence] at hv
  refine ⟨S.redTᵀ *ᵥ v, ?_⟩
  rw [← Matrix.mulVec_sub, hv]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, redTinv_mul_redT,
    Matrix.one_mul]

/-- Quadratic form of the block-diagonal `Jmat` splits blockwise. -/
private lemma quadForm_Jmat {n₁ n₂ mm pp : ℕ}
    (Sys : FIESystem n₁ n₂ mm pp) (w : Fin n₁ ⊕ Fin n₂ → ℝ) :
    quadForm Sys.Jmat w
      = quadForm Sys.Sig₁ (FIESystem.blk₁ w)
        + quadForm Sys.Sig₂ (FIESystem.blk₂ w) := by
  unfold quadForm
  rw [Sys.Jmat_mulVec]
  simp [dotProduct, Fintype.sum_sum_type, FIESystem.blk₁,
    FIESystem.blk₂]

/-- The prior penalty transfers for feasible pairs. -/
lemma red_priorPenalty (hC2 : S.C2) {a e₀ : Fin n → ℝ}
    (h : S.Feasible a e₀) :
    S.redSys.priorPenalty (S.redT *ᵥ a) (S.redT *ᵥ e₀)
      = S.priorPen a e₀ := by
  obtain ⟨z, hz⟩ := h
  set zh := S.redTinvᵀ *ᵥ z with hzh
  have hd : S.redT *ᵥ e₀ - S.redT *ᵥ a = S.redSys.Jmat *ᵥ zh := by
    rw [S.redSys_Jmat_eq hC2, S.red_sub_param hz]
  unfold FIESystem.priorPenalty priorPen
  rw [hd, S.redSys.Jmat_mulVec]
  simp only [FIESystem.blk₁_sumElim, FIESystem.blk₂_sumElim]
  rw [quadForm_symmPinv_image S.redSys.hSig₁,
    quadForm_symmPinv_image S.redSys.hSig₂]
  have h2 : quadForm S.redSys.Sig₁ (FIESystem.blk₁ zh)
      + quadForm S.redSys.Sig₂ (FIESystem.blk₂ zh)
      = quadForm S.redSys.Jmat zh := (quadForm_Jmat S.redSys zh).symm
  rw [h2, show quadForm S.redSys.Jmat zh = quadForm S.redSig zh from by
    rw [S.redSys_Jmat_eq hC2]]
  rw [redSig_eq_congruence]
  have h3 : ∀ v : Fin S.rk1 ⊕ Fin S.rk2 → ℝ,
      quadForm (S.redT * S.Sig0 * S.redTᵀ) v
        = quadForm S.Sig0 (S.redTᵀ *ᵥ v) := fun v => by
    rw [quadForm_mulVec, Matrix.transpose_transpose]
  rw [h3 zh, hzh, Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    redTinv_mul_redT, Matrix.transpose_one, Matrix.one_mulVec, hz,
    quadForm_symmPinv_image S.hSig0]

/-- The full objective transfers. -/
lemma red_fieCost (hC2 : S.C2) {a e₀ : Fin n → ℝ}
    (h : S.Feasible a e₀) (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    S.redSys.fieCost (S.redT *ᵥ a) (S.redT *ᵥ e₀) ω T
      = S.gCost a e₀ ω T := by
  unfold FIESystem.fieCost gCost
  rw [red_priorPenalty S hC2 h, red_cost]

/-! ### Value and optimizer transfer -/

theorem red_value (hC2 : S.C2) (a : Fin n → ℝ) (T : ℕ) :
    S.redSys.value (S.redT *ᵥ a) T = S.value a T := by
  apply le_antisymm
  · have h1 := S.redSys.value_le_fieCost
      (S.red_feasible hC2 (S.optInit_feasible a T))
      (S.glq.optCtrl (S.optInit a T) T) T
    rwa [red_fieCost S hC2 (S.optInit_feasible a T),
      S.gCost_optCtrl] at h1
  · set eh := S.redSys.optInit (S.redT *ᵥ a) T with heh
    have hfe : S.Feasible a (S.redTinv *ᵥ eh) := by
      have h := S.red_feasible_rev hC2
        (S.redSys.optInit_feasible (S.redT *ᵥ a) T)
      rwa [redTinv_redT_mulVec] at h
    have h2 := S.value_le_gCost hfe
      (S.redSys.lq.optCtrl eh T) T
    have h3 := S.red_fieCost hC2 hfe (S.redSys.lq.optCtrl eh T) T
    rw [redT_redTinv_mulVec] at h3
    rw [← h3, S.redSys.fieCost_optCtrl] at h2
    exact h2

/-- The optimal initial errors correspond. -/
theorem red_optInit (hC2 : S.C2) (a : Fin n → ℝ) (T : ℕ) :
    S.redSys.optInit (S.redT *ᵥ a) T = S.redT *ᵥ S.optInit a T := by
  refine S.redSys.isStationary_unique
    (S.redSys.optInit_isStationary _ T) ?_
  obtain ⟨z, hz⟩ := S.optInit_feasible a T
  constructor
  · exact S.red_feasible hC2 (S.optInit_feasible a T)
  · intro d hd
    obtain ⟨w, hw⟩ := hd
    have hstat := (S.optInit_isStationary a T).2
      (S.Sig0 *ᵥ (S.redTᵀ *ᵥ w)) ⟨_, rfl⟩
    -- decompose the transported deviation and direction blockwise
    have hdev : S.redT *ᵥ S.optInit a T - S.redT *ᵥ a
        = S.redSys.Jmat *ᵥ (S.redTinvᵀ *ᵥ z) := by
      rw [S.redSys_Jmat_eq hC2, S.red_sub_param hz]
    rw [hdev, hw, S.redSys.Jmat_mulVec, S.redSys.Jmat_mulVec]
    simp only [FIESystem.blk₁_sumElim, FIESystem.blk₂_sumElim]
    rw [pinv_pairing S.redSys.hSig₁, pinv_pairing S.redSys.hSig₂]
    -- reassemble the two prior pairings into a Jmat pairing
    have hsum : (S.redSys.Sig₁ *ᵥ FIESystem.blk₁ (S.redTinvᵀ *ᵥ z))
          ⬝ᵥ FIESystem.blk₁ w
        + (S.redSys.Sig₂ *ᵥ FIESystem.blk₂ (S.redTinvᵀ *ᵥ z))
          ⬝ᵥ FIESystem.blk₂ w
        = (S.redSys.Jmat *ᵥ (S.redTinvᵀ *ᵥ z)) ⬝ᵥ w := by
      rw [S.redSys.Jmat_mulVec]
      simp [dotProduct, Fintype.sum_sum_type, FIESystem.blk₁,
        FIESystem.blk₂]
    -- the Jmat pairing equals the original prior pairing
    have hJ : (S.redSys.Jmat *ᵥ (S.redTinvᵀ *ᵥ z)) ⬝ᵥ w
        = (S.Sig0 *ᵥ z) ⬝ᵥ (S.redTᵀ *ᵥ w) := by
      rw [S.redSys_Jmat_eq hC2, redSig_eq_congruence,
        Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
        ← Matrix.transpose_mul, redTinv_mul_redT,
        Matrix.transpose_one, Matrix.mul_one,
        ← Matrix.mulVec_mulVec, mulVec_dotProduct_eq]
    -- the Riccati pairing equals the original one
    have hric : (S.redSys.lq.ric T *ᵥ (S.redT *ᵥ S.optInit a T))
          ⬝ᵥ (S.redSys.Jmat *ᵥ w)
        = (S.glq.ric T *ᵥ S.optInit a T)
          ⬝ᵥ (S.Sig0 *ᵥ (S.redTᵀ *ᵥ w)) := by
      rw [red_ric, Matrix.mulVec_mulVec,
        Matrix.mul_assoc (S.redTinvᵀ * S.glq.ric T),
        redTinv_mul_redT, Matrix.mul_one, ← Matrix.mulVec_mulVec,
        mulVec_dotProduct_eq, Matrix.transpose_transpose]
      congr 1
      rw [S.redSys_Jmat_eq hC2, redSig_eq_congruence,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      congr 1
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, redTinv_mul_redT,
        Matrix.one_mul]
    rw [hsum, hJ, ← S.redSys.Jmat_mulVec, hric]
    -- now exactly the general stationarity identity
    have hz' : S.optInit a T - a = S.Sig0 *ᵥ z := hz
    calc (S.Sig0 *ᵥ z) ⬝ᵥ (S.redTᵀ *ᵥ w)
          + (S.glq.ric T *ᵥ S.optInit a T)
            ⬝ᵥ (S.Sig0 *ᵥ (S.redTᵀ *ᵥ w))
        = (symmPinv S.hSig0.1 *ᵥ (S.optInit a T - a))
            ⬝ᵥ (S.Sig0 *ᵥ (S.redTᵀ *ᵥ w))
          + (S.glq.ric T *ᵥ S.optInit a T)
            ⬝ᵥ (S.Sig0 *ᵥ (S.redTᵀ *ᵥ w)) := by
          rw [hz', pinv_pairing S.hSig0]
      _ = 0 := hstat

/-! ### Terminal-error correspondence and stability transfer -/

open scoped Matrix.Norms.Operator

theorem red_optTerm (hC2 : S.C2) (a : Fin n → ℝ) (T : ℕ) :
    S.redSys.optTerm (S.redT *ᵥ a) T = S.redT *ᵥ S.optTerm a T := by
  unfold FIESystem.optTerm optTerm
  rw [red_optInit S hC2, red_optTraj]

/-- GAS transfers from the reduced system to the general one. -/
theorem isGAS_of_red (hC2 : S.C2) (h : S.redSys.IsGAS) : S.IsGAS := by
  obtain ⟨σ, hσ0, hσb⟩ := h
  refine ⟨fun T => ‖S.redTinv‖ * ‖S.redT‖ * max (σ T) 0, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun T => max (σ T) 0) Filter.atTop
        (nhds 0) := by
      have h2 := hσ0.max (tendsto_const_nhds (x := (0 : ℝ))
        (f := Filter.atTop (α := ℕ)))
      simpa using h2
    have h3 := h1.const_mul (‖S.redTinv‖ * ‖S.redT‖)
    simpa using h3
  · intro T a
    have h4 : S.optTerm a T
        = S.redTinv *ᵥ (S.redSys.optTerm (S.redT *ᵥ a) T) := by
      rw [red_optTerm S hC2, redTinv_redT_mulVec]
    rw [h4]
    have h5 := Matrix.linfty_opNorm_mulVec S.redTinv
      (S.redSys.optTerm (S.redT *ᵥ a) T)
    have h6 := hσb T (S.redT *ᵥ a)
    have h7 := Matrix.linfty_opNorm_mulVec S.redT a
    have h8 : ‖S.redSys.optTerm (S.redT *ᵥ a) T‖
        ≤ max (σ T) 0 * (‖S.redT‖ * ‖a‖) := by
      have h9 : σ T * ‖S.redT *ᵥ a‖ ≤ max (σ T) 0 * (‖S.redT‖ * ‖a‖) := by
        have h10 : σ T * ‖S.redT *ᵥ a‖
            ≤ max (σ T) 0 * ‖S.redT *ᵥ a‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        have h11 : max (σ T) 0 * ‖S.redT *ᵥ a‖
            ≤ max (σ T) 0 * (‖S.redT‖ * ‖a‖) :=
          mul_le_mul_of_nonneg_left h7 (le_max_right _ _)
        linarith
      linarith
    calc ‖S.redTinv *ᵥ S.redSys.optTerm (S.redT *ᵥ a) T‖
        ≤ ‖S.redTinv‖ * ‖S.redSys.optTerm (S.redT *ᵥ a) T‖ := h5
      _ ≤ ‖S.redTinv‖ * (max (σ T) 0 * (‖S.redT‖ * ‖a‖)) :=
          mul_le_mul_of_nonneg_left h8 (norm_nonneg _)
      _ = ‖S.redTinv‖ * ‖S.redT‖ * max (σ T) 0 * ‖a‖ := by ring

/-- GAS transfers from the general system to the reduced one. -/
theorem red_isGAS (hC2 : S.C2) (h : S.IsGAS) : S.redSys.IsGAS := by
  obtain ⟨σ, hσ0, hσb⟩ := h
  refine ⟨fun T => ‖S.redT‖ * ‖S.redTinv‖ * max (σ T) 0, ?_, ?_⟩
  · have h1 : Filter.Tendsto (fun T => max (σ T) 0) Filter.atTop
        (nhds 0) := by
      have h2 := hσ0.max (tendsto_const_nhds (x := (0 : ℝ))
        (f := Filter.atTop (α := ℕ)))
      simpa using h2
    have h3 := h1.const_mul (‖S.redT‖ * ‖S.redTinv‖)
    simpa using h3
  · intro T a'
    have h4 : S.redSys.optTerm a' T
        = S.redT *ᵥ S.optTerm (S.redTinv *ᵥ a') T := by
      have h5 := red_optTerm S hC2 (S.redTinv *ᵥ a') T
      rwa [redT_redTinv_mulVec] at h5
    rw [h4]
    have h5 := Matrix.linfty_opNorm_mulVec S.redT
      (S.optTerm (S.redTinv *ᵥ a') T)
    have h6 := hσb T (S.redTinv *ᵥ a')
    have h7 := Matrix.linfty_opNorm_mulVec S.redTinv a'
    have h8 : ‖S.optTerm (S.redTinv *ᵥ a') T‖
        ≤ max (σ T) 0 * (‖S.redTinv‖ * ‖a'‖) := by
      have h10 : σ T * ‖S.redTinv *ᵥ a'‖
          ≤ max (σ T) 0 * ‖S.redTinv *ᵥ a'‖ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
      have h11 : max (σ T) 0 * ‖S.redTinv *ᵥ a'‖
          ≤ max (σ T) 0 * (‖S.redTinv‖ * ‖a'‖) :=
        mul_le_mul_of_nonneg_left h7 (le_max_right _ _)
      linarith
    calc ‖S.redT *ᵥ S.optTerm (S.redTinv *ᵥ a') T‖
        ≤ ‖S.redT‖ * ‖S.optTerm (S.redTinv *ᵥ a') T‖ := h5
      _ ≤ ‖S.redT‖ * (max (σ T) 0 * (‖S.redTinv‖ * ‖a'‖)) :=
          mul_le_mul_of_nonneg_left h8 (norm_nonneg _)
      _ = ‖S.redT‖ * ‖S.redTinv‖ * max (σ T) 0 * ‖a'‖ := by ring

/-- GES transfers from the reduced system to the general one. -/
theorem isGES_of_red (hC2 : S.C2) (h : S.redSys.IsGES) : S.IsGES := by
  obtain ⟨c, ρ, hc, hρ0, hρ1, hb⟩ := h
  refine ⟨(‖S.redTinv‖ * ‖S.redT‖ + 1) * c, ρ, by positivity, hρ0,
    hρ1, ?_⟩
  intro T a
  have h4 : S.optTerm a T
      = S.redTinv *ᵥ (S.redSys.optTerm (S.redT *ᵥ a) T) := by
    rw [red_optTerm S hC2, redTinv_redT_mulVec]
  rw [h4]
  have h5 := Matrix.linfty_opNorm_mulVec S.redTinv
    (S.redSys.optTerm (S.redT *ᵥ a) T)
  have h6 := hb T (S.redT *ᵥ a)
  have h7 := Matrix.linfty_opNorm_mulVec S.redT a
  have hcρ : 0 ≤ c * ρ ^ T := by positivity
  calc ‖S.redTinv *ᵥ S.redSys.optTerm (S.redT *ᵥ a) T‖
      ≤ ‖S.redTinv‖ * ‖S.redSys.optTerm (S.redT *ᵥ a) T‖ := h5
    _ ≤ ‖S.redTinv‖ * (c * ρ ^ T * ‖S.redT *ᵥ a‖) :=
        mul_le_mul_of_nonneg_left h6 (norm_nonneg _)
    _ ≤ ‖S.redTinv‖ * (c * ρ ^ T * (‖S.redT‖ * ‖a‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left h7 hcρ
    _ ≤ (‖S.redTinv‖ * ‖S.redT‖ + 1) * c * ρ ^ T * ‖a‖ := by
        nlinarith [norm_nonneg a, norm_nonneg (S.redTinv),
          norm_nonneg (S.redT), pow_nonneg hρ0.le T, hc.le]

/-- GES transfers from the general system to the reduced one. -/
theorem red_isGES (hC2 : S.C2) (h : S.IsGES) : S.redSys.IsGES := by
  obtain ⟨c, ρ, hc, hρ0, hρ1, hb⟩ := h
  refine ⟨(‖S.redT‖ * ‖S.redTinv‖ + 1) * c, ρ, by positivity, hρ0,
    hρ1, ?_⟩
  intro T a'
  have h4 : S.redSys.optTerm a' T
      = S.redT *ᵥ S.optTerm (S.redTinv *ᵥ a') T := by
    have h5 := red_optTerm S hC2 (S.redTinv *ᵥ a') T
    rwa [redT_redTinv_mulVec] at h5
  rw [h4]
  have h5 := Matrix.linfty_opNorm_mulVec S.redT
    (S.optTerm (S.redTinv *ᵥ a') T)
  have h6 := hb T (S.redTinv *ᵥ a')
  have h7 := Matrix.linfty_opNorm_mulVec S.redTinv a'
  have hcρ : 0 ≤ c * ρ ^ T := by positivity
  calc ‖S.redT *ᵥ S.optTerm (S.redTinv *ᵥ a') T‖
      ≤ ‖S.redT‖ * ‖S.optTerm (S.redTinv *ᵥ a') T‖ := h5
    _ ≤ ‖S.redT‖ * (c * ρ ^ T * ‖S.redTinv *ᵥ a'‖) :=
        mul_le_mul_of_nonneg_left h6 (norm_nonneg _)
    _ ≤ ‖S.redT‖ * (c * ρ ^ T * (‖S.redTinv‖ * ‖a'‖)) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact mul_le_mul_of_nonneg_left h7 hcρ
    _ ≤ (‖S.redT‖ * ‖S.redTinv‖ + 1) * c * ρ ^ T * ‖a'‖ := by
        nlinarith [norm_nonneg a', norm_nonneg (S.redTinv),
          norm_nonneg (S.redT), pow_nonneg hρ0.le T, hc.le]

end GeneralSystem

end Estimation
