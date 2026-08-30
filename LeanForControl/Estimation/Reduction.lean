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

end GeneralSystem

end Estimation
