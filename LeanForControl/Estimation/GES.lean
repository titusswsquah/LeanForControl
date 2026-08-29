import LeanForControl.Estimation.GAS
import Architect

/-!
# The exponential track (`lem:val-rate`, `thm:ges-fi`)

The heart is the **gap bound** (`eq:gap-bound`), derived here
variationally — the cross-block `Y_T` of the paper never appears:
`V̄(a) - V_T⁰(a) ≤ ‖e₂*‖²_{Σ₂†} + ‖(0,e₂*)‖²_{P_T-full} + ‖x_T‖²_{P_∞}`,
where `e₂* = e₂*(0|T)` is the antistable block of the horizon-`T`
optimizer and `x_T` the endpoint of the block-1 optimal rollout.
-/

namespace Estimation

namespace FIESystem

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

variable {n₁ n₂ m p : ℕ} (Sys : FIESystem n₁ n₂ m p)

/-- Quadratic form of a block vector supported on the first block. -/
lemma quadForm_sumElim_zero_right {M : Matrix (Fin n₁ ⊕ Fin n₂)
    (Fin n₁ ⊕ Fin n₂) ℝ} (x : Fin n₁ → ℝ) :
    quadForm M (Sum.elim x 0) = quadForm M.toBlocks₁₁ x := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  rw [quadForm, Matrix.fromBlocks_mulVec, dotProduct_blocks]
  simp [quadForm, blk₁, blk₂, Sum.elim_comp_inl, Sum.elim_comp_inr]

/-- The optimal trajectory is the reverse product of closed-loop
factors. -/
lemma _root_.LinearSystems.LQSystem.optTraj_eq_revProd {d m' : ℕ}
    (S : LQSystem (Fin d) (Fin m')) (x : Fin d → ℝ) (T : ℕ) :
    ∀ k, k ≤ T →
      S.optTraj x T k = revProd (fun r => S.Acl (S.ric r)) (T - k) k *ᵥ x
  | 0, _ => by simp [LQSystem.optTraj]
  | k + 1, hk => by
    change S.Acl (S.ric (T - 1 - k)) *ᵥ S.optTraj x T k = _
    rw [S.optTraj_eq_revProd x T k (by omega), Matrix.mulVec_mulVec]
    congr 1
    have h1 : T - (k + 1) = T - 1 - k := by omega
    have h2 : T - 1 - k + 1 = T - k := by omega
    rw [revProd_succ, h1, h2]

/-- **The gap bound** (`eq:gap-bound`, variational form): the value gap
is controlled by the antistable block of the optimizer and the block-1
closed-loop endpoint — no cross block appears. -/
theorem gap_le_antistable_energy (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.valueLim a - Sys.value a T
      ≤ quadForm (symmPinv Sys.hSig₂.1) (blk₂ (Sys.optInit a T))
        + quadForm (Sys.lq.ric T)
            (Sum.elim 0 (blk₂ (Sys.optInit a T)))
        + quadForm (Sys.Pinf hC1)
            (Sys.lqRed.optTraj (blk₁ (Sys.optInit a T)) T T) := by
  classical
  set ξ := blk₁ (Sys.optInit a T) with hξ
  set e₂ := blk₂ (Sys.optInit a T) with he₂
  set xT := Sys.lqRed.optTraj ξ T T with hxT
  set e₀c : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim ξ 0 with he₀c
  set d : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim 0 e₂ with hd
  have hsum : Sys.optInit a T = e₀c + d := by
    rw [he₀c, hd]
    conv_lhs => rw [← sumElim_blk (Sys.optInit a T)]
    funext i
    cases i <;> simp [← hξ, ← he₂]
  -- the extended candidate control
  set ωc : ℕ → Fin m → ℝ := fun k =>
    if k < T then Sys.lqRed.optCtrl ξ T k
    else -(Sys.lqRed.gainK (Sys.Pinf hC1)
      *ᵥ (Sys.lqRed.Acl (Sys.Pinf hC1) ^ (k - T) *ᵥ xT)) with hωc
  -- Step 1: the candidate caps the limiting value
  have hstep1 : Sys.valueLim a
      ≤ Sys.priorPenalty a e₀c + quadForm (Sys.lqRed.ric T) ξ
        + quadForm (Sys.Pinf hC1) xT := by
    have hfeas : Sys.Feasible a e₀c := by
      constructor
      · obtain ⟨z, hz⟩ := (Sys.optInit_feasible a T).1
        refine ⟨z, ?_⟩
        have h1 : blk₁ (e₀c - a) = ξ - blk₁ a := by
          rw [blk₁_sub, he₀c]
          congr 1
        rw [h1, hξ, ← blk₁_sub]
        exact hz
      · refine ⟨Sys.Sig₂⁻¹ *ᵥ (-(blk₂ a)), ?_⟩
        have h1 : blk₂ (e₀c - a) = -(blk₂ a) := by
          rw [blk₂_sub, he₀c]
          funext i
          simp [blk₂]
        rw [h1, Matrix.mulVec_mulVec,
          Matrix.mul_nonsing_inv _
            (isUnit_iff_ne_zero.mpr hC2.det_pos.ne'),
          Matrix.one_mulVec]
    have hbnd : ∀ τ, T ≤ τ → Sys.value a τ
        ≤ Sys.priorPenalty a e₀c + quadForm (Sys.lqRed.ric T) ξ
          + quadForm (Sys.Pinf hC1) xT := by
      intro τ hτ
      have h1 := Sys.value_le_fieCost hfeas ωc τ
      have h2 : Sys.lq.cost e₀c ωc τ
          ≤ quadForm (Sys.lqRed.ric T) ξ
            + quadForm (Sys.Pinf hC1) xT := by
        have h3 : Sys.lq.cost e₀c ωc τ = Sys.lqRed.cost ξ ωc τ := by
          rw [he₀c, Sys.lq_cost_sumElim_zero]
        obtain ⟨M, hM⟩ : ∃ M, τ = T + M := ⟨τ - T, by omega⟩
        subst hM
        rw [h3, Sys.lqRed.cost_add]
        have h4 : Sys.lqRed.cost ξ ωc T
            = quadForm (Sys.lqRed.ric T) ξ := by
          rw [Sys.lqRed.cost_congr ξ (u' := Sys.lqRed.optCtrl ξ T)
            fun j hj => by rw [hωc]; simp [hj]]
          exact Sys.lqRed.cost_optCtrl ξ T
        have h5 : Sys.lqRed.traj ξ ωc T = xT := by
          rw [Sys.lqRed.traj_congr ξ (u' := Sys.lqRed.optCtrl ξ T)
            fun j hj => by rw [hωc]; simp [hj], Sys.lqRed.traj_optCtrl]
        have h6 : Sys.lqRed.cost (Sys.lqRed.traj ξ ωc T)
            (fun j => ωc (T + j)) M ≤ quadForm (Sys.Pinf hC1) xT := by
          rw [h5]
          have h7 : (fun j => ωc (T + j)) = fun j =>
              -(Sys.lqRed.gainK (Sys.Pinf hC1)
                *ᵥ (Sys.lqRed.Acl (Sys.Pinf hC1) ^ j *ᵥ xT)) := by
            funext j
            rw [hωc]
            have h8 : ¬(T + j < T) := by omega
            have h9 : T + j - T = j := by omega
            simp [h8, h9]
          rw [h7, Sys.lqRed.cost_fixedGain (Sys.Pinf_posSemidef hC1)
            (Sys.Pinf_fixed hC1)]
          have h10 := (Sys.Pinf_posSemidef hC1).quadForm_nonneg
            (Sys.lqRed.Acl (Sys.Pinf hC1) ^ M *ᵥ xT)
          linarith
        linarith [h6, h4]
      unfold fieCost at h1
      linarith
    refine le_of_tendsto (Sys.tendsto_value hC1 hC2 a) ?_
    filter_upwards [eventually_ge_atTop T] with τ hτ
    exact hbnd τ hτ
  -- Step 2: expand the horizon-`T` value at the optimizer
  have hexp : Sys.value a T
      = Sys.priorPenalty a (Sys.optInit a T)
        + quadForm (Sys.lqRed.ric T) ξ
        + 2 * (e₀c ⬝ᵥ (Sys.lq.ric T *ᵥ d))
        + quadForm (Sys.lq.ric T) d := by
    have h1 : Sys.value a T = Sys.priorPenalty a (Sys.optInit a T)
        + quadForm (Sys.lq.ric T) (Sys.optInit a T) := rfl
    rw [h1]
    have h2' : quadForm (Sys.lq.ric T) (Sys.optInit a T)
        = quadForm (Sys.lqRed.ric T) ξ
          + 2 * (e₀c ⬝ᵥ (Sys.lq.ric T *ᵥ d))
          + quadForm (Sys.lq.ric T) d := by
      conv_lhs => rw [hsum]
      rw [quadForm_add_of_isHermitian (Sys.lq.ric_isHermitian T)]
      have h2 : quadForm (Sys.lq.ric T) e₀c
          = quadForm (Sys.lqRed.ric T) ξ := by
        rw [he₀c, quadForm_sumElim_zero_right, Sys.ric_toBlocks₁₁]
      rw [h2]
    rw [h2']
    ring
  -- Step 3: the stationarity along the pure-antistable direction
  have hstat : e₀c ⬝ᵥ (Sys.lq.ric T *ᵥ d)
      = -((symmPinv Sys.hSig₂.1 *ᵥ blk₂ (Sys.optInit a T - a)) ⬝ᵥ e₂)
        - quadForm (Sys.lq.ric T) d := by
    obtain ⟨_, hvar⟩ := Sys.optInit_isStationary a T
    have hdir : Sys.FeasibleDir d := by
      refine ⟨Sum.elim 0 (Sys.Sig₂⁻¹ *ᵥ e₂), ?_⟩
      rw [Sys.Jmat_mulVec]
      have h1 : blk₁ (Sum.elim (0 : Fin n₁ → ℝ)
          (Sys.Sig₂⁻¹ *ᵥ e₂)) = 0 := rfl
      have h2 : blk₂ (Sum.elim (0 : Fin n₁ → ℝ)
          (Sys.Sig₂⁻¹ *ᵥ e₂)) = Sys.Sig₂⁻¹ *ᵥ e₂ := rfl
      rw [h1, h2, Matrix.mulVec_zero, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr hC2.det_pos.ne'),
        Matrix.one_mulVec, hd]
    have h3 := hvar d hdir
    have h4 : blk₁ d = 0 := rfl
    have h5 : blk₂ d = e₂ := rfl
    rw [h4, h5, dotProduct_zero] at h3
    -- split `(ric e*) ⬝ d` along `e* = e₀c + d`
    have h6 : (Sys.lq.ric T *ᵥ Sys.optInit a T) ⬝ᵥ d
        = (Sys.lq.ric T *ᵥ e₀c) ⬝ᵥ d + quadForm (Sys.lq.ric T) d := by
      conv_lhs => rw [hsum]
      rw [Matrix.mulVec_add, add_dotProduct]
      congr 1
      rw [quadForm]
      exact dotProduct_comm _ _
    have h7 : (Sys.lq.ric T *ᵥ e₀c) ⬝ᵥ d
        = e₀c ⬝ᵥ (Sys.lq.ric T *ᵥ d) := by
      rw [dotProduct_comm]
      exact dotProduct_mulVec_comm (Sys.lq.ric_isHermitian T) d e₀c
    rw [h6, h7] at h3
    linarith
  -- Step 4: assemble; the prior-difference bracket collapses
  have hprior : Sys.priorPenalty a e₀c
      - Sys.priorPenalty a (Sys.optInit a T)
      + 2 * ((symmPinv Sys.hSig₂.1
          *ᵥ blk₂ (Sys.optInit a T - a)) ⬝ᵥ e₂)
      = quadForm (symmPinv Sys.hSig₂.1) e₂ := by
    unfold priorPenalty
    have h1 : blk₁ (e₀c - a) = blk₁ (Sys.optInit a T - a) := by
      rw [blk₁_sub, blk₁_sub, he₀c]
      congr 1
    have h2 : blk₂ (e₀c - a) = blk₂ (Sys.optInit a T - a) - e₂ := by
      rw [blk₂_sub, blk₂_sub, he₀c]
      have h3 : blk₂ (Sum.elim ξ (0 : Fin n₂ → ℝ)) = 0 := rfl
      rw [h3, he₂]
      abel
    rw [h1, h2]
    set W := symmPinv Sys.hSig₂.1 with hW
    set x := blk₂ (Sys.optInit a T - a) with hx
    have h4 : quadForm W (x - e₂)
        = quadForm W x - 2 * (x ⬝ᵥ (W *ᵥ e₂)) + quadForm W e₂ := by
      have h5 : x - e₂ = x + (-e₂) := by abel
      rw [h5, quadForm_add_of_isHermitian (symmPinv_isHermitian _),
        quadForm_neg, Matrix.mulVec_neg, dotProduct_neg]
      ring
    have h6 : (W *ᵥ x) ⬝ᵥ e₂ = x ⬝ᵥ (W *ᵥ e₂) := by
      rw [dotProduct_comm]
      exact dotProduct_mulVec_comm (symmPinv_isHermitian _) e₂ x
    rw [h4, h6]
    ring
  have hgap := sub_le_sub hstep1 (le_of_eq hexp.symm)
  rw [hstat] at hgap
  linarith [hgap, hprior]

/-! ### The polynomial upper bracket (`eq:bracket`, upper half) -/

/-- Antistability makes `A₂` invertible. -/
lemma A₂_det_ne_zero : Sys.A₂.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : complexify Sys.A₂ *ᵥ complexifyVec v
      = (0 : ℂ) • complexifyVec v := by
    rw [complexify_mulVec, hv, zero_smul]
    funext i
    simp [complexifyVec]
  have h2 : complexifyVec v ≠ 0 := by
    intro h
    apply hvne
    funext i
    have h3 := congrFun h i
    simpa [complexifyVec] using h3
  have h4 := Sys.hAnti 0 (mem_spectrum_of_mulVec_eq_smul h2 h1)
  rw [norm_zero] at h4
  linarith

/-- The inverse antistable dynamics live in the closed unit disc. -/
lemma A₂_inv_spectrum_le_one :
    ∀ μ ∈ spectrum ℂ (complexify Sys.A₂⁻¹), ‖μ‖ ≤ 1 := by
  intro μ hμ
  rcases eq_or_ne μ 0 with h0 | hne
  · simp [h0]
  -- extract an eigenvector
  have hspec : μ ∈ spectrum ℂ (Matrix.toLin' (complexify Sys.A₂⁻¹)) := by
    rw [Matrix.spectrum_toLin']
    exact hμ
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    hspec).exists_hasEigenvector
  have hAv : complexify Sys.A₂⁻¹ *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  -- push through `A₂`
  have hunit : IsUnit Sys.A₂.det :=
    isUnit_iff_ne_zero.mpr Sys.A₂_det_ne_zero
  have hAAinv : complexify Sys.A₂ * complexify Sys.A₂⁻¹ = 1 := by
    rw [← complexify_mul, Matrix.mul_nonsing_inv _ hunit, complexify_one]
  have h1 : complexify Sys.A₂ *ᵥ (complexify Sys.A₂⁻¹ *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, hAAinv, Matrix.one_mulVec]
  rw [hAv, Matrix.mulVec_smul] at h1
  have h2 : complexify Sys.A₂ *ᵥ v = μ⁻¹ • v := by
    have h3 := congrArg (fun w => μ⁻¹ • w) h1
    simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h3
    exact h3
  have h4 := Sys.hAnti μ⁻¹
    (mem_spectrum_of_mulVec_eq_smul hv.2 h2)
  rw [norm_inv] at h4
  have h5 : 0 < ‖μ‖ := norm_pos_iff.mpr hne
  have h6 : ‖μ‖ * ‖μ‖⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h5)
  nlinarith

/-- Reconstructing early antistable states from the final one. -/
lemma pow_mulVec_eq_invPow (e₂ : Fin n₂ → ℝ) {j T : ℕ} (hj : j ≤ T) :
    Sys.A₂ ^ j *ᵥ e₂ = Sys.A₂⁻¹ ^ (T - j) *ᵥ (Sys.A₂ ^ T *ᵥ e₂) := by
  rw [Matrix.mulVec_mulVec]
  have hunit : IsUnit Sys.A₂.det :=
    isUnit_iff_ne_zero.mpr Sys.A₂_det_ne_zero
  have key : ∀ l j' : ℕ, Sys.A₂⁻¹ ^ l * Sys.A₂ ^ (l + j') = Sys.A₂ ^ j' := by
    intro l
    induction l with
    | zero => intro j'; simp
    | succ l ih =>
      intro j'
      have h1 : l + 1 + j' = (l + j') + 1 := by omega
      rw [h1, pow_succ, pow_succ']
      calc Sys.A₂⁻¹ ^ l * Sys.A₂⁻¹ * (Sys.A₂ * Sys.A₂ ^ (l + j'))
          = Sys.A₂⁻¹ ^ l * (Sys.A₂⁻¹ * Sys.A₂) * Sys.A₂ ^ (l + j') := by
            simp only [Matrix.mul_assoc]
      _ = Sys.A₂⁻¹ ^ l * Sys.A₂ ^ (l + j') := by
            rw [Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
      _ = Sys.A₂ ^ j' := ih j'
  congr 1
  have h2 : (T - j) + j = T := by omega
  have h3 := key (T - j) j
  rw [h2] at h3
  exact h3.symm

/-- A stabilizing state-feedback gain for the reduced pair `(A₁, G₁)`
(from the staged `detect_inj` by duality). -/
theorem exists_stabilizing_gain :
    ∃ Kt : Matrix (Fin m) (Fin n₁) ℝ,
      IsSchurStable (Sys.A₁ - Sys.G₁ * Kt) := by
  have hdet : IsDetectable (complexify Sys.A₁ᵀ) (complexify Sys.G₁ᵀ) := by
    rw [complexify_transpose, complexify_transpose]
    exact Sys.hStab
  obtain ⟨L, hL⟩ := detect_inj Sys.A₁ᵀ Sys.G₁ᵀ hdet
  refine ⟨Lᵀ, ?_⟩
  have h1 : (Sys.A₁ᵀ - L * Sys.G₁ᵀ)ᵀ = Sys.A₁ - Sys.G₁ * Lᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  have h2 := hL.transpose
  rwa [h1] at h2

/-- The stable block of the `K̃`-rollout from `(0, e₂)`. -/
noncomputable def rollE₁ (Kt : Matrix (Fin m) (Fin n₁) ℝ)
    (e₂ : Fin n₂ → ℝ) : ℕ → Fin n₁ → ℝ
  | 0 => 0
  | k + 1 => (Sys.A₁ - Sys.G₁ * Kt) *ᵥ rollE₁ Kt e₂ k
      + Sys.A₁₂ *ᵥ (Sys.A₂ ^ k *ᵥ e₂)

/-- The `K̃`-rollout is a genuine trajectory of the error system. -/
lemma traj_rollE₁ (Kt : Matrix (Fin m) (Fin n₁) ℝ)
    (e₂ : Fin n₂ → ℝ) : ∀ k,
    Sys.lq.traj (Sum.elim 0 e₂)
        (fun j => Kt *ᵥ Sys.rollE₁ Kt e₂ j) k
      = Sum.elim (Sys.rollE₁ Kt e₂ k) (Sys.A₂ ^ k *ᵥ e₂)
  | 0 => by
    funext i
    cases i with
    | inl i => rfl
    | inr i => simp
  | k + 1 => by
    rw [LQSystem.traj_succ, traj_rollE₁ Kt e₂ k, lq_A_eq, lq_B_eq]
    rw [Matrix.fromBlocks_mulVec]
    funext i
    cases i with
    | inl i =>
      simp only [Sum.elim_inl, Pi.add_apply, Matrix.neg_mulVec,
        Matrix.fromRows_mulVec, Pi.neg_apply, Sum.elim_inr]
      show (Sys.A₁ *ᵥ Sys.rollE₁ Kt e₂ k) i
          + (Sys.A₁₂ *ᵥ (Sys.A₂ ^ k *ᵥ e₂)) i
          + -((Sys.G₁ *ᵥ (Kt *ᵥ Sys.rollE₁ Kt e₂ k)) i)
        = Sys.rollE₁ Kt e₂ (k + 1) i
      show _ = ((Sys.A₁ - Sys.G₁ * Kt) *ᵥ Sys.rollE₁ Kt e₂ k
          + Sys.A₁₂ *ᵥ (Sys.A₂ ^ k *ᵥ e₂)) i
      rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    | inr i =>
      simp only [Sum.elim_inr, Pi.add_apply, Matrix.neg_mulVec,
        Matrix.fromRows_mulVec, Pi.neg_apply]
      show (0 *ᵥ Sys.rollE₁ Kt e₂ k) i
          + (Sys.A₂ *ᵥ (Sys.A₂ ^ k *ᵥ e₂)) i
          + -((0 *ᵥ (Kt *ᵥ Sys.rollE₁ Kt e₂ k)) i)
        = (Sys.A₂ ^ (k + 1) *ᵥ e₂) i
      rw [Matrix.mulVec_mulVec, ← pow_succ']
      simp [Matrix.zero_mulVec]

set_option maxHeartbeats 1000000 in
/-- **The polynomial upper bracket** (`eq:bracket`, upper half): the
antistable energy of the horizon-`T` value is at most polynomially
larger than the squared final antistable state. Needs neither C1 nor
C2. -/
theorem exists_upper_bracket :
    ∃ (c : ℝ) (q : ℕ), 0 < c ∧
      ∀ (e₂ : Fin n₂ → ℝ) (T : ℕ),
        quadForm (symmPinv Sys.hSig₂.1) e₂
          + quadForm (Sys.lq.ric T) (Sum.elim 0 e₂)
        ≤ c * ((1 + T : ℝ)) ^ q * ‖Sys.A₂ ^ T *ᵥ e₂‖ ^ 2 := by
  classical
  obtain ⟨Kt, hKt⟩ := Sys.exists_stabilizing_gain
  obtain ⟨cs, ρs, hcs, hρ0, hρ1, hpow⟩ := hKt.exists_pow_norm_le
  obtain ⟨cp, hcp, hpg⟩ :=
    pow_mulVec_le_poly Sys.A₂⁻¹ Sys.A₂_inv_spectrum_le_one
  obtain ⟨cQs, hcQs, hQs⟩ := exists_quadForm_le Sys.lq.Qs
  obtain ⟨cW, hcW, hW⟩ := exists_quadForm_le (symmPinv Sys.hSig₂.1)
  obtain ⟨cRu, hcRu, hRu⟩ := exists_quadForm_le Sys.lq.Ru
  set q := n₂ - 1 with hq
  -- a single stage-uniform bound on the rollout states
  set cE : ℝ := cs * ‖Sys.A₁₂‖ * cp * (1 - ρs)⁻¹ + cp + 1 with hcE
  have hρinv : 0 < (1 - ρs)⁻¹ := by
    rw [inv_pos]
    linarith
  have hcE0 : 0 < cE := by positivity
  refine ⟨cW * cp ^ 2
      + (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 + 1, 2 * q + 2,
    by positivity, ?_⟩
  intro e₂ T
  set eT := Sys.A₂ ^ T *ᵥ e₂ with heT
  have h1T : (0:ℝ) < 1 + T := by positivity
  -- free antistable states are polynomially bounded by the final one
  have hp2 : ∀ j ≤ T, ‖Sys.A₂ ^ j *ᵥ e₂‖
      ≤ cp * (1 + T : ℝ) ^ q * ‖eT‖ := by
    intro j hj
    rw [Sys.pow_mulVec_eq_invPow e₂ hj, ← heT]
    have h1 := hpg (T - j) eT
    have h2 : ((1 : ℝ) + (T - j : ℕ)) ^ q ≤ (1 + T : ℝ) ^ q := by
      have h3 : ((1 : ℝ) + (T - j : ℕ)) ≤ 1 + T := by
        have h4 : (T - j : ℕ) ≤ T := Nat.sub_le T j
        have h5 : ((T - j : ℕ) : ℝ) ≤ T := by exact_mod_cast h4
        linarith
      exact pow_le_pow_left₀ (by positivity) h3 q
    calc ‖Sys.A₂⁻¹ ^ (T - j) *ᵥ eT‖
        ≤ cp * ((1 : ℝ) + (T - j : ℕ)) ^ q * ‖eT‖ := h1
    _ ≤ cp * (1 + T : ℝ) ^ q * ‖eT‖ := by
        have h6 := norm_nonneg eT
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h2 hcp.le) h6
  -- the rollout's stable block is uniformly bounded on the horizon
  have hr : ∀ k ≤ T, ‖Sys.rollE₁ Kt e₂ k‖
      ≤ cE * (1 + T : ℝ) ^ q * ‖eT‖ := by
    intro k hk
    have hrec : ∀ j, Sys.rollE₁ Kt e₂ (j + 1)
        = (Sys.A₁ - Sys.G₁ * Kt) *ᵥ Sys.rollE₁ Kt e₂ j
          + (Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ e₂)) := fun j => rfl
    have hvc := varConst (Sys.A₁ - Sys.G₁ * Kt) (Sys.rollE₁ Kt e₂)
      (fun j => Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ e₂)) hrec k
    have h0 : Sys.rollE₁ Kt e₂ 0 = 0 := rfl
    rw [h0, Matrix.mulVec_zero, zero_add] at hvc
    rw [hvc]
    have h1 : ∀ j ∈ Finset.range k,
        ‖(Sys.A₁ - Sys.G₁ * Kt) ^ (k - 1 - j)
            *ᵥ (Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ e₂))‖
          ≤ cs * ρs ^ (k - 1 - j)
              * (‖Sys.A₁₂‖ * (cp * (1 + T : ℝ) ^ q * ‖eT‖)) := by
      intro j hj
      have h2 : ‖(Sys.A₁ - Sys.G₁ * Kt) ^ (k - 1 - j)
          *ᵥ (Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ e₂))‖
            ≤ ‖(Sys.A₁ - Sys.G₁ * Kt) ^ (k - 1 - j)‖
              * (‖Sys.A₁₂‖ * ‖Sys.A₂ ^ j *ᵥ e₂‖) := by
        refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact (Matrix.linfty_opNorm_mulVec _ _).trans le_rfl
      have h3 := hp2 j (le_trans (Finset.mem_range.mp hj).le hk)
      have h4 := hpow (k - 1 - j)
      have h6 := norm_nonneg (Sys.A₁₂)
      have h9 := norm_nonneg (Sys.A₂ ^ j *ᵥ e₂)
      refine h2.trans (mul_le_mul h4 (mul_le_mul_of_nonneg_left h3 h6)
        (mul_nonneg h6 h9) (mul_nonneg hcs.le (pow_nonneg hρ0.le _)))
    have h10 : ‖∑ j ∈ Finset.range k, (Sys.A₁ - Sys.G₁ * Kt) ^ (k - 1 - j)
        *ᵥ (Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ e₂))‖
          ≤ ∑ j ∈ Finset.range k, cs * ρs ^ (k - 1 - j)
              * (‖Sys.A₁₂‖ * (cp * (1 + T : ℝ) ^ q * ‖eT‖)) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum h1)
    have h11 : ∑ j ∈ Finset.range k, cs * ρs ^ (k - 1 - j)
        * (‖Sys.A₁₂‖ * (cp * (1 + T : ℝ) ^ q * ‖eT‖))
          ≤ cs * (1 - ρs)⁻¹
            * (‖Sys.A₁₂‖ * (cp * (1 + T : ℝ) ^ q * ‖eT‖)) := by
      have h12 : ∑ j ∈ Finset.range k, ρs ^ (k - 1 - j)
          ≤ (1 - ρs)⁻¹ := by
        rw [Finset.sum_range_reflect (fun j => ρs ^ j) k]
        have hpos : 0 < 1 - ρs := by linarith
        have hgs := geom_sum_eq (ne_of_lt hρ1) k
        have heq : (ρs ^ k - 1) / (ρs - 1) = (1 - ρs ^ k) / (1 - ρs) := by
          rw [show (1 - ρs ^ k) = -(ρs ^ k - 1) from by ring,
            show (1 - ρs) = -(ρs - 1) from by ring, neg_div_neg_eq]
        rw [hgs, heq, div_le_iff₀ hpos, inv_mul_cancel₀ (ne_of_gt hpos)]
        nlinarith [pow_pos hρ0 k]
      have h13 : (0:ℝ) ≤ ‖Sys.A₁₂‖ * (cp * (1 + T : ℝ) ^ q * ‖eT‖) := by
        have := norm_nonneg (Sys.A₁₂)
        have := norm_nonneg eT
        positivity
      calc ∑ j ∈ Finset.range k, cs * ρs ^ (k - 1 - j)
          * (‖Sys.A₁₂‖ * (cp * (1 + T : ℝ) ^ q * ‖eT‖))
          = cs * (∑ j ∈ Finset.range k, ρs ^ (k - 1 - j))
            * (‖Sys.A₁₂‖ * (cp * (1 + T : ℝ) ^ q * ‖eT‖)) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
      _ ≤ cs * (1 - ρs)⁻¹
            * (‖Sys.A₁₂‖ * (cp * (1 + T : ℝ) ^ q * ‖eT‖)) := by
            refine mul_le_mul_of_nonneg_right ?_ h13
            exact mul_le_mul_of_nonneg_left h12 hcs.le
    calc ‖∑ j ∈ Finset.range k, (Sys.A₁ - Sys.G₁ * Kt) ^ (k - 1 - j)
          *ᵥ (Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ e₂))‖
        ≤ cs * (1 - ρs)⁻¹
            * (‖Sys.A₁₂‖ * (cp * (1 + T : ℝ) ^ q * ‖eT‖)) :=
          le_trans h10 h11
    _ ≤ cE * (1 + T : ℝ) ^ q * ‖eT‖ := by
        rw [hcE]
        have h15 := norm_nonneg eT
        have h16 : (0:ℝ) < (1 + T : ℝ) ^ q := pow_pos h1T q
        nlinarith [mul_nonneg (mul_nonneg hcp.le h16.le) h15]
  -- assemble the cost of the rollout
  have hcost : quadForm (Sys.lq.ric T) (Sum.elim 0 e₂)
      ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
        * (1 + T : ℝ) ^ (2 * q + 1) * ‖eT‖ ^ 2 := by
    have h1 := Sys.lq.quadForm_ric_le_cost (Sum.elim 0 e₂)
      (fun j => Kt *ᵥ Sys.rollE₁ Kt e₂ j) T
    refine h1.trans ?_
    have h2 : Sys.lq.cost (Sum.elim 0 e₂)
        (fun j => Kt *ᵥ Sys.rollE₁ Kt e₂ j) T
          = ∑ k ∈ Finset.range T,
            (quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt e₂ k)
                (Sys.A₂ ^ k *ᵥ e₂))
              + quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt e₂ k)) := by
      unfold LQSystem.cost
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Sys.traj_rollE₁]
    rw [h2]
    have hstage : ∀ k ∈ Finset.range T,
        quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt e₂ k)
            (Sys.A₂ ^ k *ᵥ e₂))
          + quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt e₂ k)
        ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
            * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 := by
      intro k hk
      have hkT := (Finset.mem_range.mp hk).le
      have hrk := hr k hkT
      have hpk := hp2 k hkT
      have hcpE : cp ≤ cE := by
        rw [hcE]
        have h30 : (0:ℝ) ≤ cs * ‖Sys.A₁₂‖ * cp * (1 - ρs)⁻¹ := by
          positivity
        linarith
      have hpk' : ‖Sys.A₂ ^ k *ᵥ e₂‖ ≤ cE * (1 + T : ℝ) ^ q * ‖eT‖ := by
        refine hpk.trans ?_
        have h16 : (0:ℝ) ≤ (1 + T : ℝ) ^ q * ‖eT‖ :=
          mul_nonneg (pow_pos h1T q).le (norm_nonneg _)
        calc cp * (1 + T : ℝ) ^ q * ‖eT‖
            = cp * ((1 + T : ℝ) ^ q * ‖eT‖) := by ring
        _ ≤ cE * ((1 + T : ℝ) ^ q * ‖eT‖) :=
            mul_le_mul_of_nonneg_right hcpE h16
        _ = cE * (1 + T : ℝ) ^ q * ‖eT‖ := by ring
      set Y : ℝ := cE * (1 + T : ℝ) ^ q * ‖eT‖ with hY
      have hYnn : (0:ℝ) ≤ Y := by
        rw [hY]
        exact mul_nonneg (mul_nonneg hcE0.le (pow_pos h1T q).le)
          (norm_nonneg _)
      have hsum : ‖Sum.elim (Sys.rollE₁ Kt e₂ k)
          (Sys.A₂ ^ k *ᵥ e₂)‖ ≤ 2 * Y := by
        refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
        cases i with
        | inl i =>
          show ‖Sys.rollE₁ Kt e₂ k i‖ ≤ 2 * Y
          refine le_trans (norm_le_pi_norm _ i) (hrk.trans ?_)
          linarith
        | inr i =>
          show ‖(Sys.A₂ ^ k *ᵥ e₂) i‖ ≤ 2 * Y
          refine le_trans (norm_le_pi_norm _ i) (hpk'.trans ?_)
          linarith
      have hKtb : ‖Kt *ᵥ Sys.rollE₁ Kt e₂ k‖ ≤ ‖Kt‖ * Y := by
        refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
        rw [hY]
        exact mul_le_mul_of_nonneg_left hrk (norm_nonneg Kt)
      have hq1 : quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt e₂ k)
          (Sys.A₂ ^ k *ᵥ e₂)) ≤ cQs * (2 * Y) ^ 2 :=
        (hQs _).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hsum 2) hcQs.le)
      have hq2 : quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt e₂ k)
          ≤ cRu * (‖Kt‖ * Y) ^ 2 :=
        (hRu _).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hKtb 2) hcRu.le)
      have h23 : Y ^ 2 = cE ^ 2 * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 := by
        rw [hY, mul_pow, mul_pow, ← pow_mul, mul_comm q 2]
      calc quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt e₂ k)
            (Sys.A₂ ^ k *ᵥ e₂))
          + quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt e₂ k)
          ≤ cQs * (2 * Y) ^ 2 + cRu * (‖Kt‖ * Y) ^ 2 := add_le_add hq1 hq2
      _ ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * Y ^ 2 := by
          nlinarith [sq_nonneg Y, sq_nonneg ‖Kt‖, sq_nonneg (‖Kt‖ * Y),
            mul_nonneg hcRu.le (sq_nonneg (‖Kt‖ * Y))]
      _ = (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
            * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 := by
          rw [h23]
          ring
    calc ∑ k ∈ Finset.range T,
        (quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt e₂ k)
            (Sys.A₂ ^ k *ᵥ e₂))
          + quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt e₂ k))
        ≤ ∑ _k ∈ Finset.range T,
          (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
            * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 :=
          Finset.sum_le_sum hstage
    _ = T * ((cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
          * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
          * (1 + T : ℝ) ^ (2 * q + 1) * ‖eT‖ ^ 2 := by
        have h24 : (T:ℝ) ≤ (1 + T : ℝ) := by linarith
        have h25 : (1 + T : ℝ) ^ (2 * q + 1)
            = (1 + T : ℝ) ^ (2 * q) * (1 + T : ℝ) := by
          rw [pow_succ]
        rw [h25]
        have h26 : (0:ℝ) ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 := by
          have h26b : (0:ℝ) ≤ cRu * ‖Kt‖ ^ 2 :=
            mul_nonneg hcRu.le (sq_nonneg _)
          exact mul_nonneg (by linarith) (sq_nonneg cE)
        have h27 : (0:ℝ) ≤ (1 + T : ℝ) ^ (2 * q) := by positivity
        have h28 : (0:ℝ) ≤ ‖eT‖ ^ 2 := sq_nonneg _
        have hW0 : (0:ℝ) ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
            * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 :=
          mul_nonneg (mul_nonneg h26 h27) h28
        have h31 := mul_le_mul_of_nonneg_right h24 hW0
        have h32 : (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
            * ((1 + T : ℝ) ^ (2 * q) * (1 + T : ℝ)) * ‖eT‖ ^ 2
            = (1 + T : ℝ) * ((cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
              * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2) := by ring
        rw [h32]
        have h33 : (T : ℝ) * ((cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
            * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2)
            = (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
              * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 * (T : ℝ) := by ring
        have h34 : (1 + T : ℝ) * ((cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
            * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2)
            = (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
              * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 * (1 + T : ℝ) := by ring
        rw [h33, h34]
        exact mul_le_mul_of_nonneg_left h24 hW0
  -- the prior part
  have hprior : quadForm (symmPinv Sys.hSig₂.1) e₂
      ≤ cW * cp ^ 2 * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 := by
    have h1 := hW e₂
    have h2 : ‖e₂‖ ≤ cp * (1 + T : ℝ) ^ q * ‖eT‖ := by
      have h3 := hp2 0 (Nat.zero_le T)
      simpa using h3
    have h4 : ‖e₂‖ ^ 2 ≤ (cp * (1 + T : ℝ) ^ q * ‖eT‖) ^ 2 := by
      have := norm_nonneg e₂
      nlinarith
    have h5 : (cp * (1 + T : ℝ) ^ q * ‖eT‖) ^ 2
        = cp ^ 2 * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 := by
      rw [mul_pow, mul_pow, ← pow_mul, mul_comm q 2]
    calc quadForm (symmPinv Sys.hSig₂.1) e₂ ≤ cW * ‖e₂‖ ^ 2 := h1
    _ ≤ cW * (cp * (1 + T : ℝ) ^ q * ‖eT‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 hcW.le
    _ = cW * cp ^ 2 * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2 := by
        rw [h5]
        ring
  -- combine
  have hmono1 : (1 + T : ℝ) ^ (2 * q) ≤ (1 + T : ℝ) ^ (2 * q + 2) := by
    refine pow_le_pow_right₀ (by linarith) (by omega)
  have hmono2 : (1 + T : ℝ) ^ (2 * q + 1) ≤ (1 + T : ℝ) ^ (2 * q + 2) := by
    refine pow_le_pow_right₀ (by linarith) (by omega)
  have hA := sq_nonneg ‖eT‖
  have hB : (0:ℝ) ≤ cW * cp ^ 2 := by positivity
  have hC : (0:ℝ) ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 := by
    have hCb : (0:ℝ) ≤ cRu * ‖Kt‖ ^ 2 := mul_nonneg hcRu.le (sq_nonneg _)
    exact mul_nonneg (by linarith) (sq_nonneg cE)
  have hD : (0:ℝ) ≤ (1 + T : ℝ) ^ (2 * q + 2) := by positivity
  have hfin1 : cW * cp ^ 2 * (1 + T : ℝ) ^ (2 * q) * ‖eT‖ ^ 2
      ≤ cW * cp ^ 2 * (1 + T : ℝ) ^ (2 * q + 2) * ‖eT‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono1 hB) hA
  have hfin2 : (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
        * (1 + T : ℝ) ^ (2 * q + 1) * ‖eT‖ ^ 2
      ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
        * (1 + T : ℝ) ^ (2 * q + 2) * ‖eT‖ ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono2 hC) hA
  have hexp : (cW * cp ^ 2 + (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 + 1)
      * (1 + T : ℝ) ^ (2 * q + 2) * ‖eT‖ ^ 2
      = cW * cp ^ 2 * (1 + T : ℝ) ^ (2 * q + 2) * ‖eT‖ ^ 2
        + (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2
            * (1 + T : ℝ) ^ (2 * q + 2) * ‖eT‖ ^ 2
        + (1 + T : ℝ) ^ (2 * q + 2) * ‖eT‖ ^ 2 := by ring
  have hE : (0:ℝ) ≤ (1 + T : ℝ) ^ (2 * q + 2) * ‖eT‖ ^ 2 :=
    mul_nonneg hD hA
  rw [hexp]
  linarith [hprior, hcost, hfin1, hfin2]

end FIESystem

end Estimation
