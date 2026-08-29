import LeanForControl.Estimation.GAS
import Architect

set_option linter.style.show false

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
        Matrix.fromRows_mulVec, Pi.neg_apply]
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
-- the rollout norm chains at every stage make this proof elaboration-heavy
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

/-! ### The harmonic gap floor (`lem:val-rate`(2)) -/

/-- For a positive definite matrix the symmetric pseudoinverse is a
genuine left inverse. -/
lemma _root_.LinearSystems.posDef_symmPinv_mul_self {k : ℕ}
    {P : Matrix (Fin k) (Fin k) ℝ} (hP : P.PosDef) :
    symmPinv hP.1 * P = 1 := by
  have hunit : IsUnit P.det := isUnit_iff_ne_zero.mpr (ne_of_gt hP.det_pos)
  calc symmPinv hP.1 * P = 1 * (symmPinv hP.1 * P) :=
        (Matrix.one_mul _).symm
  _ = P⁻¹ * P * (symmPinv hP.1 * P) := by
      rw [Matrix.nonsing_inv_mul _ hunit]
  _ = P⁻¹ * (P * symmPinv hP.1 * P) := by
      simp only [Matrix.mul_assoc]
  _ = P⁻¹ * P := by rw [self_mul_symmPinv_mul_self hP.1]
  _ = 1 := Matrix.nonsing_inv_mul _ hunit

/-- Cost of the `K̃`-rollout under a uniform orbit bound: linear in the
horizon. -/
theorem exists_rollout_cost_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ (u : Fin n₂ → ℝ) (b : ℝ) (T : ℕ), 0 ≤ b →
      (∀ k, ‖Sys.A₂ ^ k *ᵥ u‖ ≤ b) →
      quadForm (Sys.lq.ric T) (Sum.elim 0 u)
        ≤ c * (1 + T : ℝ) * b ^ 2 := by
  classical
  obtain ⟨Kt, hKt⟩ := Sys.exists_stabilizing_gain
  obtain ⟨cs, ρs, hcs, hρ0, hρ1, hpow⟩ := hKt.exists_pow_norm_le
  obtain ⟨cQs, hcQs, hQs⟩ := exists_quadForm_le Sys.lq.Qs
  obtain ⟨cRu, hcRu, hRu⟩ := exists_quadForm_le Sys.lq.Ru
  set cE : ℝ := cs * ‖Sys.A₁₂‖ * (1 - ρs)⁻¹ + 1 with hcE
  have hρinv : 0 < (1 - ρs)⁻¹ := by
    rw [inv_pos]
    linarith
  have hcE0 : 0 < cE := by positivity
  refine ⟨(cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2, ?_, ?_⟩
  · have hb : (0:ℝ) ≤ cRu * ‖Kt‖ ^ 2 := mul_nonneg hcRu.le (sq_nonneg _)
    have hc : (0:ℝ) < cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2 := by linarith
    exact mul_pos hc (pow_pos hcE0 2)
  intro u b T hb horb
  -- the rollout's stable block is uniformly bounded
  have hr : ∀ k, ‖Sys.rollE₁ Kt u k‖ ≤ cE * b := by
    intro k
    have hrec : ∀ j, Sys.rollE₁ Kt u (j + 1)
        = (Sys.A₁ - Sys.G₁ * Kt) *ᵥ Sys.rollE₁ Kt u j
          + (Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ u)) := fun j => rfl
    have hvc := varConst (Sys.A₁ - Sys.G₁ * Kt) (Sys.rollE₁ Kt u)
      (fun j => Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ u)) hrec k
    have h0 : Sys.rollE₁ Kt u 0 = 0 := rfl
    rw [h0, Matrix.mulVec_zero, zero_add] at hvc
    rw [hvc]
    have h1 : ∀ j ∈ Finset.range k,
        ‖(Sys.A₁ - Sys.G₁ * Kt) ^ (k - 1 - j)
            *ᵥ (Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ u))‖
          ≤ cs * ρs ^ (k - 1 - j) * (‖Sys.A₁₂‖ * b) := by
      intro j _
      have h2 : ‖(Sys.A₁ - Sys.G₁ * Kt) ^ (k - 1 - j)
          *ᵥ (Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ u))‖
            ≤ ‖(Sys.A₁ - Sys.G₁ * Kt) ^ (k - 1 - j)‖
              * (‖Sys.A₁₂‖ * ‖Sys.A₂ ^ j *ᵥ u‖) := by
        refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
        exact mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mulVec _ _)
          (norm_nonneg _)
      refine h2.trans (mul_le_mul (hpow _)
        (mul_le_mul_of_nonneg_left (horb j) (norm_nonneg _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg hcs.le (pow_nonneg hρ0.le _)))
    have h10 : ‖∑ j ∈ Finset.range k, (Sys.A₁ - Sys.G₁ * Kt) ^ (k - 1 - j)
        *ᵥ (Sys.A₁₂ *ᵥ (Sys.A₂ ^ j *ᵥ u))‖
          ≤ ∑ j ∈ Finset.range k,
            cs * ρs ^ (k - 1 - j) * (‖Sys.A₁₂‖ * b) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum h1)
    have h12 : ∑ j ∈ Finset.range k, ρs ^ (k - 1 - j) ≤ (1 - ρs)⁻¹ := by
      rw [Finset.sum_range_reflect (fun j => ρs ^ j) k]
      have hpos : 0 < 1 - ρs := by linarith
      have hgs := geom_sum_eq (ne_of_lt hρ1) k
      have heq : (ρs ^ k - 1) / (ρs - 1) = (1 - ρs ^ k) / (1 - ρs) := by
        rw [show (1 - ρs ^ k) = -(ρs ^ k - 1) from by ring,
          show (1 - ρs) = -(ρs - 1) from by ring, neg_div_neg_eq]
      rw [hgs, heq, div_le_iff₀ hpos, inv_mul_cancel₀ (ne_of_gt hpos)]
      nlinarith [pow_pos hρ0 k]
    have h13 : (0:ℝ) ≤ ‖Sys.A₁₂‖ * b :=
      mul_nonneg (norm_nonneg _) hb
    have h11 : ∑ j ∈ Finset.range k,
        cs * ρs ^ (k - 1 - j) * (‖Sys.A₁₂‖ * b)
          ≤ cs * (1 - ρs)⁻¹ * (‖Sys.A₁₂‖ * b) := by
      calc ∑ j ∈ Finset.range k, cs * ρs ^ (k - 1 - j) * (‖Sys.A₁₂‖ * b)
          = cs * (∑ j ∈ Finset.range k, ρs ^ (k - 1 - j))
            * (‖Sys.A₁₂‖ * b) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
      _ ≤ cs * (1 - ρs)⁻¹ * (‖Sys.A₁₂‖ * b) := by
            refine mul_le_mul_of_nonneg_right ?_ h13
            exact mul_le_mul_of_nonneg_left h12 hcs.le
    refine (h10.trans h11).trans ?_
    rw [hcE]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hcs.le
      (norm_nonneg Sys.A₁₂)) hρinv.le) hb]
  -- stage costs are bounded, and there are `T` of them
  have h1 := Sys.lq.quadForm_ric_le_cost (Sum.elim 0 u)
    (fun j => Kt *ᵥ Sys.rollE₁ Kt u j) T
  refine h1.trans ?_
  have h2 : Sys.lq.cost (Sum.elim 0 u)
      (fun j => Kt *ᵥ Sys.rollE₁ Kt u j) T
        = ∑ k ∈ Finset.range T,
          (quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt u k)
              (Sys.A₂ ^ k *ᵥ u))
            + quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt u k)) := by
    unfold LQSystem.cost
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Sys.traj_rollE₁]
  rw [h2]
  set Y : ℝ := cE * b with hY
  have hYnn : (0:ℝ) ≤ Y := mul_nonneg hcE0.le hb
  have hstage : ∀ k ∈ Finset.range T,
      quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt u k)
          (Sys.A₂ ^ k *ᵥ u))
        + quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt u k)
      ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 * b ^ 2 := by
    intro k _
    have hrk := hr k
    have hbE : b ≤ cE * b := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hcs.le
        (norm_nonneg Sys.A₁₂)) hρinv.le) hb]
    have hsum : ‖Sum.elim (Sys.rollE₁ Kt u k) (Sys.A₂ ^ k *ᵥ u)‖
        ≤ 2 * Y := by
      refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun i => ?_
      cases i with
      | inl i =>
        show ‖Sys.rollE₁ Kt u k i‖ ≤ 2 * Y
        refine le_trans (norm_le_pi_norm _ i) (hrk.trans ?_)
        linarith
      | inr i =>
        show ‖(Sys.A₂ ^ k *ᵥ u) i‖ ≤ 2 * Y
        refine le_trans (norm_le_pi_norm _ i)
          ((horb k).trans (hbE.trans ?_))
        rw [hY]
        linarith
    have hKtb : ‖Kt *ᵥ Sys.rollE₁ Kt u k‖ ≤ ‖Kt‖ * Y := by
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      rw [hY]
      exact mul_le_mul_of_nonneg_left hrk (norm_nonneg Kt)
    have hq1 : quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt u k)
        (Sys.A₂ ^ k *ᵥ u)) ≤ cQs * (2 * Y) ^ 2 :=
      (hQs _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hsum 2) hcQs.le)
    have hq2 : quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt u k)
        ≤ cRu * (‖Kt‖ * Y) ^ 2 :=
      (hRu _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hKtb 2) hcRu.le)
    have h23 : Y ^ 2 = cE ^ 2 * b ^ 2 := by
      rw [hY, mul_pow]
    calc quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt u k)
          (Sys.A₂ ^ k *ᵥ u))
        + quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt u k)
        ≤ cQs * (2 * Y) ^ 2 + cRu * (‖Kt‖ * Y) ^ 2 := add_le_add hq1 hq2
    _ ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * Y ^ 2 := by
        nlinarith [sq_nonneg Y, sq_nonneg ‖Kt‖,
          mul_nonneg hcRu.le (sq_nonneg (‖Kt‖ * Y))]
    _ = (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 * b ^ 2 := by
        rw [h23]
        ring
  calc ∑ k ∈ Finset.range T,
      (quadForm Sys.lq.Qs (Sum.elim (Sys.rollE₁ Kt u k)
          (Sys.A₂ ^ k *ᵥ u))
        + quadForm Sys.lq.Ru (Kt *ᵥ Sys.rollE₁ Kt u k))
      ≤ ∑ _k ∈ Finset.range T,
        (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 * b ^ 2 :=
        Finset.sum_le_sum hstage
  _ = T * ((cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 * b ^ 2) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  _ ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 * (1 + T : ℝ) * b ^ 2 := by
      have h24 : (T : ℝ) ≤ 1 + T := by linarith
      have h26b : (0:ℝ) ≤ cRu * ‖Kt‖ ^ 2 :=
        mul_nonneg hcRu.le (sq_nonneg _)
      have h26 : (0:ℝ) ≤ (cQs * 4 + cRu * ‖Kt‖ ^ 2 * 2) * cE ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg cE)
      nlinarith [mul_nonneg h26 (sq_nonneg b)]

/-- **`lem:val-rate`(2)**: without C3w, the value gap closes no faster
than harmonically — a unit-circle mode keeps `1/(1+T)` of the budget
out of reach at every horizon. -/
theorem exists_gap_floor_of_not_C3w (hC1 : Sys.C1) (hC2 : Sys.C2)
    (hnc3 : ¬Sys.C3w) :
    ∃ (a : Fin n₁ ⊕ Fin n₂ → ℝ) (c' : ℝ), a ≠ 0 ∧ 0 < c' ∧
      ∀ T : ℕ, c' / (1 + T : ℝ) ≤ Sys.valueLim a - Sys.value a T := by
  classical
  -- a unit-circle eigenvalue and a bounded real direction
  rw [C3w] at hnc3
  push Not at hnc3
  obtain ⟨μ, hμmem, hμle⟩ := hnc3
  have hμ1 : ‖μ‖ = 1 := le_antisymm hμle (Sys.hAnti μ hμmem)
  have hspec : μ ∈ spectrum ℂ (Matrix.toLin' (complexify Sys.A₂)) := by
    rw [Matrix.spectrum_toLin']
    exact hμmem
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    hspec).exists_hasEigenvector
  have hAv : complexify Sys.A₂ *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  have heig : ∀ k, (complexify Sys.A₂) ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
        hAv, smul_smul, ← pow_succ]
  -- pick a nonzero real direction from the eigenvector
  set vr : Fin n₂ → ℝ := fun i => (v i).re with hvr
  set vi : Fin n₂ → ℝ := fun i => (v i).im with hvi
  have horb : ∀ (u : Fin n₂ → ℝ), (u = vr ∨ u = vi) → ∀ k,
      ‖Sys.A₂ ^ k *ᵥ u‖ ≤ ‖v‖ := by
    rintro u hu k
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr fun i => ?_
    have h1 : ((complexify Sys.A₂ ^ k *ᵥ v) i) = μ ^ k * v i := by
      rw [heig k]
      rfl
    have h2 : ‖μ ^ k * v i‖ = ‖v i‖ := by
      rw [norm_mul, norm_pow, hμ1, one_pow, one_mul]
    have h3 : ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
    rcases hu with rfl | rfl
    · have h4 : (Sys.A₂ ^ k *ᵥ vr) i
          = ((complexify Sys.A₂ ^ k *ᵥ v) i).re := by
        rw [← complexify_pow]
        exact (complexify_mulVec_re _ v i).symm
      rw [h4, h1]
      calc ‖(μ ^ k * v i).re‖ ≤ ‖μ ^ k * v i‖ := by
            rw [Real.norm_eq_abs]
            exact Complex.abs_re_le_norm _
      _ ≤ ‖v‖ := by rw [h2]; exact h3
    · have h4 : (Sys.A₂ ^ k *ᵥ vi) i
          = ((complexify Sys.A₂ ^ k *ᵥ v) i).im := by
        rw [← complexify_pow]
        exact (complexify_mulVec_im _ v i).symm
      rw [h4, h1]
      calc ‖(μ ^ k * v i).im‖ ≤ ‖μ ^ k * v i‖ := by
            rw [Real.norm_eq_abs]
            exact Complex.abs_im_le_norm _
      _ ≤ ‖v‖ := by rw [h2]; exact h3
  obtain ⟨u, hu, hune⟩ : ∃ u : Fin n₂ → ℝ,
      (u = vr ∨ u = vi) ∧ u ≠ 0 := by
    by_contra hno
    push Not at hno
    have h1 : vr = 0 := hno vr (Or.inl rfl)
    have h2 : vi = 0 := hno vi (Or.inr rfl)
    apply hv.2
    funext i
    have h3 : (v i).re = 0 := congrFun h1 i
    have h4 : (v i).im = 0 := congrFun h2 i
    exact Complex.ext h3 h4
  have horbu : ∀ k, ‖Sys.A₂ ^ k *ᵥ u‖ ≤ ‖v‖ := horb u hu
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
  -- the adversarial prior mismatch
  set a : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim 0 (Sys.Sig₂ *ᵥ u) with ha
  have hane : a ≠ 0 := by
    intro h0
    apply hune
    have h1 : Sys.Sig₂ *ᵥ u = 0 := by
      have h2 : blk₂ a = Sys.Sig₂ *ᵥ u := rfl
      rw [h0] at h2
      exact h2.symm.trans rfl
    have h3 : quadForm Sys.Sig₂ u = 0 := by
      rw [quadForm, h1, dotProduct_zero]
    by_contra hune'
    exact absurd h3 (ne_of_gt (hC2.quadForm_pos hune'))
  -- the limiting value keeps the whole antistable budget
  have hVbar : quadForm Sys.Sig₂ u ≤ Sys.valueLim a := by
    rw [Sys.valueLim_eq_valueInf hC1 hC2 a]
    unfold valueInf
    have h1 := Sys.hSig₁.symmPinv.quadForm_nonneg
      (Sys.xiInf hC1 a - blk₁ a)
    have h2 := (Sys.Pinf_posSemidef hC1).quadForm_nonneg (Sys.xiInf hC1 a)
    have h3 : blk₂ a = Sys.Sig₂ *ᵥ u := rfl
    rw [h3, quadForm_symmPinv_image Sys.hSig₂]
    linarith
  -- the scaled antistable candidate spends `2t‖u‖² - t²B_T` of it
  obtain ⟨cB, hcB, hroll⟩ := Sys.exists_rollout_cost_bound
  obtain ⟨cW, hcW, hW⟩ := exists_quadForm_le (symmPinv Sys.hSig₂.1)
  set B : ℕ → ℝ := fun T => quadForm (symmPinv Sys.hSig₂.1) u
    + quadForm (Sys.lq.ric T) (Sum.elim 0 u) with hB
  have hWinv : symmPinv Sys.hSig₂.1 *ᵥ (Sys.Sig₂ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, posDef_symmPinv_mul_self hC2,
      Matrix.one_mulVec]
  have hBpos : ∀ T, 0 < B T := by
    intro T
    have h1 : 0 < quadForm (symmPinv Sys.hSig₂.1) u := by
      have h2 : quadForm (symmPinv Sys.hSig₂.1) u
          = u ⬝ᵥ (symmPinv Sys.hSig₂.1 *ᵥ u) := rfl
      have h3 : u = Sys.Sig₂ *ᵥ (Sys.Sig₂⁻¹ *ᵥ u) := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          (isUnit_iff_ne_zero.mpr hC2.det_pos.ne'), Matrix.one_mulVec]
      have h4 : quadForm (symmPinv Sys.hSig₂.1) u
          = quadForm Sys.Sig₂ (Sys.Sig₂⁻¹ *ᵥ u) := by
        conv_lhs => rw [h3]
        exact quadForm_symmPinv_image Sys.hSig₂ _
      rw [h4]
      refine hC2.quadForm_pos ?_
      intro h5
      apply hune
      rw [h3, h5, Matrix.mulVec_zero]
    have h6 := (Sys.lq.ric_posSemidef T).quadForm_nonneg (Sum.elim 0 u)
    rw [hB]
    linarith
  have hval : ∀ T, Sys.value a T
      ≤ quadForm Sys.Sig₂ u - (u ⬝ᵥ u) ^ 2 / B T := by
    intro T
    set t : ℝ := (u ⬝ᵥ u) / B T with ht
    -- the candidate `(0, t•u)`
    set e₀t : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim 0 (t • u) with he₀t
    have hfeas : Sys.Feasible a e₀t := by
      constructor
      · refine ⟨0, ?_⟩
        rw [Matrix.mulVec_zero, blk₁_sub]
        have h6a : blk₁ e₀t = 0 := rfl
        have h6b : blk₁ a = 0 := rfl
        rw [h6a, h6b, sub_self]
      · refine ⟨t • (Sys.Sig₂⁻¹ *ᵥ u) - u, ?_⟩
        have h1 : blk₂ (e₀t - a) = t • u - Sys.Sig₂ *ᵥ u := by
          rw [blk₂_sub]
          rfl
        rw [h1, Matrix.mulVec_sub, Matrix.mulVec_smul,
          Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
            (isUnit_iff_ne_zero.mpr hC2.det_pos.ne'), Matrix.one_mulVec]
      -- feasible
    have h1 := Sys.value_le_fieCost hfeas (Sys.lq.optCtrl e₀t T) T
    have h2 : Sys.fieCost a e₀t (Sys.lq.optCtrl e₀t T) T
        = Sys.priorPenalty a e₀t + quadForm (Sys.lq.ric T) e₀t := by
      unfold fieCost
      rw [Sys.lq.cost_optCtrl]
    have h3 : quadForm (Sys.lq.ric T) e₀t
        = t ^ 2 * quadForm (Sys.lq.ric T) (Sum.elim 0 u) := by
      have h4 : e₀t = t • (Sum.elim 0 u : Fin n₁ ⊕ Fin n₂ → ℝ) := by
        funext i
        cases i with
        | inl i => exact (mul_zero t).symm
        | inr i => rfl
      rw [h4, quadForm_smul]
    have h5 : Sys.priorPenalty a e₀t
        = t ^ 2 * quadForm (symmPinv Sys.hSig₂.1) u
          - 2 * t * (u ⬝ᵥ u) + quadForm Sys.Sig₂ u := by
      unfold priorPenalty
      have h6 : blk₁ (e₀t - a) = 0 := by
        rw [blk₁_sub]
        have h6a : blk₁ e₀t = 0 := rfl
        have h6b : blk₁ a = 0 := rfl
        rw [h6a, h6b, sub_self]
      have h7 : blk₂ (e₀t - a) = t • u + -(Sys.Sig₂ *ᵥ u) := by
        rw [blk₂_sub]
        have : blk₂ e₀t = t • u := rfl
        rw [this]
        rfl
      rw [h6, h7]
      have h8 : quadForm (symmPinv Sys.hSig₁.1) (0 : Fin n₁ → ℝ) = 0 := by
        simp [quadForm]
      rw [h8, quadForm_add_of_isHermitian (symmPinv_isHermitian _),
        quadForm_neg, quadForm_smul, quadForm_symmPinv_image Sys.hSig₂]
      have h9 : (t • u) ⬝ᵥ (symmPinv Sys.hSig₂.1 *ᵥ -(Sys.Sig₂ *ᵥ u))
          = -(t * (u ⬝ᵥ u)) := by
        rw [Matrix.mulVec_neg, hWinv, dotProduct_neg, smul_dotProduct,
          smul_eq_mul]
      rw [h9]
      ring
    have h10 : t ^ 2 * B T - 2 * t * (u ⬝ᵥ u)
        = -((u ⬝ᵥ u) ^ 2 / B T) := by
      rw [ht, hB]
      field_simp
      ring
    rw [h2, h3, h5] at h1
    rw [hB] at h10
    linarith [h1, h10]
  -- the curvature grows at most linearly
  have hBup : ∀ T, B T ≤ (cW * ‖v‖ ^ 2 + cB * ‖v‖ ^ 2) * (1 + T : ℝ) := by
    intro T
    have h1 : quadForm (symmPinv Sys.hSig₂.1) u ≤ cW * ‖v‖ ^ 2 := by
      refine (hW u).trans ?_
      have h2 : ‖u‖ ≤ ‖v‖ := by
        have h3 := horbu 0
        simpa using h3
      have h4 : ‖u‖ ^ 2 ≤ ‖v‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg u) h2 2
      exact mul_le_mul_of_nonneg_left h4 hcW.le
    have h5 := hroll u ‖v‖ T (norm_nonneg v) horbu
    have h6 : (1:ℝ) ≤ 1 + T := by
      have := Nat.cast_nonneg (α := ℝ) T
      linarith
    have h7 : cW * ‖v‖ ^ 2 ≤ cW * ‖v‖ ^ 2 * (1 + T : ℝ) := by
      have h8 : (0:ℝ) ≤ cW * ‖v‖ ^ 2 := by positivity
      nlinarith
    rw [hB]
    have h9 : cB * (1 + T : ℝ) * ‖v‖ ^ 2 = cB * ‖v‖ ^ 2 * (1 + T : ℝ) := by
      ring
    rw [h9] at h5
    have h10 : (cW * ‖v‖ ^ 2 + cB * ‖v‖ ^ 2) * (1 + T : ℝ)
        = cW * ‖v‖ ^ 2 * (1 + T : ℝ) + cB * ‖v‖ ^ 2 * (1 + T : ℝ) := by
      ring
    rw [h10]
    linarith
  -- assemble the harmonic floor
  have huu : 0 < u ⬝ᵥ u := by
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hune (funext hall)
    have h1 : (0:ℝ) < u j * u j := mul_self_pos.mpr hj
    have h2 : ∀ i ∈ Finset.univ, (0:ℝ) ≤ u i * u i :=
      fun i _ => mul_self_nonneg _
    exact Finset.sum_pos' h2 ⟨j, Finset.mem_univ j, h1⟩
  set cM := cW * ‖v‖ ^ 2 + cB * ‖v‖ ^ 2 with hcM
  have hcM0 : 0 < cM := by
    rw [hcM]
    have h1 : 0 < cW * ‖v‖ ^ 2 := by positivity
    have h2 : 0 < cB * ‖v‖ ^ 2 := by positivity
    linarith
  refine ⟨a, (u ⬝ᵥ u) ^ 2 / cM, hane, by positivity, fun T => ?_⟩
  have h1 := hval T
  have h2 := hVbar
  have h3 := hBpos T
  have h4 := hBup T
  have h1T : (0:ℝ) < 1 + T := by
    have := Nat.cast_nonneg (α := ℝ) T
    linarith
  -- `(u⬝u)²/(cM(1+T)) ≤ (u⬝u)²/B_T` since `B_T ≤ cM(1+T)`
  have h5 : (u ⬝ᵥ u) ^ 2 / cM / (1 + T : ℝ)
      ≤ (u ⬝ᵥ u) ^ 2 / B T := by
    rw [div_div]
    refine div_le_div_of_nonneg_left (sq_nonneg _) h3 ?_
    calc B T ≤ cM * (1 + T : ℝ) := h4
    _ = cM * (1 + T : ℝ) := rfl
  linarith

/-! ### C3w is necessary for GES (`thm:ges-fi`, necessity) -/

private lemma tendsto_poly_geo (k : ℕ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Tendsto (fun T : ℕ => (1 + T : ℝ) ^ k * r ^ T) atTop (nhds 0) := by
  rcases eq_or_lt_of_le h0 with h | h
  · refine Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop 1] with T hT
    rw [← h, zero_pow (by omega), mul_zero]
  · have hs := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k
      (r := r) (by rwa [Real.norm_eq_abs, abs_of_nonneg h0])
    have ht := hs.tendsto_atTop_zero
    have ht2 : Tendsto (fun T : ℕ => ((T + 1 : ℕ) : ℝ) ^ k * r ^ (T + 1))
        atTop (nhds 0) := ht.comp (tendsto_add_atTop_nat 1)
    have ht3 := ht2.const_mul r⁻¹
    rw [mul_zero] at ht3
    refine ht3.congr fun T => ?_
    push_cast
    rw [pow_succ]
    field_simp
    ring

/-- **C3w is necessary for GES** (given C1 ∧ C2): an exponentially
stable terminal error closes the value gap exponentially, but an
on-circle mode holds it open harmonically. -/
theorem C3w_of_isGES (hC1 : Sys.C1) (hC2 : Sys.C2) (hges : Sys.IsGES) :
    Sys.C3w := by
  classical
  by_contra hnc3
  obtain ⟨a, c', hane, hc', hfloor⟩ :=
    Sys.exists_gap_floor_of_not_C3w hC1 hC2 hnc3
  obtain ⟨C, γ, hC0, hγ0, hγ1, hb⟩ := hges
  obtain ⟨cbr, qbr, hcbr, hbr⟩ := Sys.exists_upper_bracket
  obtain ⟨cprop, ρc, hcprop, hρc0, hρc1, hprop⟩ :=
    Sys.exists_propagator_bound hC1
  obtain ⟨c₁, hc₁0, hblk⟩ := Sys.exists_optInit_blk₁_bound hC1 hC2
  obtain ⟨cP, hcP, hPb⟩ := exists_quadForm_le (Sys.Pinf hC1)
  -- the gap closes exponentially fast
  have hgap : ∀ T : ℕ, Sys.valueLim a - Sys.value a T
      ≤ cbr * (1 + T : ℝ) ^ qbr * (C * ‖a‖) ^ 2 * (γ ^ 2) ^ T
        + cP * (cprop * (1 + c₁) * ‖a‖) ^ 2 * (ρc ^ 2) ^ T := by
    intro T
    have h1 := Sys.gap_le_antistable_energy hC1 hC2 a T
    -- the antistable terms through the bracket and GES
    have h2 : Sys.A₂ ^ T *ᵥ blk₂ (Sys.optInit a T)
        = blk₂ (Sys.optTerm a T) := by
      unfold optTerm
      rw [← Sys.lq.traj_optCtrl, Sys.blk₂_traj]
    have h3 : ‖Sys.A₂ ^ T *ᵥ blk₂ (Sys.optInit a T)‖
        ≤ C * γ ^ T * ‖a‖ := by
      rw [h2]
      exact le_trans (norm_blk₂_le _) (hb T a)
    have h4 := hbr (blk₂ (Sys.optInit a T)) T
    have h5 : ‖Sys.A₂ ^ T *ᵥ blk₂ (Sys.optInit a T)‖ ^ 2
        ≤ (C * γ ^ T * ‖a‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h3 2
    have h6 : quadForm (symmPinv Sys.hSig₂.1) (blk₂ (Sys.optInit a T))
        + quadForm (Sys.lq.ric T) (Sum.elim 0 (blk₂ (Sys.optInit a T)))
          ≤ cbr * (1 + T : ℝ) ^ qbr * (C * γ ^ T * ‖a‖) ^ 2 := by
      refine h4.trans ?_
      refine mul_le_mul_of_nonneg_left h5 ?_
      positivity
    -- the block-1 endpoint through the propagator
    have h7 : ‖Sys.lqRed.optTraj (blk₁ (Sys.optInit a T)) T T‖
        ≤ cprop * ρc ^ T * ((1 + c₁) * ‖a‖) := by
      rw [Sys.lqRed.optTraj_eq_revProd _ T T le_rfl, Nat.sub_self]
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      have h8 : ‖blk₁ (Sys.optInit a T)‖ ≤ (1 + c₁) * ‖a‖ := by
        have h9 := hblk a T
        have h10 : blk₁ (Sys.optInit a T)
            = blk₁ (Sys.optInit a T - a) + blk₁ a := by
          rw [← blk₁_add]
          congr 1
          abel
        have h11 := norm_blk₁_le a
        calc ‖blk₁ (Sys.optInit a T)‖
            ≤ ‖blk₁ (Sys.optInit a T - a)‖ + ‖blk₁ a‖ := by
              rw [h10]
              exact norm_add_le _ _
        _ ≤ c₁ * ‖a‖ + ‖a‖ := add_le_add h9 h11
        _ = (1 + c₁) * ‖a‖ := by ring
      have h12 := hprop 0 T
      refine (mul_le_mul h12 h8 (norm_nonneg _) ?_).trans (le_of_eq ?_)
      · positivity
      · ring
    have h13 : quadForm (Sys.Pinf hC1)
        (Sys.lqRed.optTraj (blk₁ (Sys.optInit a T)) T T)
          ≤ cP * (cprop * ρc ^ T * ((1 + c₁) * ‖a‖)) ^ 2 :=
      (hPb _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) h7 2) hcP.le)
    have h14 : (C * γ ^ T * ‖a‖) ^ 2
        = (C * ‖a‖) ^ 2 * (γ ^ 2) ^ T := by
      rw [← pow_mul, mul_comm 2 T, pow_mul]
      ring
    have h15 : (cprop * ρc ^ T * ((1 + c₁) * ‖a‖)) ^ 2
        = (cprop * (1 + c₁) * ‖a‖) ^ 2 * (ρc ^ 2) ^ T := by
      rw [← pow_mul, mul_comm 2 T, pow_mul]
      ring
    rw [h14] at h6
    rw [h15] at h13
    have h16 : cbr * (1 + T : ℝ) ^ qbr
        * ((C * ‖a‖) ^ 2 * (γ ^ 2) ^ T)
        = cbr * (1 + T : ℝ) ^ qbr * (C * ‖a‖) ^ 2 * (γ ^ 2) ^ T := by
      ring
    rw [h16] at h6
    linarith
  -- the harmonic floor cannot survive the exponential closure
  have hkey : ∀ T : ℕ, c'
      ≤ cbr * (C * ‖a‖) ^ 2 * ((1 + T : ℝ) ^ (qbr + 1) * (γ ^ 2) ^ T)
        + cP * (cprop * (1 + c₁) * ‖a‖) ^ 2
          * ((1 + T : ℝ) ^ 1 * (ρc ^ 2) ^ T) := by
    intro T
    have h1T : (0:ℝ) < 1 + T := by
      have := Nat.cast_nonneg (α := ℝ) T
      linarith
    have h1 := hfloor T
    have h2 := hgap T
    have h3 : c' ≤ (1 + T : ℝ) * (Sys.valueLim a - Sys.value a T) := by
      rw [div_le_iff₀ h1T] at h1
      linarith [h1]
    have h4 := mul_le_mul_of_nonneg_left h2 h1T.le
    have h5 : (1 + T : ℝ)
        * (cbr * (1 + T : ℝ) ^ qbr * (C * ‖a‖) ^ 2 * (γ ^ 2) ^ T
          + cP * (cprop * (1 + c₁) * ‖a‖) ^ 2 * (ρc ^ 2) ^ T)
        = cbr * (C * ‖a‖) ^ 2 * ((1 + T : ℝ) ^ (qbr + 1) * (γ ^ 2) ^ T)
          + cP * (cprop * (1 + c₁) * ‖a‖) ^ 2
            * ((1 + T : ℝ) ^ 1 * (ρc ^ 2) ^ T) := by
      rw [pow_succ, pow_one]
      ring
    rw [h5] at h4
    linarith
  have htend : Tendsto (fun T : ℕ =>
      cbr * (C * ‖a‖) ^ 2 * ((1 + T : ℝ) ^ (qbr + 1) * (γ ^ 2) ^ T)
        + cP * (cprop * (1 + c₁) * ‖a‖) ^ 2
          * ((1 + T : ℝ) ^ 1 * (ρc ^ 2) ^ T)) atTop (nhds 0) := by
    have h1 := (tendsto_poly_geo (qbr + 1) (r := γ ^ 2) (sq_nonneg γ)
      (by nlinarith)).const_mul (cbr * (C * ‖a‖) ^ 2)
    have h2 := (tendsto_poly_geo 1 (r := ρc ^ 2) (sq_nonneg ρc)
      (by nlinarith)).const_mul (cP * (cprop * (1 + c₁) * ‖a‖) ^ 2)
    rw [mul_zero] at h1 h2
    have h3 := h1.add h2
    rw [add_zero] at h3
    exact h3
  obtain ⟨T, hT⟩ := (htend.eventually_lt_const hc').exists
  exact absurd (hkey T) (not_le.mpr hT)

/-! ### The exponential slide and floor (`lem:coercive`(3), variational
form) -/

/-- Under C3w the inverse antistable dynamics are Schur. -/
lemma A₂_inv_schur (hC3 : Sys.C3w) : IsSchurStable Sys.A₂⁻¹ := by
  intro μ hμ
  rcases eq_or_ne μ 0 with h0 | hne
  · rw [h0, norm_zero]
    norm_num
  have hspec : μ ∈ spectrum ℂ (Matrix.toLin' (complexify Sys.A₂⁻¹)) := by
    rw [Matrix.spectrum_toLin']
    exact hμ
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    hspec).exists_hasEigenvector
  have hAv : complexify Sys.A₂⁻¹ *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
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
  have h4 := hC3 μ⁻¹ (mem_spectrum_of_mulVec_eq_smul hv.2 h2)
  rw [norm_inv] at h4
  have h5 : 0 < ‖μ‖ := norm_pos_iff.mpr hne
  have h6 : ‖μ‖ * ‖μ‖⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt h5)
  nlinarith

private lemma pow_mulVec_norm_le {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) :
    ∀ (l : ℕ) (x : Fin k → ℝ), ‖M ^ l *ᵥ x‖ ≤ (1 + ‖M‖) ^ l * ‖x‖
  | 0, x => by simp
  | l + 1, x => by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
    have h1 := pow_mulVec_norm_le M l x
    have h2 : ‖M‖ ≤ 1 + ‖M‖ := by linarith [norm_nonneg M]
    have h3 : (0:ℝ) ≤ (1 + ‖M‖) ^ l := by positivity
    calc ‖M‖ * ‖M ^ l *ᵥ x‖ ≤ ‖M‖ * ((1 + ‖M‖) ^ l * ‖x‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg M)
    _ ≤ (1 + ‖M‖) * ((1 + ‖M‖) ^ l * ‖x‖) := by
        refine mul_le_mul_of_nonneg_right h2 ?_
        exact mul_nonneg h3 (norm_nonneg x)
    _ = (1 + ‖M‖) ^ (l + 1) * ‖x‖ := by
        rw [pow_succ']
        ring

/-- The pseudoinverse of the positive definite antistable prior is
itself positive definite. -/
lemma symmPinv_Sig₂_posDef (hC2 : Sys.C2) :
    (symmPinv Sys.hSig₂.1).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (symmPinv_isHermitian _) fun w hw => ?_
  have h3 : w = Sys.Sig₂ *ᵥ (Sys.Sig₂⁻¹ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
      (isUnit_iff_ne_zero.mpr hC2.det_pos.ne'), Matrix.one_mulVec]
  have h4 : w ⬝ᵥ (symmPinv Sys.hSig₂.1 *ᵥ w)
      = quadForm Sys.Sig₂ (Sys.Sig₂⁻¹ *ᵥ w) := by
    show quadForm (symmPinv Sys.hSig₂.1) w = _
    conv_lhs => rw [h3]
    exact quadForm_symmPinv_image Sys.hSig₂ _
  simp only [star_trivial]
  rw [h4]
  refine hC2.quadForm_pos ?_
  intro h5
  apply hw
  rw [h3, h5, Matrix.mulVec_zero]

/-- **The variational slide-rate** (`eq:slide-rate` + `eq:floor`): under
C1 ∧ C2 ∧ C3w, every antistable state of the `(0,w)` problem is seen by
the total antistable energy, exponentially weighted from the far end. -/
theorem exists_slide_rate (hC1 : Sys.C1) (hC2 : Sys.C2)
    (hC3 : Sys.C3w) :
    ∃ chat ρ₂ : ℝ, 0 < chat ∧ 0 < ρ₂ ∧ ρ₂ < 1 ∧
      ∀ (w : Fin n₂ → ℝ) (T s : ℕ), s ≤ T →
        ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2 ≤ chat * ρ₂ ^ (2 * (T - s))
          * (quadForm (symmPinv Sys.hSig₂.1) w
            + quadForm (Sys.lq.ric T) (Sum.elim 0 w)) := by
  classical
  obtain ⟨α, hα, hcoer⟩ := Sys.exists_window_coercivity hC1
  obtain ⟨c₂, ρ₂, hc₂, hρ₂0, hρ₂1, hinv⟩ :=
    (Sys.A₂_inv_schur hC3).exists_pow_norm_le
  obtain ⟨cSg, hcSg, hSglow⟩ := (Sys.symmPinv_Sig₂_posDef hC2).exists_le_quadForm
  set m := n₁ + n₂ with hm
  set cm : ℝ := (1 + ‖Sys.A₂‖) ^ m with hcm
  have hcm0 : 0 < cm := by positivity
  -- the sliding no-rate bound: a valid restart sees the state
  have hslide : ∀ (w : Fin n₂ → ℝ) (T s : ℕ), s + m ≤ T →
      α * ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2
        ≤ quadForm (Sys.lq.ric T) (Sum.elim 0 w) := by
    intro w T s hsm
    set x₀ : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim 0 w with hx₀
    set ω := Sys.lq.optCtrl x₀ T with hω
    have h1 : quadForm (Sys.lq.ric T) x₀ = Sys.lq.cost x₀ ω T := by
      rw [hω, Sys.lq.cost_optCtrl]
    have h2 := Sys.lq.quadForm_ric_traj_le_cost x₀ ω hsm
    have h3 := hcoer (blk₁ (Sys.lq.traj x₀ ω s)) (blk₂ (Sys.lq.traj x₀ ω s))
    rw [sumElim_blk] at h3
    have h4 : blk₂ (Sys.lq.traj x₀ ω s) = Sys.A₂ ^ s *ᵥ w := by
      rw [Sys.blk₂_traj]
      congr 1
    rw [h4] at h3
    rw [h1]
    exact le_trans h3 (le_trans h2 (le_of_eq rfl))
  -- assemble the three regimes into one constant
  set chat : ℝ := c₂ ^ 2 * (ρ₂ ^ m)⁻¹ ^ 2 / α
    + cm ^ 2 / (α * (ρ₂ ^ m) ^ 2) + cm ^ 2 / (cSg * (ρ₂ ^ m) ^ 2)
    with hchat
  have hρ₂m : 0 < ρ₂ ^ m := pow_pos hρ₂0 m
  have hchat0 : 0 < chat := by
    rw [hchat]
    positivity
  refine ⟨chat, ρ₂, hchat0, hρ₂0, hρ₂1, ?_⟩
  intro w T s hsT
  have hqSg : 0 ≤ quadForm (symmPinv Sys.hSig₂.1) w :=
    Sys.hSig₂.symmPinv.quadForm_nonneg w
  have hqric : 0 ≤ quadForm (Sys.lq.ric T) (Sum.elim 0 w) :=
    (Sys.lq.ric_posSemidef T).quadForm_nonneg _
  have hρpow : 0 < ρ₂ ^ (2 * (T - s)) := pow_pos hρ₂0 _
  rcases le_or_gt (s + m) T with hcase1 | hcase2
  · -- a full window fits after `s`: restart at `t := T - m ≥ s`
    set t := T - m with ht
    have hst : s ≤ t := by omega
    have h1 := hslide w T t (by omega)
    -- reconstruct the `s`-state from the `t`-state
    have h2 : Sys.A₂ ^ s *ᵥ w
        = Sys.A₂⁻¹ ^ (t - s) *ᵥ (Sys.A₂ ^ t *ᵥ w) := by
      rw [Matrix.mulVec_mulVec]
      congr 1
      have key : ∀ l j' : ℕ, Sys.A₂⁻¹ ^ l * Sys.A₂ ^ (l + j')
          = Sys.A₂ ^ j' := by
        intro l
        induction l with
        | zero => intro j'; simp
        | succ l ih =>
          intro j'
          have hu : IsUnit Sys.A₂.det :=
            isUnit_iff_ne_zero.mpr Sys.A₂_det_ne_zero
          have h1' : l + 1 + j' = (l + j') + 1 := by omega
          rw [h1', pow_succ, pow_succ']
          calc Sys.A₂⁻¹ ^ l * Sys.A₂⁻¹ * (Sys.A₂ * Sys.A₂ ^ (l + j'))
              = Sys.A₂⁻¹ ^ l * (Sys.A₂⁻¹ * Sys.A₂) * Sys.A₂ ^ (l + j') := by
                simp only [Matrix.mul_assoc]
          _ = Sys.A₂⁻¹ ^ l * Sys.A₂ ^ (l + j') := by
                rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
          _ = Sys.A₂ ^ j' := ih j'
      have h2' : (t - s) + s = t := by omega
      have h3' := key (t - s) s
      rw [h2'] at h3'
      exact h3'.symm
    have h3 : ‖Sys.A₂ ^ s *ᵥ w‖
        ≤ c₂ * ρ₂ ^ (t - s) * ‖Sys.A₂ ^ t *ᵥ w‖ := by
      rw [h2]
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      exact mul_le_mul_of_nonneg_right (hinv (t - s)) (norm_nonneg _)
    have h4 : ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2
        ≤ c₂ ^ 2 * (ρ₂ ^ (t - s)) ^ 2 * ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2 := by
      have h5 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      calc ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2
          ≤ (c₂ * ρ₂ ^ (t - s) * ‖Sys.A₂ ^ t *ᵥ w‖) ^ 2 := h5
      _ = c₂ ^ 2 * (ρ₂ ^ (t - s)) ^ 2 * ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2 := by ring
    have h6 : ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2
        ≤ quadForm (Sys.lq.ric T) (Sum.elim 0 w) / α := by
      rw [le_div_iff₀ hα]
      linarith
    -- the exponent bookkeeping: `t - s = (T - s) - m`
    have h7 : (ρ₂ ^ (t - s)) ^ 2
        = ρ₂ ^ (2 * (T - s)) * ((ρ₂ ^ m)⁻¹) ^ 2 := by
      have h8 : t - s + m = T - s := by omega
      have h9 : ρ₂ ^ (t - s) * ρ₂ ^ m = ρ₂ ^ (T - s) := by
        rw [← pow_add, h8]
      have h10 : ρ₂ ^ (t - s) = ρ₂ ^ (T - s) * (ρ₂ ^ m)⁻¹ := by
        field_simp
        linarith [h9]
      rw [h10, mul_pow, ← pow_mul, mul_comm (T - s) 2]
    calc ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2
        ≤ c₂ ^ 2 * (ρ₂ ^ (t - s)) ^ 2 * ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2 := h4
    _ ≤ c₂ ^ 2 * (ρ₂ ^ (t - s)) ^ 2
          * (quadForm (Sys.lq.ric T) (Sum.elim 0 w) / α) := by
        refine mul_le_mul_of_nonneg_left h6 ?_
        positivity
    _ = c₂ ^ 2 * ((ρ₂ ^ m)⁻¹) ^ 2 / α * ρ₂ ^ (2 * (T - s))
          * quadForm (Sys.lq.ric T) (Sum.elim 0 w) := by
        rw [h7]
        ring
    _ ≤ chat * ρ₂ ^ (2 * (T - s))
          * (quadForm (symmPinv Sys.hSig₂.1) w
            + quadForm (Sys.lq.ric T) (Sum.elim 0 w)) := by
        have hle : c₂ ^ 2 * ((ρ₂ ^ m)⁻¹) ^ 2 / α ≤ chat := by
          rw [hchat]
          have hp1 : (0:ℝ) ≤ cm ^ 2 / (α * (ρ₂ ^ m) ^ 2) := by positivity
          have hp2 : (0:ℝ) ≤ cm ^ 2 / (cSg * (ρ₂ ^ m) ^ 2) := by positivity
          linarith
        have hnn : (0:ℝ) ≤ quadForm (Sys.lq.ric T) (Sum.elim 0 w) := hqric
        nlinarith [mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hle hρpow.le)
          hnn, mul_nonneg (mul_nonneg hchat0.le hρpow.le) hqSg]
  · -- fewer than `m` steps remain
    have hTs : T - s < m := by omega
    have hbase : ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2 ≤ cm ^ 2
        * (quadForm (symmPinv Sys.hSig₂.1) w
          + quadForm (Sys.lq.ric T) (Sum.elim 0 w))
        / min α cSg := by
      rcases le_or_gt m T with hmT | hmT
      · -- restart at `t := T - m`, then at most `m` extra steps
        set t := T - m with ht
        have h1 := hslide w T t (by omega)
        have h2 : Sys.A₂ ^ s *ᵥ w
            = Sys.A₂ ^ (s - t) *ᵥ (Sys.A₂ ^ t *ᵥ w) := by
          rw [Matrix.mulVec_mulVec, ← pow_add]
          congr 2
          omega
        have h4 : ‖Sys.A₂ ^ s *ᵥ w‖ ≤ cm * ‖Sys.A₂ ^ t *ᵥ w‖ := by
          rw [h2]
          refine (pow_mulVec_norm_le Sys.A₂ (s - t) _).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [hcm]
          refine pow_le_pow_right₀ ?_ (by omega)
          linarith [norm_nonneg Sys.A₂]
        have h5 : ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2
            ≤ cm ^ 2 * ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2 := by
          have h6 := pow_le_pow_left₀ (norm_nonneg _) h4 2
          calc ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2
              ≤ (cm * ‖Sys.A₂ ^ t *ᵥ w‖) ^ 2 := h6
          _ = cm ^ 2 * ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2 := by ring
        have h7 : ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2
            ≤ quadForm (Sys.lq.ric T) (Sum.elim 0 w) / min α cSg := by
          rw [le_div_iff₀ (lt_min hα hcSg)]
          have h8 : ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2 * min α cSg
              ≤ ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2 * α :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
          nlinarith
        have h9 : (0:ℝ) < min α cSg := lt_min hα hcSg
        calc ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2
            ≤ cm ^ 2 * ‖Sys.A₂ ^ t *ᵥ w‖ ^ 2 := h5
        _ ≤ cm ^ 2 * (quadForm (Sys.lq.ric T) (Sum.elim 0 w)
              / min α cSg) := mul_le_mul_of_nonneg_left h7 (sq_nonneg cm)
        _ ≤ cm ^ 2 * (quadForm (symmPinv Sys.hSig₂.1) w
              + quadForm (Sys.lq.ric T) (Sum.elim 0 w)) / min α cSg := by
            rw [mul_div_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg cm)
            have h9 : (0:ℝ) < min α cSg := lt_min hα hcSg
            gcongr
            linarith
      · -- the horizon itself is short: the prior term sees `w`
        have h1 := hSglow w
        have h2 : Sys.A₂ ^ s *ᵥ w = Sys.A₂ ^ s *ᵥ w := rfl
        have h4 : ‖Sys.A₂ ^ s *ᵥ w‖ ≤ cm * ‖w‖ := by
          refine (pow_mulVec_norm_le Sys.A₂ s w).trans ?_
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [hcm]
          refine pow_le_pow_right₀ ?_ (by omega)
          linarith [norm_nonneg Sys.A₂]
        have h5 : ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2 ≤ cm ^ 2 * ‖w‖ ^ 2 := by
          have h6 := pow_le_pow_left₀ (norm_nonneg _) h4 2
          calc ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2 ≤ (cm * ‖w‖) ^ 2 := h6
          _ = cm ^ 2 * ‖w‖ ^ 2 := by ring
        have h7 : ‖w‖ ^ 2
            ≤ quadForm (symmPinv Sys.hSig₂.1) w / min α cSg := by
          rw [le_div_iff₀ (lt_min hα hcSg)]
          have h8 : ‖w‖ ^ 2 * min α cSg ≤ ‖w‖ ^ 2 * cSg :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _)
          nlinarith
        calc ‖Sys.A₂ ^ s *ᵥ w‖ ^ 2 ≤ cm ^ 2 * ‖w‖ ^ 2 := h5
        _ ≤ cm ^ 2 * (quadForm (symmPinv Sys.hSig₂.1) w / min α cSg) :=
            mul_le_mul_of_nonneg_left h7 (sq_nonneg cm)
        _ ≤ cm ^ 2 * (quadForm (symmPinv Sys.hSig₂.1) w
              + quadForm (Sys.lq.ric T) (Sum.elim 0 w)) / min α cSg := by
            rw [mul_div_assoc]
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg cm)
            have h9 : (0:ℝ) < min α cSg := lt_min hα hcSg
            gcongr
            linarith
    -- absorb the short remaining horizon into the constant
    have hpow2 : ρ₂ ^ (2 * m) ≤ ρ₂ ^ (2 * (T - s)) :=
      pow_le_pow_of_le_one hρ₂0.le hρ₂1.le (by omega)
    have hq : 0 ≤ quadForm (symmPinv Sys.hSig₂.1) w
        + quadForm (Sys.lq.ric T) (Sum.elim 0 w) := add_nonneg hqSg hqric
    have hkey : cm ^ 2 / min α cSg ≤ chat * ρ₂ ^ (2 * (T - s)) := by
      have h1 : cm ^ 2 / min α cSg ≤ cm ^ 2 / α + cm ^ 2 / cSg := by
        rcases min_choice α cSg with hm1 | hm1 <;> rw [hm1]
        · have h1' : (0:ℝ) ≤ cm ^ 2 / cSg := by positivity
          linarith
        · have h1' : (0:ℝ) ≤ cm ^ 2 / α := by positivity
          linarith
      have hm2 : (ρ₂ ^ m) ^ 2 = ρ₂ ^ (2 * m) := by
        rw [← pow_mul, mul_comm]
      have h4 : cm ^ 2 / (α * (ρ₂ ^ m) ^ 2) * ρ₂ ^ (2 * m)
          = cm ^ 2 / α := by
        rw [← hm2]
        field_simp
      have h5 : cm ^ 2 / (cSg * (ρ₂ ^ m) ^ 2) * ρ₂ ^ (2 * m)
          = cm ^ 2 / cSg := by
        rw [← hm2]
        field_simp
      have h2 : cm ^ 2 / α + cm ^ 2 / cSg ≤ chat * ρ₂ ^ (2 * m) := by
        rw [hchat, add_mul, add_mul, h4, h5]
        have h3 : (0:ℝ) ≤ c₂ ^ 2 * ((ρ₂ ^ m)⁻¹) ^ 2 / α
            * ρ₂ ^ (2 * m) := by positivity
        linarith
      calc cm ^ 2 / min α cSg ≤ cm ^ 2 / α + cm ^ 2 / cSg := h1
      _ ≤ chat * ρ₂ ^ (2 * m) := h2
      _ ≤ chat * ρ₂ ^ (2 * (T - s)) :=
          mul_le_mul_of_nonneg_left hpow2 hchat0.le
    have hrearr : cm ^ 2 * (quadForm (symmPinv Sys.hSig₂.1) w
        + quadForm (Sys.lq.ric T) (Sum.elim 0 w)) / min α cSg
        = cm ^ 2 / min α cSg * (quadForm (symmPinv Sys.hSig₂.1) w
          + quadForm (Sys.lq.ric T) (Sum.elim 0 w)) := by
      ring
    rw [hrearr] at hbase
    exact hbase.trans (mul_le_mul_of_nonneg_right hkey hq)

/-! ### The cross-block recursion (`eq:Y-rec`) -/

lemma toBlocks₁₂_add (M N : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ) :
    (M + N).toBlocks₁₂ = M.toBlocks₁₂ + N.toBlocks₁₂ := rfl

lemma toBlocks₁₂_sub (M N : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ) :
    (M - N).toBlocks₁₂ = M.toBlocks₁₂ - N.toBlocks₁₂ := rfl

/-- The reduced closed loop, made explicit. -/
lemma lqRed_Acl_eq (P : Matrix (Fin n₁) (Fin n₁) ℝ) :
    Sys.lqRed.Acl P
      = Sys.A₁ - Sys.G₁ * (Sys.lqRed.gainΓ P)⁻¹ * Sys.G₁ᵀ * P * Sys.A₁ := by
  unfold LQSystem.Acl LQSystem.gainK
  have h1 : Sys.lqRed.A = Sys.A₁ := rfl
  have h2 : Sys.lqRed.B = -Sys.G₁ := rfl
  rw [h1, h2]
  simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  simp only [Matrix.mul_assoc]

/-- Symmetry of the reduced curvature. -/
lemma lqRed_gainΓ_transpose {P : Matrix (Fin n₁) (Fin n₁) ℝ}
    (hP : Pᵀ = P) : (Sys.lqRed.gainΓ P)ᵀ = Sys.lqRed.gainΓ P := by
  unfold LQSystem.gainΓ
  have h2 : Sys.lqRed.B = -Sys.G₁ := rfl
  have h3 : Sys.lqRed.Ru = Sys.Qi := rfl
  rw [h2, h3]
  simp only [Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_neg,
    Sys.hQi.posSemidef.1.transpose_eq_self, hP, Matrix.mul_assoc]

/-- **The `₁₂` block of the full Riccati step** (`eq:Y-rec`): the cross
block evolves by the reduced closed loop on the left and the antistable
dynamics on the right. -/
theorem step_fromBlocks_toBlocks₁₂ (P₁₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (P₁₂ : Matrix (Fin n₁) (Fin n₂) ℝ) (P₂₁ : Matrix (Fin n₂) (Fin n₁) ℝ)
    (P₂₂ : Matrix (Fin n₂) (Fin n₂) ℝ) (hP₁₁ : P₁₁ᵀ = P₁₁) :
    (Sys.lq.step (Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂)).toBlocks₁₂
      = Sys.C₁ᵀ * Sys.Ri * Sys.C₂
        + (Sys.lqRed.Acl P₁₁)ᵀ * (P₁₁ * Sys.A₁₂ + P₁₂ * Sys.A₂) := by
  unfold LQSystem.step
  have hassoc : Sys.lq.Aᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.B *
        (Sys.lq.gainΓ (Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂))⁻¹ * Sys.lq.Bᵀ *
        Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.A
      = (Sys.lq.Aᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.B) *
        (Sys.lq.gainΓ (Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂))⁻¹ *
        (Sys.lq.Bᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.A) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, Sys.lq_APB, Sys.lq_BPA, Sys.lq_gainΓ_fromBlocks, Sys.lq_APA,
    Sys.lq_Qs_fromBlocks]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  rw [toBlocks₁₂_sub, toBlocks₁₂_add, Matrix.toBlocks_fromBlocks₁₂,
    Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₁₂]
  rw [Sys.lqRed_Acl_eq]
  have hΓ : (Sys.lqRed.gainΓ P₁₁)ᵀ = Sys.lqRed.gainΓ P₁₁ :=
    Sys.lqRed_gainΓ_transpose hP₁₁
  rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_nonsing_inv, hΓ, Matrix.transpose_transpose, hP₁₁]
  simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.mul_assoc]
  abel

/-- `eq:Y-rec` on the value iterates. -/
theorem ric_toBlocks₁₂_succ (T : ℕ) :
    (Sys.lq.ric (T + 1)).toBlocks₁₂
      = Sys.C₁ᵀ * Sys.Ri * Sys.C₂
        + (Sys.lqRed.Acl (Sys.lqRed.ric T))ᵀ
          * (Sys.lqRed.ric T * Sys.A₁₂
            + (Sys.lq.ric T).toBlocks₁₂ * Sys.A₂) := by
  have h1 : Sys.lq.ric (T + 1) = Sys.lq.step (Sys.lq.ric T) := rfl
  rw [h1]
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks (Sys.lq.ric T)]
  rw [Sys.step_fromBlocks_toBlocks₁₂ _ _ _ _
    (by
      have h2 := Sys.lq.ric_isHermitian T
      have h3 : (Sys.lq.ric T)ᵀ = Sys.lq.ric T := h2.transpose_eq_self
      have h4 := congrArg Matrix.toBlocks₁₁ h3
      rwa [show (Sys.lq.ric T)ᵀ.toBlocks₁₁ = ((Sys.lq.ric T).toBlocks₁₁)ᵀ
        from rfl] at h4)]
  rw [Sys.ric_toBlocks₁₁]

/-! ### The unrolled cross block and its rate -/

/-- The bounded driving term of the cross-block recursion. -/
noncomputable def Xim (j : ℕ) : Matrix (Fin n₁) (Fin n₂) ℝ :=
  Sys.C₁ᵀ * Sys.Ri * Sys.C₂
    + (Sys.lqRed.Acl (Sys.lqRed.ric j))ᵀ
      * (Sys.lqRed.ric j * Sys.A₁₂)

/-- The unrolled cross block: closed-loop propagators against
antistable powers. -/
theorem ric_toBlocks₁₂_eq_sum : ∀ T : ℕ,
    (Sys.lq.ric T).toBlocks₁₂
      = ∑ j ∈ Finset.range T,
          (revProd (fun r => Sys.lqRed.Acl (Sys.lqRed.ric r))
              (j + 1) (T - 1 - j))ᵀ
            * Sys.Xim j * Sys.A₂ ^ (T - 1 - j)
  | 0 => by
    simp [LQSystem.ric]
    rfl
  | T + 1 => by
    rw [Sys.ric_toBlocks₁₂_succ, ric_toBlocks₁₂_eq_sum T,
      Finset.sum_range_succ]
    -- the newest term is the driving matrix itself
    have hlast : (revProd (fun r => Sys.lqRed.Acl (Sys.lqRed.ric r))
        (T + 1) (T + 1 - 1 - T))ᵀ * Sys.Xim T
          * Sys.A₂ ^ (T + 1 - 1 - T)
        = Sys.C₁ᵀ * Sys.Ri * Sys.C₂
          + (Sys.lqRed.Acl (Sys.lqRed.ric T))ᵀ
            * (Sys.lqRed.ric T * Sys.A₁₂) := by
      rw [show T + 1 - 1 - T = 0 from by omega, revProd_zero,
        Matrix.transpose_one, Matrix.one_mul, pow_zero, Matrix.mul_one]
      rfl
    -- the older terms pick up one closed-loop factor and one `A₂`
    have hold : ∀ j ∈ Finset.range T,
        (revProd (fun r => Sys.lqRed.Acl (Sys.lqRed.ric r))
            (j + 1) (T + 1 - 1 - j))ᵀ * Sys.Xim j
          * Sys.A₂ ^ (T + 1 - 1 - j)
        = (Sys.lqRed.Acl (Sys.lqRed.ric T))ᵀ
            * ((revProd (fun r => Sys.lqRed.Acl (Sys.lqRed.ric r))
                (j + 1) (T - 1 - j))ᵀ * Sys.Xim j
              * Sys.A₂ ^ (T - 1 - j)) * Sys.A₂ := by
      intro j hj
      have hjT := Finset.mem_range.mp hj
      have h1 : T + 1 - 1 - j = (T - 1 - j) + 1 := by omega
      rw [h1, revProd_succ_right, pow_succ]
      have h2 : j + 1 + (T - 1 - j) = T := by omega
      rw [h2, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [Finset.sum_congr rfl hold, hlast]
    have h3 : ∑ j ∈ Finset.range T,
        (Sys.lqRed.Acl (Sys.lqRed.ric T))ᵀ
          * ((revProd (fun r => Sys.lqRed.Acl (Sys.lqRed.ric r))
              (j + 1) (T - 1 - j))ᵀ * Sys.Xim j
            * Sys.A₂ ^ (T - 1 - j)) * Sys.A₂
        = (Sys.lqRed.Acl (Sys.lqRed.ric T))ᵀ
          * ((∑ j ∈ Finset.range T,
              (revProd (fun r => Sys.lqRed.Acl (Sys.lqRed.ric r))
                (j + 1) (T - 1 - j))ᵀ * Sys.Xim j
              * Sys.A₂ ^ (T - 1 - j)) * Sys.A₂) := by
      rw [Matrix.sum_mul, Matrix.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Matrix.mul_assoc]
    rw [h3, Matrix.mul_add]
    abel

/-- The closed-loop factors along the iteration are uniformly bounded. -/
theorem exists_Acl_bound (hC1 : Sys.C1) :
    ∃ cF : ℝ, 0 < cF ∧ ∀ r, ‖Sys.lqRed.Acl (Sys.lqRed.ric r)‖ ≤ cF := by
  obtain ⟨P, _, _, _, _, hK⟩ := Sys.lqRed_lqr hC1
  have hAcl : Tendsto (fun r => Sys.lqRed.Acl (Sys.lqRed.ric r))
      atTop (nhds (Sys.lqRed.Acl P)) := by
    have h1 : Tendsto
        (fun r => Sys.lqRed.B * Sys.lqRed.gainK (Sys.lqRed.ric r))
        atTop (nhds (Sys.lqRed.B * Sys.lqRed.gainK P)) :=
      ((Continuous.matrix_mul continuous_const continuous_id).tendsto
        _).comp hK
    exact Tendsto.sub tendsto_const_nhds h1
  exact exists_norm_bound_of_tendsto hAcl

/-- The driving terms are uniformly bounded. -/
theorem exists_Xim_bound (hC1 : Sys.C1) :
    ∃ cX : ℝ, 0 < cX ∧ ∀ j, ‖Sys.Xim j‖ ≤ cX := by
  obtain ⟨cF, hcF, hF⟩ := Sys.exists_Acl_bound hC1
  obtain ⟨cR, hcR, hRb⟩ := Sys.exists_ricRed_bound hC1
  refine ⟨‖Sys.C₁ᵀ * Sys.Ri * Sys.C₂‖
      + (n₁ : ℝ) * cF * (cR * ‖Sys.A₁₂‖) + 1,
    by positivity, fun j => ?_⟩
  unfold Xim
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(Sys.lqRed.Acl (Sys.lqRed.ric j))ᵀ
      * (Sys.lqRed.ric j * Sys.A₁₂)‖
        ≤ ‖(Sys.lqRed.Acl (Sys.lqRed.ric j))ᵀ‖
          * (‖Sys.lqRed.ric j‖ * ‖Sys.A₁₂‖) := by
    refine (Matrix.linfty_opNorm_mul _ _).trans ?_
    exact mul_le_mul_of_nonneg_left (Matrix.linfty_opNorm_mul _ _)
      (norm_nonneg _)
  have h2 : ‖(Sys.lqRed.Acl (Sys.lqRed.ric j))ᵀ‖
      ≤ (n₁ : ℝ) * cF := by
    refine (linfty_opNorm_transpose_le _).trans ?_
    exact mul_le_mul_of_nonneg_left (hF j) (Nat.cast_nonneg n₁)
  have h3 : ‖Sys.lqRed.ric j‖ * ‖Sys.A₁₂‖ ≤ cR * ‖Sys.A₁₂‖ :=
    mul_le_mul_of_nonneg_right (hRb j) (norm_nonneg _)
  have h4 : (0:ℝ) ≤ ‖Sys.lqRed.ric j‖ * ‖Sys.A₁₂‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h5 : ‖(Sys.lqRed.Acl (Sys.lqRed.ric j))ᵀ‖
      * (‖Sys.lqRed.ric j‖ * ‖Sys.A₁₂‖)
        ≤ (n₁ : ℝ) * cF * (cR * ‖Sys.A₁₂‖) :=
    mul_le_mul h2 h3 h4 (by positivity)
  linarith

end FIESystem

end Estimation
