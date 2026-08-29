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

end FIESystem

end Estimation
