import LeanForControl.Estimation.Dare.MainRate
import LeanForControl.LinearSystems.UniformExpStability
import Architect

/-!
# Robustness of the estimator (`thm:payoff`, the ISS display — F2)

Under C1 + C2 + C3w the time-varying error maps `F_T = errMap(Σ_T)`
converge to the Schur `F∞`, so the transition products are uniformly
exponentially bounded (`fact:uniexp`, at the full three-block level —
`transitionProd_norm_le_of_tendsto`, now index-generic). The
disturbance-driven error recursion `e(k+1) = F_k e(k) + d(k)` unrolls
against that bound into the deck's ISS display
`‖e(T)‖ ≤ c γ^T ‖e(0)‖ + ∑_{k<T} c γ^{T-1-k} ‖d_k‖` (`eq:diff-unroll`).
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The time-varying error map along the run from the prior. -/
noncomputable def errMapT (T : ℕ) :
    Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  errMap S.fullC S.R S.fullA (S.dare T)

/-- **The full-level uniform exponential product bound**
(`fact:uniexp` on the three-block run): under C1 + C2 + C3w the
closed-loop transition products decay geometrically, uniformly in the
start time. -/
theorem fullProd_geometric (hnm : nm = 0) (hC1 : S.C1) (hC2 : S.C2) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ i l : ℕ,
      ‖transitionProd S.errMapT i l‖ ≤ c * ρ ^ l := by
  obtain ⟨Sinf, hS⟩ := S.exists_strong_solution hC1
  have hC2w : S.C2w := S.C2w_of_C2 hC2
  obtain ⟨C, ρ₀, hC0, hρ₀0, hρ₀1, hrate⟩ :=
    S.sufficiency_geometric hnm hC1 hC2w hS
  -- the covariance run converges in norm …
  have hlim : Tendsto (fun T => ‖S.dare T - Sinf‖) atTop (nhds 0) := by
    have h0 : Tendsto (fun T : ℕ => C * ρ₀ ^ T) atTop (nhds 0) := by
      simpa using
        (tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀0.le hρ₀1).const_mul C
    refine squeeze_zero (fun T => norm_nonneg _) hrate h0
  -- … so the error maps converge to the Schur limit map
  have hF : Tendsto S.errMapT atTop
      (nhds (errMap S.fullC S.R S.fullA Sinf)) := by
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    exact errMap_tendsto_of_tendsto S.hR
      (fun T => dareIter_posSemidef S.hR S.Qw_posSemidef
        S.Sig0_posSemidef T)
      hS.posSemidef hlim
  have hFs : IsSchurStable (errMap S.fullC S.R S.fullA Sinf) :=
    (S.strong_isSchurStable_iff_C3w hC1 hS).mpr hnm
  exact transitionProd_norm_le_of_tendsto S.errMapT _ hF hFs

/-! ### The disturbance-driven error recursion (`eq:diff-unroll`) -/

/-- The perturbed error trajectory: the optimal filter's error map
driven by an arbitrary disturbance sequence,
`e(k+1) = F_k e(k) + d(k)`. -/
noncomputable def errTraj (e0 : ix n₁ na nm → ℝ)
    (d : ℕ → ix n₁ na nm → ℝ) : ℕ → ix n₁ na nm → ℝ
  | 0 => e0
  | k + 1 => S.errMapT k *ᵥ errTraj e0 d k + d k

/-- The unrolled form: transition product on the initial error plus the
disturbance convolution. -/
lemma errTraj_unroll (e0 : ix n₁ na nm → ℝ)
    (d : ℕ → ix n₁ na nm → ℝ) (T : ℕ) :
    S.errTraj e0 d T
      = transitionProd S.errMapT 0 T *ᵥ e0
        + ∑ k ∈ Finset.range T,
            transitionProd S.errMapT (k + 1) (T - (k + 1)) *ᵥ d k := by
  induction T with
  | zero => simp [errTraj]
  | succ T ih =>
    show S.errMapT T *ᵥ S.errTraj e0 d T + d T = _
    rw [ih, Matrix.mulVec_add]
    have h1 : S.errMapT T *ᵥ (transitionProd S.errMapT 0 T *ᵥ e0)
        = transitionProd S.errMapT 0 (T + 1) *ᵥ e0 := by
      rw [Matrix.mulVec_mulVec, transitionProd_succ, zero_add]
    have h2 : S.errMapT T
        *ᵥ ∑ k ∈ Finset.range T,
          transitionProd S.errMapT (k + 1) (T - (k + 1)) *ᵥ d k
        = ∑ k ∈ Finset.range T,
            transitionProd S.errMapT (k + 1) (T + 1 - (k + 1)) *ᵥ d k := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkT : k < T := Finset.mem_range.mp hk
      rw [Matrix.mulVec_mulVec]
      have h3 : T + 1 - (k + 1) = (T - (k + 1)) + 1 := by omega
      rw [h3, transitionProd_succ]
      have h4 : k + 1 + (T - (k + 1)) = T := by omega
      rw [h4]
    have h5 : ∑ k ∈ Finset.range (T + 1),
        transitionProd S.errMapT (k + 1) (T + 1 - (k + 1)) *ᵥ d k
        = (∑ k ∈ Finset.range T,
            transitionProd S.errMapT (k + 1) (T + 1 - (k + 1)) *ᵥ d k)
          + transitionProd S.errMapT (T + 1) 0 *ᵥ d T := by
      rw [Finset.sum_range_succ, Nat.sub_self]
    rw [h1, h2, h5]
    have h6 : transitionProd S.errMapT (T + 1) 0 *ᵥ d T = d T := by
      rw [transitionProd_zero, Matrix.one_mulVec]
    rw [h6]
    abel

/-- **`thm:payoff`, the ISS display, verified**: under C1 + C2 + C3w
the perturbed estimator error obeys
`‖e(T)‖ ≤ c γ^T ‖e(0)‖ + ∑_{k<T} c γ^{T-1-k} ‖d_k‖` — input-to-state
stability of the optimal filter's error dynamics, with a geometric
transient and a geometrically-discounted disturbance convolution. -/
theorem payoff_iss (hnm : nm = 0) (hC1 : S.C1) (hC2 : S.C2) :
    ∃ c γ : ℝ, 0 < c ∧ 0 < γ ∧ γ < 1 ∧
      ∀ (e0 : ix n₁ na nm → ℝ) (d : ℕ → ix n₁ na nm → ℝ) (T : ℕ),
        ‖S.errTraj e0 d T‖
          ≤ c * γ ^ T * ‖e0‖
            + ∑ k ∈ Finset.range T, c * γ ^ (T - 1 - k) * ‖d k‖ := by
  obtain ⟨c, γ, hc, hγ0, hγ1, hb⟩ := S.fullProd_geometric hnm hC1 hC2
  refine ⟨c, γ, hc, hγ0, hγ1, fun e0 d T => ?_⟩
  rw [S.errTraj_unroll]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖transitionProd S.errMapT 0 T *ᵥ e0‖ ≤ c * γ ^ T * ‖e0‖ := by
    refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hb 0 T) (norm_nonneg _)
  have h2 : ‖∑ k ∈ Finset.range T,
      transitionProd S.errMapT (k + 1) (T - (k + 1)) *ᵥ d k‖
      ≤ ∑ k ∈ Finset.range T, c * γ ^ (T - 1 - k) * ‖d k‖ := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun k hk => ?_
    refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
    have h3 : T - (k + 1) = T - 1 - k := by omega
    rw [← h3]
    exact mul_le_mul_of_nonneg_right (hb (k + 1) (T - (k + 1)))
      (norm_nonneg _)
  linarith

end DareSystem

end Dare
end Estimation
