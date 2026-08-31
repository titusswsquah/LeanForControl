import Mathlib.Analysis.SpecificLimits.Basic
import LeanForControl.LinearSystems.QuadForm
import Architect

/-!
# Geometric kernel against a null sequence

The convergence engine of the repaired `lem:marginal`(ii) and of
`lem:supremal`'s stabilizable–antistable step: a nonnegative sequence
dominated by `a·ρ^T + Σ_{j<T} ρ^{T−1−j} e_j` with `ρ < 1` and
`e_j → 0` tends to zero.
-/

namespace Estimation
namespace Dare

open Filter

/-- **Geometric kernel against a null sequence.** -/
lemma tendsto_zero_of_geometric_conv {a ρ : ℝ} (ha : 0 ≤ a)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {x e : ℕ → ℝ}
    (hx : ∀ T, 0 ≤ x T) (he : ∀ j, 0 ≤ e j)
    (hetend : Tendsto e atTop (nhds 0))
    (hbound : ∀ T, x T ≤ a * ρ ^ T
      + ∑ j ∈ Finset.range T, ρ ^ (T - 1 - j) * e j) :
    Tendsto x atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε * (1 - ρ) / 3 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < 1 - ρ := by linarith
    positivity
  -- the input is eventually below δ
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (hetend.eventually_lt_const hδ0)
  -- the head mass
  set H : ℝ := ∑ j ∈ Finset.range M, e j with hH
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun j _ => he j
  -- pick N beyond which the seed and the head are small
  have hρpow : Tendsto (fun T : ℕ => ρ ^ T) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
  have hseed : Tendsto (fun T : ℕ => a * ρ ^ T) atTop (nhds 0) := by
    simpa using hρpow.const_mul a
  have hhead : Tendsto (fun T : ℕ => H * ρ ^ T) atTop (nhds 0) := by
    simpa using hρpow.const_mul H
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (hseed.eventually_lt_const (by positivity : (0:ℝ) < ε / 3))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (hhead.eventually_lt_const (by positivity : (0:ℝ) < ε / 3))
  refine ⟨max (max N₁ (N₂ + M + 1)) (M + 1), fun T hT => ?_⟩
  have hTN₁ : N₁ ≤ T := le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hT)
  have hTN₂ : N₂ + M + 1 ≤ T := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hT)
  have hTM : M + 1 ≤ T := le_trans (le_max_right _ _) hT
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hx T)]
  -- split the convolution at M
  have hsplit : ∑ j ∈ Finset.range T, ρ ^ (T - 1 - j) * e j
      = ∑ j ∈ Finset.range M, ρ ^ (T - 1 - j) * e j
        + ∑ j ∈ Finset.Ico M T, ρ ^ (T - 1 - j) * e j := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : M ≤ T)]
  -- head: each kernel weight is at most ρ^(T-M)
  have hhead' : ∑ j ∈ Finset.range M, ρ ^ (T - 1 - j) * e j
      ≤ H * ρ ^ (T - M) := by
    rw [hH, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have h1 : T - M ≤ T - 1 - j := by omega
    have h2 : ρ ^ (T - 1 - j) ≤ ρ ^ (T - M) :=
      pow_le_pow_of_le_one hρ0.le hρ1.le h1
    calc ρ ^ (T - 1 - j) * e j ≤ ρ ^ (T - M) * e j :=
          mul_le_mul_of_nonneg_right h2 (he j)
    _ = e j * ρ ^ (T - M) := mul_comm _ _
  -- tail: kernel is summable, input below δ
  have htail : ∑ j ∈ Finset.Ico M T, ρ ^ (T - 1 - j) * e j
      ≤ δ / (1 - ρ) := by
    have h1 : ∑ j ∈ Finset.Ico M T, ρ ^ (T - 1 - j) * e j
        ≤ ∑ j ∈ Finset.Ico M T, ρ ^ (T - 1 - j) * δ := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hjM := (Finset.mem_Ico.mp hj).1
      exact mul_le_mul_of_nonneg_left (le_of_lt (hM j hjM))
        (pow_nonneg hρ0.le _)
    have h2 : ∑ j ∈ Finset.Ico M T, ρ ^ (T - 1 - j) * δ
        ≤ (1 - ρ)⁻¹ * δ := by
      rw [← Finset.sum_mul]
      refine mul_le_mul_of_nonneg_right ?_ hδ0.le
      -- the kernel weights are distinct powers of ρ, each appearing once
      have h3 : ∑ j ∈ Finset.Ico M T, ρ ^ (T - 1 - j)
          ≤ ∑ k ∈ Finset.range T, ρ ^ k := by
        have himg : ∑ k ∈ (Finset.Ico M T).image (fun j => T - 1 - j),
              ρ ^ k
            = ∑ j ∈ Finset.Ico M T, ρ ^ (T - 1 - j) := by
          refine Finset.sum_image ?_
          intro j₁ h₁ j₂ h₂ hf
          dsimp only at hf
          have e₁ := (Finset.mem_Ico.mp h₁).2
          have e₂ := (Finset.mem_Ico.mp h₂).2
          omega
        rw [← himg]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro k hk
          obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
          have := (Finset.mem_Ico.mp hj).2
          exact Finset.mem_range.mpr (by omega)
        · intro k _ _
          exact pow_nonneg hρ0.le _
      have h4 : ∑ k ∈ Finset.range T, ρ ^ k ≤ (1 - ρ)⁻¹ := by
        have h5 : 0 < 1 - ρ := by linarith
        have h6 := geom_sum_mul ρ T
        rw [inv_eq_one_div, le_div_iff₀ h5]
        nlinarith [pow_nonneg hρ0.le T]
      exact le_trans h3 h4
    calc ∑ j ∈ Finset.Ico M T, ρ ^ (T - 1 - j) * e j
        ≤ (1 - ρ)⁻¹ * δ := le_trans h1 h2
    _ = δ / (1 - ρ) := by rw [div_eq_inv_mul]
  have hδdiv : δ / (1 - ρ) = ε / 3 := by
    rw [hδ]
    have : (0:ℝ) < 1 - ρ := by linarith
    field_simp
  have hseed' : a * ρ ^ T < ε / 3 := hN₁ T hTN₁
  have hhead'' : H * ρ ^ (T - M) < ε / 3 := by
    have := hN₂ (T - M) (by omega)
    simpa using this
  calc x T ≤ a * ρ ^ T
        + ∑ j ∈ Finset.range T, ρ ^ (T - 1 - j) * e j := hbound T
  _ = a * ρ ^ T + (∑ j ∈ Finset.range M, ρ ^ (T - 1 - j) * e j
        + ∑ j ∈ Finset.Ico M T, ρ ^ (T - 1 - j) * e j) := by
      rw [hsplit]
  _ ≤ a * ρ ^ T + (H * ρ ^ (T - M) + δ / (1 - ρ)) := by
      have := add_le_add hhead' htail
      linarith
  _ < ε / 3 + (ε / 3 + ε / 3) := by
      rw [hδdiv] at *
      have := hseed'
      have := hhead''
      linarith
  _ = ε := by ring

end Dare
end Estimation