import LeanForControl.LinearSystems.Schur
import Mathlib.Algebra.Order.Field.GeomSum
import Architect

/-!
# Terminal-state bound through a stabilizing output injection

If some output injection `L` makes `A - LC` Schur, then any trajectory of
`x⁺ = Ax + Bu` has its terminal state controlled by the initial state,
the measured outputs `Cx(k)`, and the inputs, in energy form:
`‖x(T)‖² ≤ c (‖x(0)‖² + Σ (‖Cx(k)‖² + ‖u(k)‖²))`, uniformly in `T`.
This is the convolution/Cauchy–Schwarz step of `prop:gas` in `costogo`,
isolated at the `LinearSystems` layer.
-/

namespace LinearSystems

open Matrix

open scoped Matrix.Norms.Operator

variable {d p' m' : ℕ}

/-- Variation of constants for `x⁺ = Fx + w`. -/
lemma varConst (F : Matrix (Fin d) (Fin d) ℝ) (x w : ℕ → Fin d → ℝ)
    (hrec : ∀ k, x (k + 1) = F *ᵥ x k + w k) (T : ℕ) :
    x T = F ^ T *ᵥ x 0
      + ∑ k ∈ Finset.range T, F ^ (T - 1 - k) *ᵥ w k := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [hrec T, ih, Matrix.mulVec_add, Matrix.mulVec_sum,
      Finset.sum_range_succ]
    have h1 : ∀ k ∈ Finset.range T,
        F *ᵥ (F ^ (T - 1 - k) *ᵥ w k) = F ^ (T + 1 - 1 - k) *ᵥ w k := by
      intro k hk
      rw [Matrix.mulVec_mulVec,
        show T + 1 - 1 - k = (T - 1 - k) + 1 from by
          have := Finset.mem_range.mp hk; omega,
        pow_succ']
    rw [Finset.sum_congr rfl h1, Matrix.mulVec_mulVec, ← pow_succ']
    have h2 : F ^ (T + 1 - 1 - T) *ᵥ w T = w T := by
      rw [show T + 1 - 1 - T = 0 from by omega, pow_zero,
        Matrix.one_mulVec]
    rw [h2]
    abel

/-- **Terminal energy bound through output injection**: with `A - LC`
Schur, `‖x(T)‖²` is dominated by the initial state plus the output/input
energies, uniformly in the horizon. -/
theorem exists_terminal_sq_bound_of_injection
    (A : Matrix (Fin d) (Fin d) ℝ) (C : Matrix (Fin p') (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin m') ℝ) {L : Matrix (Fin d) (Fin p') ℝ}
    (hL : IsSchurStable (A - L * C)) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x : ℕ → Fin d → ℝ) (u : ℕ → Fin m' → ℝ),
      (∀ k, x (k + 1) = A *ᵥ x k + B *ᵥ u k) → ∀ T : ℕ,
      ‖x T‖ ^ 2 ≤ c * (‖x 0‖ ^ 2
        + ∑ k ∈ Finset.range T, (‖C *ᵥ x k‖ ^ 2 + ‖u k‖ ^ 2)) := by
  obtain ⟨cF, ρ, hcF, hρ0, hρ1, hpow⟩ := hL.exists_pow_norm_le
  set κ := max ‖L‖ ‖B‖ + 1 with hκ
  have hκ0 : 0 < κ := by
    have h1 : (0 : ℝ) ≤ max ‖L‖ ‖B‖ :=
      le_trans (norm_nonneg L) (le_max_left _ _)
    rw [hκ]
    linarith
  have hρinv : 0 < (1 - ρ)⁻¹ := by
    rw [inv_pos]
    linarith
  have hc0 : 0 < 2 * cF ^ 2 + 4 * cF ^ 2 * κ ^ 2 * (1 - ρ)⁻¹ := by
    have h1 : 0 < cF ^ 2 := pow_pos hcF 2
    have h2 : 0 < κ ^ 2 := pow_pos hκ0 2
    nlinarith [mul_pos (mul_pos h1 h2) hρinv]
  refine ⟨2 * cF ^ 2 + 4 * cF ^ 2 * κ ^ 2 * (1 - ρ)⁻¹, hc0, ?_⟩
  intro x u hrec T
  set F := A - L * C with hF
  set w : ℕ → Fin d → ℝ := fun k => L *ᵥ (C *ᵥ x k) + B *ᵥ u k with hw
  have hrecF : ∀ k, x (k + 1) = F *ᵥ x k + w k := by
    intro k
    rw [hrec k, hF, hw, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
    module
  -- pointwise bound on the disturbance
  have hwk : ∀ k, ‖w k‖ ≤ κ * (‖C *ᵥ x k‖ + ‖u k‖) := by
    intro k
    rw [hw]
    have h1 : ‖L *ᵥ (C *ᵥ x k)‖ ≤ ‖L‖ * ‖C *ᵥ x k‖ :=
      Matrix.linfty_opNorm_mulVec _ _
    have h2 : ‖B *ᵥ u k‖ ≤ ‖B‖ * ‖u k‖ := Matrix.linfty_opNorm_mulVec _ _
    have h3 : ‖L‖ ≤ κ := by
      rw [hκ]
      have := le_max_left ‖L‖ ‖B‖
      linarith
    have h4 : ‖B‖ ≤ κ := by
      rw [hκ]
      have := le_max_right ‖L‖ ‖B‖
      linarith
    refine (norm_add_le _ _).trans ?_
    have h5 : ‖L‖ * ‖C *ᵥ x k‖ ≤ κ * ‖C *ᵥ x k‖ :=
      mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    have h6 : ‖B‖ * ‖u k‖ ≤ κ * ‖u k‖ :=
      mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
    linarith
  -- variation of constants and the convolution bound
  set G := ∑ k ∈ Finset.range T,
    ρ ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖) with hG
  have hxT : ‖x T‖ ≤ cF * ‖x 0‖ + cF * κ * G := by
    have hvc := varConst F x w hrecF T
    have h1 : ‖x T‖ ≤ ‖F ^ T *ᵥ x 0‖
        + ∑ k ∈ Finset.range T, ‖F ^ (T - 1 - k) *ᵥ w k‖ := by
      rw [hvc]
      exact (norm_add_le _ _).trans
        (add_le_add le_rfl (norm_sum_le _ _))
    have h2 : ‖F ^ T *ᵥ x 0‖ ≤ cF * ‖x 0‖ := by
      refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
      have h3 : ‖F ^ T‖ ≤ cF * ρ ^ T := hpow T
      have h4 : ρ ^ T ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
      have h5 := mul_le_mul_of_nonneg_right h3 (norm_nonneg (x 0))
      have h6 := mul_le_mul_of_nonneg_right h4 (norm_nonneg (x 0))
      nlinarith [norm_nonneg (x 0)]
    have h5 : ∑ k ∈ Finset.range T, ‖F ^ (T - 1 - k) *ᵥ w k‖
        ≤ cF * κ * G := by
      rw [hG, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h6 : ‖F ^ (T - 1 - k) *ᵥ w k‖
          ≤ (cF * ρ ^ (T - 1 - k)) * ‖w k‖ := by
        refine (Matrix.linfty_opNorm_mulVec _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (hpow _) (norm_nonneg _)
      have h7 : (cF * ρ ^ (T - 1 - k)) * ‖w k‖
          ≤ (cF * ρ ^ (T - 1 - k)) * (κ * (‖C *ᵥ x k‖ + ‖u k‖)) := by
        refine mul_le_mul_of_nonneg_left (hwk k) ?_
        positivity
      calc ‖F ^ (T - 1 - k) *ᵥ w k‖
          ≤ (cF * ρ ^ (T - 1 - k)) * (κ * (‖C *ᵥ x k‖ + ‖u k‖)) :=
            h6.trans h7
      _ = cF * κ * (ρ ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖)) := by ring
    linarith
  -- Cauchy–Schwarz: `G² ≤ (1-ρ)⁻¹ · 2S`
  set S := ∑ k ∈ Finset.range T, (‖C *ᵥ x k‖ ^ 2 + ‖u k‖ ^ 2) with hS
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact Finset.sum_nonneg fun k _ => by positivity
  have hG0 : 0 ≤ G := by
    rw [hG]
    refine Finset.sum_nonneg fun k _ => ?_
    positivity
  have hconv : G ^ 2 ≤ (1 - ρ)⁻¹ * (2 * S) := by
    set r := Real.sqrt ρ with hr
    have hrr : r * r = ρ := Real.mul_self_sqrt hρ0.le
    have hid : ∀ k, r ^ (T - 1 - k)
        * (r ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖))
        = ρ ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖) := by
      intro k
      rw [← mul_assoc, ← mul_pow, hrr]
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range T)
      (fun k => r ^ (T - 1 - k))
      (fun k => r ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖))
    simp only [hid] at hCS
    rw [← hG] at hCS
    -- first factor: reflected geometric sum
    have hgeo : ∑ k ∈ Finset.range T, (r ^ (T - 1 - k)) ^ 2
        ≤ (1 - ρ)⁻¹ := by
      have h1 : ∀ k, (r ^ (T - 1 - k)) ^ 2 = ρ ^ (T - 1 - k) := by
        intro k
        rw [← pow_mul, mul_comm (T - 1 - k) 2, pow_mul, sq, hrr]
      simp only [h1]
      rw [Finset.sum_range_reflect (fun j => ρ ^ j) T]
      have hpos : 0 < 1 - ρ := by linarith
      have hgs := geom_sum_eq (ne_of_lt hρ1) T
      have heq : (ρ ^ T - 1) / (ρ - 1) = (1 - ρ ^ T) / (1 - ρ) := by
        rw [show (1 - ρ ^ T) = -(ρ ^ T - 1) from by ring,
          show (1 - ρ) = -(ρ - 1) from by ring, neg_div_neg_eq]
      rw [hgs, heq, div_le_iff₀ hpos, inv_mul_cancel₀ (ne_of_gt hpos)]
      nlinarith [pow_pos hρ0 T]
    -- second factor: `ρ^j ≤ 1` and `(a+b)² ≤ 2(a²+b²)`
    have hsq : ∑ k ∈ Finset.range T,
        (r ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖)) ^ 2 ≤ 2 * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_le_sum fun k _ => ?_
      have h1 : (r ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖)) ^ 2
          = ρ ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖) ^ 2 := by
        rw [mul_pow, ← pow_mul, mul_comm (T - 1 - k) 2, pow_mul, sq, hrr]
      rw [h1]
      have h2 : ρ ^ (T - 1 - k) ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
      have h3 : (‖C *ᵥ x k‖ + ‖u k‖) ^ 2
          ≤ 2 * (‖C *ᵥ x k‖ ^ 2 + ‖u k‖ ^ 2) := by
        nlinarith [sq_nonneg (‖C *ᵥ x k‖ - ‖u k‖)]
      nlinarith [sq_nonneg (‖C *ᵥ x k‖ + ‖u k‖),
        pow_nonneg hρ0.le (T - 1 - k)]
    calc G ^ 2 ≤ (∑ k ∈ Finset.range T, (r ^ (T - 1 - k)) ^ 2)
          * ∑ k ∈ Finset.range T,
            (r ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖)) ^ 2 := hCS
    _ ≤ (1 - ρ)⁻¹ * (2 * S) := by
        have h4 : 0 ≤ ∑ k ∈ Finset.range T,
            (r ^ (T - 1 - k) * (‖C *ᵥ x k‖ + ‖u k‖)) ^ 2 :=
          Finset.sum_nonneg fun k _ => sq_nonneg _
        exact mul_le_mul hgeo hsq h4 hρinv.le
  -- assemble
  have hsq2 : ‖x T‖ ^ 2 ≤ 2 * (cF * ‖x 0‖) ^ 2 + 2 * (cF * κ) ^ 2
      * G ^ 2 := by
    have h1 : ‖x T‖ ^ 2 ≤ (cF * ‖x 0‖ + cF * κ * G) ^ 2 := by
      have h2 : 0 ≤ ‖x T‖ := norm_nonneg _
      nlinarith
    nlinarith [sq_nonneg (cF * ‖x 0‖ - cF * κ * G)]
  have h5 : 2 * (cF * κ) ^ 2 * G ^ 2
      ≤ 2 * (cF * κ) ^ 2 * ((1 - ρ)⁻¹ * (2 * S)) := by
    refine mul_le_mul_of_nonneg_left hconv ?_
    positivity
  have h6 : (0 : ℝ) ≤ ‖x 0‖ ^ 2 := sq_nonneg _
  nlinarith [sq_nonneg cF, sq_nonneg κ, mul_nonneg (sq_nonneg cF) hS0,
    mul_nonneg (mul_nonneg (sq_nonneg cF) (sq_nonneg κ)) h6,
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg cF) (sq_nonneg κ))
      hρinv.le) h6]

end LinearSystems
