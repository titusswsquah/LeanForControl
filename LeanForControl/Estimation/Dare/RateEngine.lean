import LeanForControl.Estimation.Dare.Main
import Architect

/-!
# The rate engine (E1)

Scalar and matrix helpers that turn the Phase-B/D convergence
machinery into geometric rates:

* `geom_conv_le` — the geometric convolution
  `∑_{j<T} ρ^{T-1-j}σ^j ≤ C·ρ'^T` for any `ρ' ∈ (max ρ σ, 1)`
  (the equal-rate log factor is dodged by widening);
* `rate_of_unroll_bound` — the master packaging: a sequence dominated
  by `a·ρ₀^T + K·(convolution)` is geometric;
* `diff_norm_mul_le` / `diff_norm_triple_le` — telescoped product
  differences;
* Lipschitz bounds for the gain chain (`innovInv_diff_norm_le`,
  `kGain_diff_norm_le`, `errMap_diff_norm_le`) — the rate versions of
  the D3 continuity lemmas;
* `norm_eq_zero_of_isEmpty` — the trivial marginal bound under C3w.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

/-! ### Scalar rate lemmas -/

/-- `(t+1)·q^t` is bounded for `q < 1`. -/
lemma exists_bound_nat_succ_mul_pow {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℕ, ((t : ℝ) + 1) * q ^ t ≤ C := by
  have hq' : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have hsum := summable_pow_mul_geometric_of_norm_lt_one
    (R := ℝ) 1 hq'
  have h1 : Tendsto (fun t : ℕ => (t : ℝ) ^ 1 * q ^ t) atTop
      (nhds 0) := hsum.tendsto_atTop_zero
  have h2 : Tendsto (fun t : ℕ => q ^ t) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have h3 : Tendsto (fun t : ℕ => ((t : ℝ) + 1) * q ^ t) atTop
      (nhds 0) := by
    have h4 := h1.add h2
    simp only [pow_one] at h4
    have h5 : (fun t : ℕ => ((t : ℝ) + 1) * q ^ t)
        = fun t : ℕ => (t : ℝ) * q ^ t + q ^ t := by
      funext t
      ring
    rw [h5]
    simpa using h4
  exact exists_bound_of_tendsto_zero h3

/-- **The geometric convolution bound**: a `ρ`-kernel against a
`σ`-drive is dominated at any rate strictly above both. -/
lemma geom_conv_le {ρ σ ρ' : ℝ} (hρ0 : 0 ≤ ρ) (hσ0 : 0 ≤ σ)
    (hρ : ρ < ρ') (hσ : σ < ρ') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      ∑ j ∈ Finset.range T, ρ ^ (T - 1 - j) * σ ^ j
        ≤ C * ρ' ^ T := by
  have hρ'0 : 0 < ρ' := lt_of_le_of_lt hρ0 hρ
  set m : ℝ := max ρ σ with hm
  have hm0 : 0 ≤ m := le_trans hρ0 (le_max_left _ _)
  have hmρ' : m < ρ' := max_lt hρ hσ
  set q : ℝ := m / ρ' with hq
  have hq0 : 0 ≤ q := div_nonneg hm0 hρ'0.le
  have hq1 : q < 1 := (div_lt_one hρ'0).mpr hmρ'
  obtain ⟨Cg, hCg0, hCgb⟩ := exists_bound_nat_succ_mul_pow hq0 hq1
  refine ⟨Cg / ρ', by positivity, fun T => ?_⟩
  cases T with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero,
      mul_one]
    positivity
  | succ t =>
    have hterm : ∀ j ∈ Finset.range (t + 1),
        ρ ^ (t + 1 - 1 - j) * σ ^ j ≤ m ^ t := by
      intro j hj
      have hj' : j ≤ t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 : ρ ^ (t - j) ≤ m ^ (t - j) :=
        pow_le_pow_left₀ hρ0 (le_max_left _ _) _
      have h2 : σ ^ j ≤ m ^ j :=
        pow_le_pow_left₀ hσ0 (le_max_right _ _) _
      have h3 : t + 1 - 1 - j = t - j := by omega
      calc ρ ^ (t + 1 - 1 - j) * σ ^ j
          = ρ ^ (t - j) * σ ^ j := by rw [h3]
      _ ≤ m ^ (t - j) * m ^ j := by
          refine mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = m ^ (t - j + j) := (pow_add m _ _).symm
      _ = m ^ t := by rw [Nat.sub_add_cancel hj']
    have hmq : m ^ t = q ^ t * ρ' ^ t := by
      rw [hq, div_pow]
      field_simp
    calc ∑ j ∈ Finset.range (t + 1), ρ ^ (t + 1 - 1 - j) * σ ^ j
        ≤ ∑ _j ∈ Finset.range (t + 1), m ^ t :=
          Finset.sum_le_sum hterm
    _ = ((t : ℝ) + 1) * m ^ t := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
    _ = (((t : ℝ) + 1) * q ^ t) * ρ' ^ t := by
        rw [hmq]
        ring
    _ ≤ Cg * ρ' ^ t :=
        mul_le_mul_of_nonneg_right (hCgb t) (by positivity)
    _ = Cg / ρ' * ρ' ^ (t + 1) := by
        rw [pow_succ]
        field_simp

/-- **The master rate lemma**: a sequence dominated by a geometric
head plus a geometric convolution is geometric. -/
lemma rate_of_unroll_bound {x : ℕ → ℝ} {a ρ₀ K ρ₁ σ : ℝ}
    (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hρ₀0 : 0 ≤ ρ₀) (hρ₀1 : ρ₀ < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁1 : ρ₁ < 1) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1)
    (hx : ∀ T, x T ≤ a * ρ₀ ^ T
      + K * ∑ j ∈ Finset.range T, ρ₁ ^ (T - 1 - j) * σ ^ j) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ T, x T ≤ C * ρ ^ T := by
  set m : ℝ := max ρ₀ (max ρ₁ σ) with hm
  have hm0 : 0 ≤ m := le_trans hρ₀0 (le_max_left _ _)
  have hm1 : m < 1 := by
    rw [hm, max_lt_iff, max_lt_iff]
    exact ⟨hρ₀1, hρ₁1, hσ1⟩
  set ρ : ℝ := (m + 1) / 2 with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ < 1 := by rw [hρdef]; linarith
  have hmρ : m < ρ := by rw [hρdef]; linarith
  obtain ⟨C₁, hC₁0, hC₁b⟩ := geom_conv_le hρ₁0 hσ0
    (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _))
      hmρ)
    (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _))
      hmρ)
  refine ⟨a + K * C₁, ρ, by positivity, hρ0, hρ1, fun T => ?_⟩
  have h1 : ρ₀ ^ T ≤ ρ ^ T :=
    pow_le_pow_left₀ hρ₀0
      (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hmρ)) T
  calc x T ≤ a * ρ₀ ^ T
      + K * ∑ j ∈ Finset.range T, ρ₁ ^ (T - 1 - j) * σ ^ j := hx T
  _ ≤ a * ρ ^ T + K * (C₁ * ρ ^ T) := by
      refine add_le_add (mul_le_mul_of_nonneg_left h1 ha) ?_
      exact mul_le_mul_of_nonneg_left (hC₁b T) hK
  _ = (a + K * C₁) * ρ ^ T := by ring

/-! ### Product-difference telescopes -/

variable {ι₁ ι₂ ι₃ ι₄ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
  [Fintype ι₄]

/-- Two-factor product difference. -/
lemma diff_norm_mul_le (X₁ X₂ : Matrix ι₁ ι₂ ℝ)
    (Y₁ Y₂ : Matrix ι₂ ι₃ ℝ) :
    ‖X₁ * Y₁ - X₂ * Y₂‖
      ≤ ‖X₁ - X₂‖ * ‖Y₁‖ + ‖X₂‖ * ‖Y₁ - Y₂‖ := by
  have hid : X₁ * Y₁ - X₂ * Y₂
      = (X₁ - X₂) * Y₁ + X₂ * (Y₁ - Y₂) := by
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hid]
  refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
  · exact Matrix.linfty_opNorm_mul _ _
  · exact Matrix.linfty_opNorm_mul _ _

/-- Three-factor product difference. -/
lemma diff_norm_triple_le (X₁ X₂ : Matrix ι₁ ι₂ ℝ)
    (Y₁ Y₂ : Matrix ι₂ ι₃ ℝ) (Z₁ Z₂ : Matrix ι₃ ι₄ ℝ) :
    ‖X₁ * Y₁ * Z₁ - X₂ * Y₂ * Z₂‖
      ≤ ‖X₁ - X₂‖ * ‖Y₁‖ * ‖Z₁‖ + ‖X₂‖ * ‖Y₁ - Y₂‖ * ‖Z₁‖
        + ‖X₂‖ * ‖Y₂‖ * ‖Z₁ - Z₂‖ := by
  have hid : X₁ * Y₁ * Z₁ - X₂ * Y₂ * Z₂
      = (X₁ - X₂) * Y₁ * Z₁ + X₂ * (Y₁ - Y₂) * Z₁
        + X₂ * Y₂ * (Z₁ - Z₂) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hid]
  refine le_trans (norm_add_le _ _) (add_le_add
    (le_trans (norm_add_le _ _) (add_le_add ?_ ?_)) ?_)
  · exact norm_triple_le _ _ _
  · exact norm_triple_le _ _ _
  · exact norm_triple_le _ _ _

/-! ### Lipschitz bounds along the gain chain -/

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

variable {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}

/-- The innovation inverse is Lipschitz on PSD arguments. -/
lemma innovInv_diff_norm_le (hR : R.PosDef) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X Y : Matrix ι ι ℝ,
      X.PosSemidef → Y.PosSemidef →
        ‖(innov C R X)⁻¹ - (innov C R Y)⁻¹‖ ≤ c * ‖X - Y‖ := by
  obtain ⟨bR, hbR, hbRb⟩ := innov_inv_norm_bound_general (C := C) hR
  refine ⟨bR * (‖C‖ * ‖Cᵀ‖) * bR, by positivity, fun X Y hX hY => ?_⟩
  have hXPD : (innov C R X).PosDef := innov_posDef hR hX
  have hYPD : (innov C R Y).PosDef := innov_posDef hR hY
  have hid : (innov C R X)⁻¹ - (innov C R Y)⁻¹
      = (innov C R X)⁻¹ * (innov C R Y - innov C R X)
        * (innov C R Y)⁻¹ := by
    have h1 : (innov C R X)⁻¹ * (innov C R Y - innov C R X)
        * (innov C R Y)⁻¹
        = (innov C R X)⁻¹ * (innov C R Y * (innov C R Y)⁻¹)
          - (innov C R X)⁻¹ * innov C R X * (innov C R Y)⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hYPD.isUnit),
      Matrix.nonsing_inv_mul _
        ((Matrix.isUnit_iff_isUnit_det _).mp hXPD.isUnit),
      Matrix.mul_one, Matrix.one_mul]
  have hdiff : innov C R Y - innov C R X = C * (Y - X) * Cᵀ := by
    unfold innov
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [hid]
  calc ‖(innov C R X)⁻¹ * (innov C R Y - innov C R X)
      * (innov C R Y)⁻¹‖
      ≤ ‖(innov C R X)⁻¹‖ * ‖innov C R Y - innov C R X‖
        * ‖(innov C R Y)⁻¹‖ := norm_triple_le _ _ _
  _ ≤ bR * (‖C‖ * ‖X - Y‖ * ‖Cᵀ‖) * bR := by
      have h2 : ‖innov C R Y - innov C R X‖
          ≤ ‖C‖ * ‖X - Y‖ * ‖Cᵀ‖ := by
        rw [hdiff]
        calc ‖C * (Y - X) * Cᵀ‖
            ≤ ‖C‖ * ‖Y - X‖ * ‖Cᵀ‖ := norm_triple_le _ _ _
        _ = ‖C‖ * ‖X - Y‖ * ‖Cᵀ‖ := by rw [norm_sub_rev]
      refine mul_le_mul (mul_le_mul (hbRb X hX) h2
        (norm_nonneg _) hbR) (hbRb Y hY) (norm_nonneg _) ?_
      positivity
  _ = bR * (‖C‖ * ‖Cᵀ‖) * bR * ‖X - Y‖ := by ring

/-- The Kalman gain is Lipschitz on PSD arguments (anchored at `Y`). -/
lemma kGain_diff_norm_le (hR : R.PosDef) {Y : Matrix ι ι ℝ}
    (hY : Y.PosSemidef) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : Matrix ι ι ℝ, X.PosSemidef →
      ‖kGain C R X - kGain C R Y‖ ≤ c * ‖X - Y‖ := by
  obtain ⟨bR, hbR, hbRb⟩ := innov_inv_norm_bound_general (C := C) hR
  obtain ⟨cI, hcI, hcIb⟩ := innovInv_diff_norm_le (C := C) hR
  refine ⟨‖Cᵀ‖ * bR + ‖Y‖ * ‖Cᵀ‖ * cI, by positivity,
    fun X hX => ?_⟩
  have hid : kGain C R X - kGain C R Y
      = (X - Y) * Cᵀ * (innov C R X)⁻¹
        + Y * Cᵀ * ((innov C R X)⁻¹ - (innov C R Y)⁻¹) := by
    unfold kGain
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hid]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(X - Y) * Cᵀ * (innov C R X)⁻¹‖
      ≤ ‖X - Y‖ * ‖Cᵀ‖ * bR := by
    calc ‖(X - Y) * Cᵀ * (innov C R X)⁻¹‖
        ≤ ‖X - Y‖ * ‖Cᵀ‖ * ‖(innov C R X)⁻¹‖ :=
          norm_triple_le _ _ _
    _ ≤ ‖X - Y‖ * ‖Cᵀ‖ * bR := by
        refine mul_le_mul_of_nonneg_left (hbRb X hX) ?_
        positivity
  have h2 : ‖Y * Cᵀ * ((innov C R X)⁻¹ - (innov C R Y)⁻¹)‖
      ≤ ‖Y‖ * ‖Cᵀ‖ * (cI * ‖X - Y‖) := by
    calc ‖Y * Cᵀ * ((innov C R X)⁻¹ - (innov C R Y)⁻¹)‖
        ≤ ‖Y‖ * ‖Cᵀ‖
          * ‖(innov C R X)⁻¹ - (innov C R Y)⁻¹‖ :=
          norm_triple_le _ _ _
    _ ≤ ‖Y‖ * ‖Cᵀ‖ * (cI * ‖X - Y‖) := by
        refine mul_le_mul_of_nonneg_left (hcIb X Y hX hY) ?_
        positivity
  calc ‖(X - Y) * Cᵀ * (innov C R X)⁻¹‖
      + ‖Y * Cᵀ * ((innov C R X)⁻¹ - (innov C R Y)⁻¹)‖
      ≤ ‖X - Y‖ * ‖Cᵀ‖ * bR + ‖Y‖ * ‖Cᵀ‖ * (cI * ‖X - Y‖) :=
        add_le_add h1 h2
  _ = (‖Cᵀ‖ * bR + ‖Y‖ * ‖Cᵀ‖ * cI) * ‖X - Y‖ := by ring

/-- The closed loop is Lipschitz on PSD arguments (anchored at `Y`). -/
lemma errMap_diff_norm_le (hR : R.PosDef) {A : Matrix ι ι ℝ}
    {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ X : Matrix ι ι ℝ, X.PosSemidef →
      ‖errMap C R A X - errMap C R A Y‖ ≤ c * ‖X - Y‖ := by
  obtain ⟨cK, hcK, hcKb⟩ := kGain_diff_norm_le (C := C) hR hY
  refine ⟨‖A‖ * (cK * ‖C‖), by positivity, fun X hX => ?_⟩
  have hid : errMap C R A X - errMap C R A Y
      = A * ((kGain C R Y - kGain C R X) * C) := by
    unfold errMap
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one,
      Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [hid]
  calc ‖A * ((kGain C R Y - kGain C R X) * C)‖
      ≤ ‖A‖ * ‖(kGain C R Y - kGain C R X) * C‖ :=
        Matrix.linfty_opNorm_mul _ _
  _ ≤ ‖A‖ * (‖kGain C R Y - kGain C R X‖ * ‖C‖) := by
      refine mul_le_mul_of_nonneg_left
        (Matrix.linfty_opNorm_mul _ _) (norm_nonneg A)
  _ ≤ ‖A‖ * (cK * ‖X - Y‖ * ‖C‖) := by
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg A)
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg C)
      rw [norm_sub_rev]
      exact hcKb X hX
  _ = ‖A‖ * (cK * ‖C‖) * ‖X - Y‖ := by ring

/-! ### The empty marginal -/

/-- A matrix with empty row type has zero `L∞` norm (the trivial
power bound under C3w). -/
lemma norm_eq_zero_of_isEmpty {ι' κ' : Type*} [Fintype ι']
    [Fintype κ'] [IsEmpty ι'] (M : Matrix ι' κ' ℝ) : ‖M‖ = 0 := by
  have h : ‖M‖₊ = 0 := by
    rw [Matrix.linfty_opNNNorm_def, Finset.univ_eq_empty,
      Finset.sup_empty]
    rfl
  calc ‖M‖ = ((‖M‖₊ : ℝ)) := rfl
  _ = 0 := by rw [h]; rfl

end Dare
end Estimation
