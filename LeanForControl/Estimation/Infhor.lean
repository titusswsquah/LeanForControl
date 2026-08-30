import LeanForControl.Estimation.Coercive
import LeanForControl.LinearSystems.ConstrainedQuadratic
import Architect

/-!
# The infinite-horizon limit (`prop:infhor`)

The value `V_T⁰` is nondecreasing in the horizon and (under C1 ∧ C2)
bounded, so it converges; the full gap formula then makes the optimal
decisions Cauchy across horizons. This file builds that convergence layer:

* `value_mono`, `valueLim` (the limit `V̄(a) = ⨆_T V_T⁰(a)`);
* the deviation estimates: for `T ≤ τ` the `τ`-optimum, truncated, is
  feasible at horizon `T` with gap at most `V̄ - V_T⁰`, which bounds the
  initial-error and per-stage deviations of the optimizers
  (`optInit_cauchy_bound`, `optCtrl_cauchy_bound`);
* convergence of the optimal initial errors and controls
  (`optInitLim`, `optCtrlLim`).

Everything is per-mismatch (`a` fixed); the uniform (quadratic-in-`a`)
statements come with the `Π`-matrix layer in `Estimation/Gas.lean`.
-/

namespace Estimation

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

variable {n₁ n₂ m p : ℕ}

namespace FIESystem

variable (Sys : FIESystem n₁ n₂ m p)

/-- The value is nondecreasing in the horizon. -/
theorem value_mono (a : Fin n₁ ⊕ Fin n₂ → ℝ) {T τ : ℕ} (h : T ≤ τ) :
    Sys.value a T ≤ Sys.value a τ := by
  calc Sys.value a T
      ≤ Sys.fieCost a (Sys.optInit a τ) (Sys.lq.optCtrl (Sys.optInit a τ) τ) T :=
        Sys.value_le_fieCost (Sys.optInit_feasible a τ) _ T
  _ ≤ Sys.fieCost a (Sys.optInit a τ) (Sys.lq.optCtrl (Sys.optInit a τ) τ) τ := by
      unfold fieCost
      have := Sys.lq.cost_mono (Sys.optInit a τ)
        (Sys.lq.optCtrl (Sys.optInit a τ) τ) h
      linarith
  _ = Sys.value a τ := Sys.fieCost_optCtrl a τ

/-- The limiting value `V̄(a) = ⨆_T V_T⁰(a)` (finite under C1 ∧ C2 by
`exists_value_bound`; junk otherwise). -/
noncomputable def valueLim (a : Fin n₁ ⊕ Fin n₂ → ℝ) : ℝ :=
  ⨆ T, Sys.value a T

/-- Under C1 ∧ C2 the values converge to `valueLim` from below. -/
theorem tendsto_value (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Tendsto (fun T => Sys.value a T) atTop (nhds (Sys.valueLim a)) := by
  obtain ⟨c, hc, hb⟩ := Sys.exists_value_bound_C2 hC2
  refine tendsto_atTop_ciSup (fun T τ h => Sys.value_mono a h) ⟨c * ‖a‖ ^ 2, ?_⟩
  rintro x ⟨T, rfl⟩
  exact hb a T

theorem value_le_valueLim (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.value a T ≤ Sys.valueLim a := by
  obtain ⟨c, hc, hb⟩ := Sys.exists_value_bound_C2 hC2
  refine le_ciSup ⟨c * ‖a‖ ^ 2, ?_⟩ T
  rintro x ⟨τ, rfl⟩
  exact hb a τ

theorem valueLim_le (a : Fin n₁ ⊕ Fin n₂ → ℝ) {b : ℝ}
    (h : ∀ T, Sys.value a T ≤ b) : Sys.valueLim a ≤ b :=
  ciSup_le h

/-- **The truncation gap bound**: for `T ≤ τ` the `τ`-optimal decisions,
viewed at horizon `T`, deviate from the `T`-optimum by at most
`V̄(a) - V_T⁰(a)` in the gap metric. -/
theorem truncation_gap (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) {T τ : ℕ} (h : T ≤ τ) :
    Sys.fieCost 0 (Sys.optInit a τ - Sys.optInit a T)
      (fun j => Sys.lq.optCtrl (Sys.optInit a τ) τ j
        - Sys.lq.optCtrl (Sys.optInit a T) T j) T
      ≤ Sys.valueLim a - Sys.value a T := by
  have hgap := Sys.fieCost_gap (Sys.optInit_feasible a τ)
    (Sys.lq.optCtrl (Sys.optInit a τ) τ) T
  have h1 : Sys.fieCost a (Sys.optInit a τ) (Sys.lq.optCtrl (Sys.optInit a τ) τ) T
      ≤ Sys.value a τ := by
    unfold fieCost
    have h2 := Sys.lq.cost_mono (Sys.optInit a τ)
      (Sys.lq.optCtrl (Sys.optInit a τ) τ) h
    have h3 := Sys.fieCost_optCtrl a τ
    unfold fieCost at h3
    linarith
  have h4 := Sys.value_le_valueLim hC2 a τ
  linarith


/-- Sup norms over the sum index are controlled by block norms. -/
lemma sq_norm_le_blocks (v : Fin n₁ ⊕ Fin n₂ → ℝ) :
    ‖v‖ ^ 2 ≤ ‖blk₁ v‖ ^ 2 + ‖blk₂ v‖ ^ 2 := by
  have h1 : ‖v‖ ≤ max ‖blk₁ v‖ ‖blk₂ v‖ := by
    refine (pi_norm_le_iff_of_nonneg (le_max_iff.mpr (Or.inl (norm_nonneg _)))).mpr
      fun i => ?_
    cases i with
    | inl i => exact le_trans (norm_le_pi_norm (blk₁ v) i) (le_max_left _ _)
    | inr i => exact le_trans (norm_le_pi_norm (blk₂ v) i) (le_max_right _ _)
  have h2 : ‖v‖ ^ 2 ≤ max ‖blk₁ v‖ ‖blk₂ v‖ ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
    gcongr
  rcases max_cases ‖blk₁ v‖ ‖blk₂ v‖ with ⟨heq, -⟩ | ⟨heq, -⟩ <;>
    rw [heq] at h2 <;> nlinarith [sq_nonneg ‖blk₁ v‖, sq_nonneg ‖blk₂ v‖]

/-- **Initial-error deviation bound**: optimal initial errors at two
horizons differ by at most the value gap, in norm. -/
theorem exists_optInit_dev_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n₁ ⊕ Fin n₂ → ℝ) {T τ : ℕ}, T ≤ τ →
      Sys.value a τ ≤ Sys.valueLim a →
      ‖Sys.optInit a τ - Sys.optInit a T‖ ^ 2
        ≤ C * (Sys.valueLim a - Sys.value a T) := by
  obtain ⟨C₁, hC₁, hr₁⟩ := Sys.hSig₁.exists_sq_norm_mulVec_le
  obtain ⟨C₂, hC₂, hr₂⟩ := Sys.hSig₂.exists_sq_norm_mulVec_le
  refine ⟨C₁ + C₂, by positivity, ?_⟩
  intro a T τ h hτ
  set d := Sys.optInit a τ - Sys.optInit a T with hd
  set δf : ℕ → Fin m → ℝ := fun j => Sys.lq.optCtrl (Sys.optInit a τ) τ j
    - Sys.lq.optCtrl (Sys.optInit a T) T j with hδf
  have hdir : Sys.FeasibleDir d :=
    Sys.feasibleDir_sub (Sys.optInit_feasible a τ) (Sys.optInit_feasible a T)
  obtain ⟨w, hw⟩ := hdir
  have hw1 : blk₁ d = Sys.Sig₁ *ᵥ blk₁ w := by
    rw [hw, Sys.Jmat_mulVec]
    simp
  have hw2 : blk₂ d = Sys.Sig₂ *ᵥ blk₂ w := by
    rw [hw, Sys.Jmat_mulVec]
    simp
  -- the zero-mismatch deviation cost is at most the value gap
  have hgap := Sys.fieCost_gap (Sys.optInit_feasible a τ)
    (Sys.lq.optCtrl (Sys.optInit a τ) τ) T
  rw [← hd] at hgap
  have hcost : Sys.fieCost a (Sys.optInit a τ)
      (Sys.lq.optCtrl (Sys.optInit a τ) τ) T ≤ Sys.valueLim a := by
    have h2 : Sys.fieCost a (Sys.optInit a τ)
        (Sys.lq.optCtrl (Sys.optInit a τ) τ) T
        ≤ Sys.fieCost a (Sys.optInit a τ)
            (Sys.lq.optCtrl (Sys.optInit a τ) τ) τ := by
      unfold fieCost
      have := Sys.lq.cost_mono (Sys.optInit a τ)
        (Sys.lq.optCtrl (Sys.optInit a τ) τ) h
      linarith
    rw [Sys.fieCost_optCtrl a τ] at h2
    linarith
  have hdev : Sys.fieCost 0 d δf T ≤ Sys.valueLim a - Sys.value a T := by
    rw [hδf]
    linarith [hgap, hcost]
  -- extract the prior energies
  have hsplit : Sys.fieCost 0 d δf T
      = quadForm (symmPinv Sys.hSig₁.1) (blk₁ d)
        + quadForm (symmPinv Sys.hSig₂.1) (blk₂ d)
        + Sys.lq.cost d δf T := by
    unfold fieCost priorPenalty
    rw [sub_zero]
  have hlqnn : 0 ≤ Sys.lq.cost d δf T :=
    Finset.sum_nonneg fun k _ => Sys.lq.stage_nonneg _ _
  have hq1nn := Sys.hSig₁.symmPinv.quadForm_nonneg (blk₁ d)
  have hq2nn := Sys.hSig₂.symmPinv.quadForm_nonneg (blk₂ d)
  have hb1 : ‖blk₁ d‖ ^ 2
      ≤ C₁ * quadForm (symmPinv Sys.hSig₁.1) (blk₁ d) := by
    rw [hw1]
    calc ‖Sys.Sig₁ *ᵥ blk₁ w‖ ^ 2 ≤ C₁ * quadForm Sys.Sig₁ (blk₁ w) := hr₁ _
    _ = C₁ * quadForm (symmPinv Sys.hSig₁.1) (Sys.Sig₁ *ᵥ blk₁ w) := by
        rw [quadForm_symmPinv_mulVec Sys.hSig₁]
  have hb2 : ‖blk₂ d‖ ^ 2
      ≤ C₂ * quadForm (symmPinv Sys.hSig₂.1) (blk₂ d) := by
    rw [hw2]
    calc ‖Sys.Sig₂ *ᵥ blk₂ w‖ ^ 2 ≤ C₂ * quadForm Sys.Sig₂ (blk₂ w) := hr₂ _
    _ = C₂ * quadForm (symmPinv Sys.hSig₂.1) (Sys.Sig₂ *ᵥ blk₂ w) := by
        rw [quadForm_symmPinv_mulVec Sys.hSig₂]
  have hfin : ‖d‖ ^ 2 ≤ ‖blk₁ d‖ ^ 2 + ‖blk₂ d‖ ^ 2 := sq_norm_le_blocks d
  nlinarith [hsplit ▸ hdev, mul_le_mul_of_nonneg_left hq1nn hC₂.le,
    mul_le_mul_of_nonneg_left hq2nn hC₁.le,
    mul_le_mul_of_nonneg_left hq1nn hC₁.le,
    mul_le_mul_of_nonneg_left hq2nn hC₂.le]

/-- **Control deviation bound**: the optimal noise decisions at two
horizons differ stagewise by at most the value gap. -/
theorem exists_optCtrl_dev_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n₁ ⊕ Fin n₂ → ℝ) (k : ℕ) {T τ : ℕ},
      k < T → T ≤ τ → Sys.value a τ ≤ Sys.valueLim a →
      ‖Sys.lq.optCtrl (Sys.optInit a τ) τ k
        - Sys.lq.optCtrl (Sys.optInit a T) T k‖ ^ 2
        ≤ C * (Sys.valueLim a - Sys.value a T) := by
  obtain ⟨cq, hcq, hq⟩ := Sys.hQi.exists_le_quadForm
  refine ⟨cq⁻¹, by positivity, ?_⟩
  intro a k T τ hk h hτ
  set d := Sys.optInit a τ - Sys.optInit a T with hd
  set δf : ℕ → Fin m → ℝ := fun j => Sys.lq.optCtrl (Sys.optInit a τ) τ j
    - Sys.lq.optCtrl (Sys.optInit a T) T j with hδf
  have hgap := Sys.fieCost_gap (Sys.optInit_feasible a τ)
    (Sys.lq.optCtrl (Sys.optInit a τ) τ) T
  rw [← hd] at hgap
  have hcost : Sys.fieCost a (Sys.optInit a τ)
      (Sys.lq.optCtrl (Sys.optInit a τ) τ) T ≤ Sys.valueLim a := by
    have h2 : Sys.fieCost a (Sys.optInit a τ)
        (Sys.lq.optCtrl (Sys.optInit a τ) τ) T
        ≤ Sys.fieCost a (Sys.optInit a τ)
            (Sys.lq.optCtrl (Sys.optInit a τ) τ) τ := by
      unfold fieCost
      have := Sys.lq.cost_mono (Sys.optInit a τ)
        (Sys.lq.optCtrl (Sys.optInit a τ) τ) h
      linarith
    rw [Sys.fieCost_optCtrl a τ] at h2
    linarith
  have hdev : Sys.fieCost 0 d δf T ≤ Sys.valueLim a - Sys.value a T := by
    rw [hδf]
    linarith [hgap, hcost]
  -- the k-th stage of the deviation cost is dominated by the total
  have hstage : quadForm Sys.Qi (δf k) ≤ Sys.fieCost 0 d δf T := by
    have h5 : quadForm Sys.lq.Qs (Sys.lq.traj d δf k) + quadForm Sys.lq.Ru (δf k)
        ≤ Sys.lq.cost d δf T :=
      Finset.single_le_sum (f := fun j =>
        quadForm Sys.lq.Qs (Sys.lq.traj d δf j) + quadForm Sys.lq.Ru (δf j))
        (fun j _ => Sys.lq.stage_nonneg _ _) (Finset.mem_range.mpr hk)
    have h6 : 0 ≤ quadForm Sys.lq.Qs (Sys.lq.traj d δf k) :=
      Sys.lq.hQs.quadForm_nonneg _
    have h7 : 0 ≤ Sys.priorPenalty 0 d := Sys.priorPenalty_nonneg 0 d
    have h8 : quadForm Sys.lq.Ru (δf k) = quadForm Sys.Qi (δf k) := rfl
    unfold fieCost
    linarith
  have h9 := hq (δf k)
  have h10 : quadForm Sys.Qi (δf k) ≤ Sys.valueLim a - Sys.value a T :=
    le_trans hstage hdev
  change ‖δf k‖ ^ 2 ≤ cq⁻¹ * (Sys.valueLim a - Sys.value a T)
  have h11 : ‖δf k‖ ^ 2 = cq⁻¹ * (cq * ‖δf k‖ ^ 2) := by
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcq), one_mul]
  rw [h11]
  have h12 : cq⁻¹ * (cq * ‖δf k‖ ^ 2) ≤ cq⁻¹ * quadForm Sys.Qi (δf k) :=
    mul_le_mul_of_nonneg_left h9 (by positivity)
  have h13 : cq⁻¹ * quadForm Sys.Qi (δf k)
      ≤ cq⁻¹ * (Sys.valueLim a - Sys.value a T) :=
    mul_le_mul_of_nonneg_left h10 (by positivity)
  linarith


/-! ### Convergence of the optimizers -/

/-- The optimal initial errors form a Cauchy sequence in the horizon. -/
theorem optInit_cauchySeq (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    CauchySeq (fun T => Sys.optInit a T) := by
  obtain ⟨C, hC, hb⟩ := Sys.exists_optInit_dev_bound
  rw [Metric.cauchySeq_iff']
  intro ε hε
  -- pick `N` with `C·(V̄ - V_N) < ε²`
  have htend := Sys.tendsto_value hC2 a
  have h1 : Tendsto (fun T => C * (Sys.valueLim a - Sys.value a T)) atTop
      (nhds 0) := by
    have h2 : Tendsto (fun T => Sys.valueLim a - Sys.value a T) atTop
        (nhds 0) := by
      have := htend.const_sub (Sys.valueLim a)
      simpa using this
    simpa using h2.const_mul C
  have h3 : ∀ᶠ T in atTop, C * (Sys.valueLim a - Sys.value a T) < ε ^ 2 :=
    h1.eventually_lt_const (by positivity)
  obtain ⟨N, hN⟩ := h3.exists
  refine ⟨N, fun τ hτ => ?_⟩
  have h4 := hb a hτ (Sys.value_le_valueLim hC2 a τ)
  rw [dist_eq_norm]
  have h5 : ‖Sys.optInit a τ - Sys.optInit a N‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt h4 hN
  nlinarith [norm_nonneg (Sys.optInit a τ - Sys.optInit a N), hε]

/-- The limiting optimal initial error `ē(0)`. -/
noncomputable def optInitLim (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Fin n₁ ⊕ Fin n₂ → ℝ :=
  limUnder atTop (fun T => Sys.optInit a T)

theorem tendsto_optInit (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Tendsto (fun T => Sys.optInit a T) atTop (nhds (Sys.optInitLim a)) := by
  have h := (Sys.optInit_cauchySeq hC2 a).tendsto_limUnder
  exact h

/-- The optimal controls converge stagewise. -/
theorem optCtrl_cauchySeq (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (k : ℕ) :
    CauchySeq (fun T => Sys.lq.optCtrl (Sys.optInit a T) T k) := by
  obtain ⟨C, hC, hb⟩ := Sys.exists_optCtrl_dev_bound
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have htend := Sys.tendsto_value hC2 a
  have h1 : Tendsto (fun T => C * (Sys.valueLim a - Sys.value a T)) atTop
      (nhds 0) := by
    have h2 : Tendsto (fun T => Sys.valueLim a - Sys.value a T) atTop
        (nhds 0) := by
      have := htend.const_sub (Sys.valueLim a)
      simpa using this
    simpa using h2.const_mul C
  have h3 : ∀ᶠ T in atTop, C * (Sys.valueLim a - Sys.value a T) < ε ^ 2 :=
    h1.eventually_lt_const (by positivity)
  obtain ⟨N, hN, hNk⟩ := (h3.and (eventually_gt_atTop k)).exists
  refine ⟨N, fun τ hτ => ?_⟩
  have h4 := hb a k hNk hτ (Sys.value_le_valueLim hC2 a τ)
  rw [dist_eq_norm]
  have h5 : ‖Sys.lq.optCtrl (Sys.optInit a τ) τ k
      - Sys.lq.optCtrl (Sys.optInit a N) N k‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt h4 hN
  nlinarith [norm_nonneg (Sys.lq.optCtrl (Sys.optInit a τ) τ k
    - Sys.lq.optCtrl (Sys.optInit a N) N k), hε]

/-- The limiting optimal noise sequence `ω̄`. -/
noncomputable def optCtrlLim (a : Fin n₁ ⊕ Fin n₂ → ℝ) (k : ℕ) :
    Fin m → ℝ :=
  limUnder atTop (fun T => Sys.lq.optCtrl (Sys.optInit a T) T k)

theorem tendsto_optCtrl (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (k : ℕ) :
    Tendsto (fun T => Sys.lq.optCtrl (Sys.optInit a T) T k) atTop
      (nhds (Sys.optCtrlLim a k)) :=
  (Sys.optCtrl_cauchySeq hC2 a k).tendsto_limUnder

/-! ### Identification of the limit

The limiting pair `(ē₀, ω̄)` inherits the structural properties of the
finite-horizon optimizers: the antistable block of `ē₀` vanishes (forced
by `exists_optInit_blk₂_decay`), the support constraint survives the
limit (closedness of ranges), and every truncated cost of the limit is
dominated by `V̄`. -/

section LimitIdentification

private lemma continuous_blk₁ :
    Continuous fun e : Fin n₁ ⊕ Fin n₂ → ℝ => blk₁ e :=
  continuous_pi fun i => continuous_apply (Sum.inl i)

private lemma continuous_blk₂ :
    Continuous fun e : Fin n₁ ⊕ Fin n₂ → ℝ => blk₂ e :=
  continuous_pi fun i => continuous_apply (Sum.inr i)

private lemma continuous_quadForm {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) : Continuous fun v : ι → ℝ => quadForm M v :=
  continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/-- The antistable block of the optimal initial error tends to zero. -/
theorem tendsto_optInit_blk₂_zero (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Tendsto (fun T => blk₂ (Sys.optInit a T)) atTop (nhds 0) := by
  obtain ⟨c, hc, hd⟩ := Sys.exists_optInit_blk₂_decay hC1 hC2
  rw [Metric.tendsto_atTop]
  intro ε hε
  set J : ℕ := ⌊c * ‖a‖ ^ 2 / ε ^ 2⌋₊ + 1 with hJ
  have hJpos : 0 < (J : ℝ) := by positivity
  have hJbig : c * ‖a‖ ^ 2 < ε ^ 2 * J := by
    have h1 : c * ‖a‖ ^ 2 / ε ^ 2 < (J : ℝ) := by
      rw [hJ]
      push_cast
      exact Nat.lt_floor_add_one _
    calc c * ‖a‖ ^ 2 = c * ‖a‖ ^ 2 / ε ^ 2 * ε ^ 2 := by
          field_simp
    _ < J * ε ^ 2 := by
          exact mul_lt_mul_of_pos_right h1 (by positivity)
    _ = ε ^ 2 * J := mul_comm _ _
  refine ⟨(n₁ + n₂) * J, fun T hT => ?_⟩
  have h2 := hd a J T hT
  rw [dist_zero_right]
  have h3 : ‖blk₂ (Sys.optInit a T)‖ ^ 2 < ε ^ 2 := by
    by_contra h4
    push Not at h4
    have h5 : ε ^ 2 * J ≤ (J : ℝ) * ‖blk₂ (Sys.optInit a T)‖ ^ 2 := by
      calc ε ^ 2 * J ≤ ‖blk₂ (Sys.optInit a T)‖ ^ 2 * J :=
            mul_le_mul_of_nonneg_right h4 hJpos.le
      _ = (J : ℝ) * ‖blk₂ (Sys.optInit a T)‖ ^ 2 := mul_comm _ _
    linarith
  nlinarith [norm_nonneg (blk₂ (Sys.optInit a T)), hε]

/-- **The antistable block of the limiting optimal initial error is
zero** — the structural heart of `prop:infhor`. -/
theorem blk₂_optInitLim_eq_zero (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    blk₂ (Sys.optInitLim a) = 0 :=
  tendsto_nhds_unique
    ((continuous_blk₂.tendsto _).comp (Sys.tendsto_optInit hC2 a))
    (Sys.tendsto_optInit_blk₂_zero hC1 hC2 a)

/-- The limiting optimal initial error stays feasible: ranges of the
prior blocks are closed. -/
theorem optInitLim_feasible (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.Feasible a (Sys.optInitLim a) := by
  have htend : Tendsto (fun T => Sys.optInit a T - a) atTop
      (nhds (Sys.optInitLim a - a)) :=
    (Sys.tendsto_optInit hC2 a).sub_const a
  constructor
  · have hcl : IsClosed
        (LinearMap.range Sys.Sig₁.mulVecLin : Set (Fin n₁ → ℝ)) :=
      Submodule.closed_of_finiteDimensional _
    have hmem : ∀ T, blk₁ (Sys.optInit a T - a)
        ∈ LinearMap.range Sys.Sig₁.mulVecLin := by
      intro T
      obtain ⟨z, hz⟩ := (Sys.optInit_feasible a T).1
      exact ⟨z, by rw [Matrix.mulVecLin_apply, ← hz]⟩
    obtain ⟨z, hz⟩ := hcl.mem_of_tendsto
      ((continuous_blk₁.tendsto _).comp htend)
      (Filter.Eventually.of_forall hmem)
    exact ⟨z, by rw [← hz, Matrix.mulVecLin_apply]⟩
  · have hcl : IsClosed
        (LinearMap.range Sys.Sig₂.mulVecLin : Set (Fin n₂ → ℝ)) :=
      Submodule.closed_of_finiteDimensional _
    have hmem : ∀ T, blk₂ (Sys.optInit a T - a)
        ∈ LinearMap.range Sys.Sig₂.mulVecLin := by
      intro T
      obtain ⟨w, hw⟩ := (Sys.optInit_feasible a T).2
      exact ⟨w, by rw [Matrix.mulVecLin_apply, ← hw]⟩
    obtain ⟨w, hw⟩ := hcl.mem_of_tendsto
      ((continuous_blk₂.tendsto _).comp htend)
      (Filter.Eventually.of_forall hmem)
    exact ⟨w, by rw [← hw, Matrix.mulVecLin_apply]⟩

/-- Convergence of the finite-horizon optimal trajectories, pointwise in
time. -/
theorem tendsto_traj (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) : ∀ k,
    Tendsto (fun T => Sys.lq.traj (Sys.optInit a T)
        (Sys.lq.optCtrl (Sys.optInit a T) T) k) atTop
      (nhds (Sys.lq.traj (Sys.optInitLim a) (Sys.optCtrlLim a) k))
  | 0 => by
    simpa only [LQSystem.traj_zero] using Sys.tendsto_optInit hC2 a
  | k + 1 => by
    simp only [LQSystem.traj_succ]
    exact (((continuous_const.matrix_mulVec continuous_id).tendsto
        _).comp (tendsto_traj hC1 hC2 a k)).add
      (((continuous_const.matrix_mulVec continuous_id).tendsto _).comp
        (Sys.tendsto_optCtrl hC2 a k))

/-- Every truncation of the limiting objective is dominated by `V̄`:
the limit pair is "infinite-horizon feasible with value at most `V̄`". -/
theorem truncated_cost_le_valueLim (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (N : ℕ) :
    Sys.priorPenalty a (Sys.optInitLim a)
      + Sys.lq.cost (Sys.optInitLim a) (Sys.optCtrlLim a) N
        ≤ Sys.valueLim a := by
  have hprior : Tendsto (fun T => Sys.priorPenalty a (Sys.optInit a T))
      atTop (nhds (Sys.priorPenalty a (Sys.optInitLim a))) := by
    have htend : Tendsto (fun T => Sys.optInit a T - a) atTop
        (nhds (Sys.optInitLim a - a)) :=
      (Sys.tendsto_optInit hC2 a).sub_const a
    unfold priorPenalty
    exact (((continuous_quadForm _).tendsto _).comp
        ((continuous_blk₁.tendsto _).comp htend)).add
      (((continuous_quadForm _).tendsto _).comp
        ((continuous_blk₂.tendsto _).comp htend))
  have hcost : Tendsto (fun T => Sys.lq.cost (Sys.optInit a T)
      (Sys.lq.optCtrl (Sys.optInit a T) T) N) atTop
      (nhds (Sys.lq.cost (Sys.optInitLim a) (Sys.optCtrlLim a) N)) := by
    unfold LQSystem.cost
    refine tendsto_finset_sum _ fun k _ => ?_
    exact (((continuous_quadForm _).tendsto _).comp
        (Sys.tendsto_traj hC1 hC2 a k)).add
      (((continuous_quadForm _).tendsto _).comp
        (Sys.tendsto_optCtrl hC2 a k))
  refine le_of_tendsto (hprior.add hcost) ?_
  filter_upwards [eventually_ge_atTop N] with T hT
  have h1 : Sys.lq.cost (Sys.optInit a T)
      (Sys.lq.optCtrl (Sys.optInit a T) T) N
        ≤ Sys.lq.cost (Sys.optInit a T)
          (Sys.lq.optCtrl (Sys.optInit a T) T) T :=
    Sys.lq.cost_mono _ _ hT
  have h2 : Sys.priorPenalty a (Sys.optInit a T)
      + Sys.lq.cost (Sys.optInit a T)
        (Sys.lq.optCtrl (Sys.optInit a T) T) T = Sys.value a T := by
    have h3 := Sys.fieCost_optCtrl a T
    unfold fieCost at h3
    exact h3
  have h4 := Sys.value_le_valueLim hC2 a T
  linarith

end LimitIdentification

/-! ### The explicit infinite-horizon value (`prop:infhor`)

Under C1 the reduced Riccati iteration has a stabilizing limit `P_∞`
(staged `fact:lqr`), and the limiting value admits the explicit
characterization
`V̄(a) = min_{ξ ∈ a₁ + ran Σ₁} ‖ξ - a₁‖²_{Σ₁†} + ‖a₂‖²_{Σ₂⁻¹} + ‖ξ‖²_{P_∞}`,
attained at `ē₀ = (ξ_∞, 0)`. -/

section InfiniteHorizon

/-- The stabilizing solution `P_∞` of the reduced Riccati equation,
chosen from the staged `fact:lqr` (through `lqRed_lqr`). -/
noncomputable def Pinf (hC1 : Sys.C1) : Matrix (Fin n₁) (Fin n₁) ℝ :=
  Classical.choose (Sys.lqRed_lqr hC1)

lemma Pinf_posSemidef (hC1 : Sys.C1) : (Sys.Pinf hC1).PosSemidef :=
  (Classical.choose_spec (Sys.lqRed_lqr hC1)).1

lemma Pinf_fixed (hC1 : Sys.C1) :
    Sys.lqRed.step (Sys.Pinf hC1) = Sys.Pinf hC1 :=
  (Classical.choose_spec (Sys.lqRed_lqr hC1)).2.1

lemma Pinf_schur (hC1 : Sys.C1) :
    IsSchurStable (Sys.lqRed.Acl (Sys.Pinf hC1)) :=
  (Classical.choose_spec (Sys.lqRed_lqr hC1)).2.2.1

lemma tendsto_ricRed (hC1 : Sys.C1) :
    Tendsto (fun T => Sys.lqRed.ric T) atTop (nhds (Sys.Pinf hC1)) :=
  (Classical.choose_spec (Sys.lqRed_lqr hC1)).2.2.2.1

lemma tendsto_gainRed (hC1 : Sys.C1) :
    Tendsto (fun T => Sys.lqRed.gainK (Sys.lqRed.ric T)) atTop
      (nhds (Sys.lqRed.gainK (Sys.Pinf hC1))) :=
  (Classical.choose_spec (Sys.lqRed_lqr hC1)).2.2.2.2

/-- The optimal block-1 initial error of the infinite-horizon problem
(chosen from `exists_min_quadForm_over_range`). -/
noncomputable def xiInf (hC1 : Sys.C1) (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Fin n₁ → ℝ :=
  Classical.choose (exists_min_quadForm_over_range Sys.hSig₁
    (Sys.Pinf_posSemidef hC1) (blk₁ a))

lemma xiInf_feasible (hC1 : Sys.C1) (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    ∃ z, Sys.xiInf hC1 a - blk₁ a = Sys.Sig₁ *ᵥ z :=
  (Classical.choose_spec (exists_min_quadForm_over_range Sys.hSig₁
    (Sys.Pinf_posSemidef hC1) (blk₁ a))).1

lemma xiInf_min (hC1 : Sys.C1) (a : Fin n₁ ⊕ Fin n₂ → ℝ)
    (ξ' : Fin n₁ → ℝ) (hξ' : ∃ z, ξ' - blk₁ a = Sys.Sig₁ *ᵥ z) :
    quadForm (symmPinv Sys.hSig₁.1) (Sys.xiInf hC1 a - blk₁ a)
        + quadForm (Sys.Pinf hC1) (Sys.xiInf hC1 a)
      ≤ quadForm (symmPinv Sys.hSig₁.1) (ξ' - blk₁ a)
        + quadForm (Sys.Pinf hC1) ξ' :=
  (Classical.choose_spec (exists_min_quadForm_over_range Sys.hSig₁
    (Sys.Pinf_posSemidef hC1) (blk₁ a))).2 ξ' hξ'

/-- The explicit infinite-horizon value `V_∞(a)`. -/
noncomputable def valueInf (hC1 : Sys.C1) (a : Fin n₁ ⊕ Fin n₂ → ℝ) : ℝ :=
  quadForm (symmPinv Sys.hSig₁.1) (Sys.xiInf hC1 a - blk₁ a)
    + quadForm (symmPinv Sys.hSig₂.1) (blk₂ a)
    + quadForm (Sys.Pinf hC1) (Sys.xiInf hC1 a)

/-- The infinite-horizon candidate `(ξ_∞, 0)` with the frozen-gain noise
caps every finite-horizon value: `V_T⁰(a) ≤ V_∞(a)`. -/
theorem value_le_valueInf (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.value a T ≤ Sys.valueInf hC1 a := by
  classical
  set ξ := Sys.xiInf hC1 a with hξ
  set e₀c : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim ξ 0 with he₀c
  set ωc : ℕ → Fin m → ℝ := fun j =>
    -(Sys.lqRed.gainK (Sys.Pinf hC1)
      *ᵥ (Sys.lqRed.Acl (Sys.Pinf hC1) ^ j *ᵥ ξ)) with hωc
  -- feasibility of the candidate (block 2 via `Σ₂ ≻ 0`)
  have hblk₁ : blk₁ (e₀c - a) = ξ - blk₁ a := by
    rw [blk₁_sub, he₀c]
    congr 1
  have hblk₂ : blk₂ (e₀c - a) = -(blk₂ a) := by
    rw [blk₂_sub, he₀c]
    funext i
    simp [blk₂]
  have hfeas : Sys.Feasible a e₀c := by
    constructor
    · obtain ⟨z, hz⟩ := Sys.xiInf_feasible hC1 a
      exact ⟨z, by rw [hblk₁, hξ, hz]⟩
    · refine ⟨Sys.Sig₂⁻¹ *ᵥ (-(blk₂ a)), ?_⟩
      rw [hblk₂, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hC2.det_pos.ne'),
        Matrix.one_mulVec]
  have h1 := Sys.value_le_fieCost hfeas ωc T
  -- the candidate cost telescopes to at most `quadForm P_∞ ξ`
  have h2 : Sys.lq.cost e₀c ωc T ≤ quadForm (Sys.Pinf hC1) ξ := by
    rw [he₀c, Sys.lq_cost_sumElim_zero]
    rw [hωc, Sys.lqRed.cost_fixedGain (Sys.Pinf_posSemidef hC1)
      (Sys.Pinf_fixed hC1)]
    have h3 := (Sys.Pinf_posSemidef hC1).quadForm_nonneg
      (Sys.lqRed.Acl (Sys.Pinf hC1) ^ T *ᵥ ξ)
    linarith
  have h4 : Sys.priorPenalty a e₀c
      = quadForm (symmPinv Sys.hSig₁.1) (ξ - blk₁ a)
        + quadForm (symmPinv Sys.hSig₂.1) (blk₂ a) := by
    unfold priorPenalty
    rw [hblk₁, hblk₂, quadForm_neg]
  unfold valueInf
  unfold fieCost at h1
  rw [h4] at h1
  rw [← hξ]
  linarith

/-- `V̄(a) ≤ V_∞(a)`. -/
theorem valueLim_le_valueInf (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.valueLim a ≤ Sys.valueInf hC1 a :=
  Sys.valueLim_le a (Sys.value_le_valueInf hC1 hC2 a)

/-- The optimal decomposition of the limit pair: the endpoint of every
truncation bounds `V̄` from below, so the telescoped block-1 value of
`ē₀` fits under `V̄` — the "candidate budget" that `prop:gas` spends. -/
theorem priorPenalty_add_quadForm_Pinf_le_valueLim (hC1 : Sys.C1)
    (hC2 : Sys.C2) (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.priorPenalty a (Sys.optInitLim a)
      + quadForm (Sys.Pinf hC1) (blk₁ (Sys.optInitLim a))
        ≤ Sys.valueLim a := by
  set ē := Sys.optInitLim a with hē
  set ξb := blk₁ ē with hξb
  have hblk2 : blk₂ ē = 0 := Sys.blk₂_optInitLim_eq_zero hC1 hC2 a
  have hsum : ē = Sum.elim ξb 0 := by
    rw [hξb, ← hblk2, sumElim_blk]
  -- every truncation of the limit pair is below `V̄`
  have hstep : ∀ N, Sys.priorPenalty a ē
      + quadForm (Sys.lqRed.ric N) ξb ≤ Sys.valueLim a := by
    intro N
    have h1 := Sys.truncated_cost_le_valueLim hC1 hC2 a N
    rw [← hē] at h1
    have h2 : Sys.lq.cost ē (Sys.optCtrlLim a) N
        = Sys.lqRed.cost ξb (Sys.optCtrlLim a) N := by
      rw [hsum, Sys.lq_cost_sumElim_zero]
    have h3 : quadForm (Sys.lqRed.ric N) ξb
        ≤ Sys.lqRed.cost ξb (Sys.optCtrlLim a) N :=
      Sys.lqRed.quadForm_ric_le_cost _ _ N
    linarith [h2 ▸ h3]
  -- pass `N → ∞` through the Riccati limit
  have htd : Tendsto (fun N => Sys.priorPenalty a ē
      + quadForm (Sys.lqRed.ric N) ξb) atTop
      (nhds (Sys.priorPenalty a ē + quadForm (Sys.Pinf hC1) ξb)) := by
    refine Tendsto.const_add _ ?_
    have hcont : Continuous fun Mq : Matrix (Fin n₁) (Fin n₁) ℝ =>
        quadForm Mq ξb :=
      Continuous.dotProduct continuous_const
        (continuous_id.matrix_mulVec continuous_const)
    exact (hcont.tendsto _).comp (Sys.tendsto_ricRed hC1)
  exact le_of_tendsto htd (Filter.Eventually.of_forall hstep)

/-- `V_∞(a) ≤ V̄(a)`: the limit pair witnesses the infinite-horizon
minimum. -/
theorem valueInf_le_valueLim (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.valueInf hC1 a ≤ Sys.valueLim a := by
  set ē := Sys.optInitLim a with hē
  set ξb := blk₁ ē with hξb
  have hblk2 : blk₂ ē = 0 := Sys.blk₂_optInitLim_eq_zero hC1 hC2 a
  have hlim : Sys.priorPenalty a ē + quadForm (Sys.Pinf hC1) ξb
      ≤ Sys.valueLim a := by
    have h := Sys.priorPenalty_add_quadForm_Pinf_le_valueLim hC1 hC2 a
    rw [← hē, ← hξb] at h
    exact h
  -- identify the prior of the limit pair and use block-1 optimality
  have hprior : Sys.priorPenalty a ē
      = quadForm (symmPinv Sys.hSig₁.1) (ξb - blk₁ a)
        + quadForm (symmPinv Sys.hSig₂.1) (blk₂ a) := by
    unfold priorPenalty
    have hb2 : blk₂ (ē - a) = -(blk₂ a) := by
      rw [blk₂_sub, hblk2]
      funext i
      simp
    rw [hb2, quadForm_neg, blk₁_sub, ← hξb]
  have hfeasb : ∃ z, ξb - blk₁ a = Sys.Sig₁ *ᵥ z := by
    obtain ⟨z, hz⟩ := (Sys.optInitLim_feasible hC1 hC2 a).1
    exact ⟨z, by rw [← hz, ← hē, blk₁_sub, hξb]⟩
  have hmin := Sys.xiInf_min hC1 a ξb hfeasb
  unfold valueInf
  rw [hprior] at hlim
  linarith

/-- **`prop:infhor` (value identification)**: under C1 ∧ C2,
`V̄(a) = ‖ξ_∞ - a₁‖²_{Σ₁†} + ‖a₂‖²_{Σ₂†} + ‖ξ_∞‖²_{P_∞}`. -/
theorem valueLim_eq_valueInf (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Sys.valueLim a = Sys.valueInf hC1 a :=
  le_antisymm (Sys.valueLim_le_valueInf hC1 hC2 a)
    (Sys.valueInf_le_valueLim hC1 hC2 a)

end InfiniteHorizon

end FIESystem

end Estimation
