import LeanForControl.Estimation.Coercive
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
theorem tendsto_value (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Tendsto (fun T => Sys.value a T) atTop (nhds (Sys.valueLim a)) := by
  obtain ⟨c, hc, hb⟩ := Sys.exists_value_bound hC1 hC2
  refine tendsto_atTop_ciSup (fun T τ h => Sys.value_mono a h) ⟨c * ‖a‖ ^ 2, ?_⟩
  rintro x ⟨T, rfl⟩
  exact hb a T

theorem value_le_valueLim (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ) :
    Sys.value a T ≤ Sys.valueLim a := by
  obtain ⟨c, hc, hb⟩ := Sys.exists_value_bound hC1 hC2
  refine le_ciSup ⟨c * ‖a‖ ^ 2, ?_⟩ T
  rintro x ⟨τ, rfl⟩
  exact hb a τ

theorem valueLim_le (a : Fin n₁ ⊕ Fin n₂ → ℝ) {b : ℝ}
    (h : ∀ T, Sys.value a T ≤ b) : Sys.valueLim a ≤ b :=
  ciSup_le h

/-- **The truncation gap bound**: for `T ≤ τ` the `τ`-optimal decisions,
viewed at horizon `T`, deviate from the `T`-optimum by at most
`V̄(a) - V_T⁰(a)` in the gap metric. -/
theorem truncation_gap (hC1 : Sys.C1) (hC2 : Sys.C2)
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
  have h4 := Sys.value_le_valueLim hC1 hC2 a τ
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
theorem optInit_cauchySeq (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    CauchySeq (fun T => Sys.optInit a T) := by
  obtain ⟨C, hC, hb⟩ := Sys.exists_optInit_dev_bound
  rw [Metric.cauchySeq_iff']
  intro ε hε
  -- pick `N` with `C·(V̄ - V_N) < ε²`
  have htend := Sys.tendsto_value hC1 hC2 a
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
  have h4 := hb a hτ (Sys.value_le_valueLim hC1 hC2 a τ)
  rw [dist_eq_norm]
  have h5 : ‖Sys.optInit a τ - Sys.optInit a N‖ ^ 2 < ε ^ 2 :=
    lt_of_le_of_lt h4 hN
  nlinarith [norm_nonneg (Sys.optInit a τ - Sys.optInit a N), hε]

/-- The limiting optimal initial error `ē(0)`. -/
noncomputable def optInitLim (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Fin n₁ ⊕ Fin n₂ → ℝ :=
  limUnder atTop (fun T => Sys.optInit a T)

theorem tendsto_optInit (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) :
    Tendsto (fun T => Sys.optInit a T) atTop (nhds (Sys.optInitLim a)) := by
  have h := (Sys.optInit_cauchySeq hC1 hC2 a).tendsto_limUnder
  exact h

/-- The optimal controls converge stagewise. -/
theorem optCtrl_cauchySeq (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (k : ℕ) :
    CauchySeq (fun T => Sys.lq.optCtrl (Sys.optInit a T) T k) := by
  obtain ⟨C, hC, hb⟩ := Sys.exists_optCtrl_dev_bound
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have htend := Sys.tendsto_value hC1 hC2 a
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
  have h4 := hb a k hNk hτ (Sys.value_le_valueLim hC1 hC2 a τ)
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

theorem tendsto_optCtrl (hC1 : Sys.C1) (hC2 : Sys.C2)
    (a : Fin n₁ ⊕ Fin n₂ → ℝ) (k : ℕ) :
    Tendsto (fun T => Sys.lq.optCtrl (Sys.optInit a T) T k) atTop
      (nhds (Sys.optCtrlLim a k)) :=
  (Sys.optCtrl_cauchySeq hC1 hC2 a k).tendsto_limUnder

end FIESystem

end Estimation
