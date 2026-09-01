import LeanForControl.Estimation.Dare.Sufficiency
import Architect

/-!
# The marginal rate obstruction (`thm:main` Part 2, converse — the
finding-7 repair)

With a marginal block present, the run from the explicit C2-prior
`Σ∞ + eₘ·eₘᵀ` is **not** exponentially attracted to the strong
solution. Mechanism: along the exact from-above gap recursion
(`eq:gap-ric`), the marginal-covector energy
`φ_T = ⟨y_T, Δ_T y_T⟩` (with `y_T` the `Aₘ⁻ᵀ`-transported marginal
direction — invariant because the strong gain vanishes on the extinct
marginal) loses per step at most `c‖Δ_T‖·φ_T`. If the `ε = 1` run
were exponential, the total loss along a small-`ε` run — controlled
by comparison and by the loop-power bound near `Σ∞` — could be made
`< φ₀/2`, pinning `φ_T ≥ ε/2` forever while `φ_T → 0`. Contradiction.

The quantifier matters: a prior with *exactly known* marginal block
(zero marginal rows) converges exponentially even with `nm > 0` — the
per-prior converse of `eq:main-stab` is false, and the repair
quantifies over C2 priors, this one the witness.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

/-- Every entry is dominated by the `L∞` operator norm. -/
lemma abs_entry_le_linfty {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (i : ι) (j : κ) : |M i j| ≤ ‖M‖ := by
  have h : ‖M i j‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine le_trans ?_ (Finset.le_sup (f := fun i' => ∑ j', ‖M i' j'‖₊)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' => ‖M i j'‖₊)
      (fun _ _ => zero_le _) (Finset.mem_univ j)
  calc |M i j| = ‖M i j‖ := (Real.norm_eq_abs _).symm
  _ = ((‖M i j‖₊ : ℝ)) := rfl
  _ ≤ ((‖M‖₊ : ℝ)) := by exact_mod_cast h
  _ = ‖M‖ := rfl

/-- A Löwner-sandwiched PSD matrix has controlled norm. -/
lemma psd_norm_le_of_loewner {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X Y : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (hXY : (Y - X).PosSemidef) :
    ‖X‖ ≤ (Fintype.card ι : ℝ) ^ 3 * ‖Y‖ := by
  have hq : ∀ v, quadForm X v
      ≤ ((Fintype.card ι : ℝ) * ‖Y‖) * ‖v‖ ^ 2 := by
    intro v
    calc quadForm X v ≤ quadForm Y v :=
        quadForm_le_quadForm_of_posSemidef_sub hXY v
    _ ≤ (Fintype.card ι : ℝ) * ‖Y‖ * ‖v‖ ^ 2 :=
        quadForm_le_card_norm Y v
  calc ‖X‖ ≤ (Fintype.card ι : ℝ) ^ 2
        * ((Fintype.card ι : ℝ) * ‖Y‖) :=
      posSemidef_norm_le_of_quadForm_le hX (by positivity) hq
  _ = (Fintype.card ι : ℝ) ^ 3 * ‖Y‖ := by ring

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-- Uniform norm bound on the full innovation inverse (`S ⪰ R`). -/
lemma innov_inv_norm_bound : ∃ bR : ℝ, 0 ≤ bR ∧
    ∀ (Sg : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ), Sg.PosSemidef →
      ‖(innov S.fullC S.R Sg)⁻¹‖ ≤ bR := by
  obtain ⟨cRi, hcRi, hcRile⟩ := exists_quadForm_le S.R⁻¹
  refine ⟨(Fintype.card (Fin p) : ℝ) ^ 2 * cRi, by positivity,
    fun Sg hSg => ?_⟩
  have hSt : (innov S.fullC S.R Sg).PosDef := innov_posDef S.hR hSg
  have hdiff : (innov S.fullC S.R Sg - S.R).PosSemidef := by
    have h1 : innov S.fullC S.R Sg - S.R
        = S.fullC * Sg * S.fullCᵀ := by
      unfold innov
      abel
    rw [h1]
    have h := hSg.mul_mul_conjTranspose_same S.fullC
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hinv := posSemidef_inv_sub_inv S.hR hSt hdiff
  have hq : ∀ x, quadForm (innov S.fullC S.R Sg)⁻¹ x
      ≤ cRi * ‖x‖ ^ 2 := by
    intro x
    have h1 := quadForm_le_quadForm_of_posSemidef_sub hinv x
    linarith [hcRile x]
  exact posSemidef_norm_le_of_quadForm_le hSt.inv.posSemidef
    hcRi.le hq

set_option maxHeartbeats 1600000 in
/-- **The marginal rate obstruction** (`thm:main` Part 2 converse,
repaired): with a marginal block present, the run from the C2-prior
`Σ∞ + eₘ·eₘᵀ` is not exponentially attracted to the strong solution.
(Backward power-boundedness of `Aₘ` is the semisimple qualification.) -/
theorem marg_not_exponential (hC1 : S.C1)
    (hS : S.IsStrongSolution Sinf) (hnm : Nonempty (Fin nm))
    {cm₂ : ℝ} (hPBi : ∀ k : ℕ, ‖(S.Am⁻¹) ^ k‖ ≤ cm₂) :
    ¬ ∃ C ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ T, ‖S.dareFrom (Sinf + embM n₁ na nm * (embM n₁ na nm)ᵀ) T
        - Sinf‖ ≤ C * ρ ^ T := by
  rintro ⟨C, ρ, hρ0, hρ1, hexp⟩
  obtain ⟨i0⟩ := hnm
  set u : Fin nm → ℝ := Pi.single i0 1 with hu
  set M : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
    embM n₁ na nm * (embM n₁ na nm)ᵀ with hM
  have hMpsd : M.PosSemidef := by
    rw [hM]
    have h := (Matrix.PosSemidef.one
      (n := Fin nm) (R := ℝ)).mul_mul_conjTranspose_same
      (embM n₁ na nm)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mul_one] at h
  have hC0 : (0:ℝ) ≤ C := by
    have h := hexp 0
    rw [pow_zero, mul_one] at h
    exact le_trans (norm_nonneg _) h
  have hcm₂ : (0:ℝ) ≤ cm₂ := le_trans (norm_nonneg _) (hPBi 0)
  have hAmT : IsUnit S.Amᵀ.det := by
    rw [Matrix.det_transpose]
    exact S.isUnit_Am_det
  -- system constants
  obtain ⟨bR, hbR, hbRb⟩ := S.innov_inv_norm_bound
  set K : ℝ := (Fintype.card (ix n₁ na nm) : ℝ) with hK
  have hKnn : (0:ℝ) ≤ K := Nat.cast_nonneg _
  set Kp : ℝ := (Fintype.card (Fin p) : ℝ) with hKp
  have hKpnn : (0:ℝ) ≤ Kp := Nat.cast_nonneg _
  set cC : ℝ := ‖S.fullC‖ with hcC
  set c₅ : ℝ := Kp * bR * (K * cC ^ 2) with hc₅
  have hc₅nn : 0 ≤ c₅ := by positivity
  -- the ε-family of gaps
  set Δ : ℝ → ℕ → Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
    fun ε T => S.dareFrom (Sinf + ε • M) T - Sinf with hΔ
  have hseedpsd : ∀ {ε : ℝ}, 0 ≤ ε → (Sinf + ε • M).PosSemidef :=
    fun {ε} hε => hS.posSemidef.add (hMpsd.smul hε)
  have hseeddom : ∀ {ε : ℝ}, 0 ≤ ε →
      (Sinf + ε • M - Sinf).PosSemidef := by
    intro ε hε
    rw [add_sub_cancel_left]
    exact hMpsd.smul hε
  have hΔpsd : ∀ {ε : ℝ}, 0 ≤ ε → ∀ T, (Δ ε T).PosSemidef :=
    fun {ε} hε T => S.supremal_gap_posSemidef hS (hseedpsd hε)
      (hseeddom hε) T
  have hexp1 : ∀ T, ‖Δ 1 T‖ ≤ C * ρ ^ T := by
    intro T
    have h : Δ 1 T = S.dareFrom (Sinf + M) T - Sinf := by
      rw [hΔ]
      dsimp only
      rw [one_smul]
    rw [h, hM]
    exact hexp T
  -- comparison against the ε = 1 run
  have hcomp : ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ 1 → ∀ T,
      (Δ 1 T - Δ ε T).PosSemidef := by
    intro ε hε0 hε1 T
    have h := dareIter_mono (C := S.fullC) (A := S.fullA)
      (Qw := S.Qw) S.hR S.Qw_posSemidef (hseedpsd hε0)
      (hseedpsd zero_le_one)
      (by
        have h1 : Sinf + (1:ℝ) • M - (Sinf + ε • M)
            = (1 - ε) • M := by
          rw [sub_smul, one_smul]
          abel
        rw [h1]
        exact hMpsd.smul (by linarith)) T
    have heq : dareIter S.fullC S.R S.fullA S.Qw
          (Sinf + (1:ℝ) • M) T
        - dareIter S.fullC S.R S.fullA S.Qw (Sinf + ε • M) T
        = Δ 1 T - Δ ε T := by
      rw [hΔ]
      show S.dareFrom (Sinf + (1:ℝ) • M) T
        - S.dareFrom (Sinf + ε • M) T = _
      dsimp only
      abel
    rwa [heq] at h
  have hεnorm : ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ 1 → ∀ T,
      ‖Δ ε T‖ ≤ K ^ 3 * ‖Δ 1 T‖ :=
    fun {ε} hε0 hε1 T =>
      psd_norm_le_of_loewner (hΔpsd hε0 T) (hcomp hε0 hε1 T)
  -- the loop-power upper bound near Σ∞
  set F : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
    errMap S.fullC S.R S.fullA Sinf with hF
  have hupperF : ∀ {ε : ℝ}, 0 ≤ ε → ∀ T,
      ‖Δ ε T‖ ≤ ε * (K ^ 3 * (‖F ^ T‖
        * (K * ‖F ^ T‖) * ‖M‖)) := by
    intro ε hε T
    have hstep : ∀ T', (F * Δ ε T' * Fᵀ + (fun _ => (0 :
        Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ)) T'
        - Δ ε (T' + 1)).PosSemidef := by
      intro T'
      have h := S.supremal_gap_step hS (hseedpsd hε) (hseeddom hε) T'
      simpa using h
    have hit := loewner_iter hstep T
    have hz : (∑ j ∈ Finset.range T, F ^ (T - 1 - j)
        * (fun _ => (0 : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ)) j
        * (F ^ (T - 1 - j))ᵀ) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      simp
    rw [hz, add_zero] at hit
    have hΔ0 : Δ ε 0 = ε • M := by
      rw [hΔ]
      show Sinf + ε • M - Sinf = ε • M
      abel
    rw [hΔ0] at hit
    calc ‖Δ ε T‖ ≤ K ^ 3 * ‖F ^ T * (ε • M) * (F ^ T)ᵀ‖ :=
        psd_norm_le_of_loewner (hΔpsd hε T) hit
    _ ≤ ε * (K ^ 3 * (‖F ^ T‖ * (K * ‖F ^ T‖) * ‖M‖)) := by
        have h1 : ‖F ^ T * (ε • M) * (F ^ T)ᵀ‖
            ≤ ‖F ^ T‖ * ‖ε • M‖ * ‖(F ^ T)ᵀ‖ := norm_triple_le _ _ _
        have h2 : ‖(F ^ T)ᵀ‖ ≤ K * ‖F ^ T‖ :=
          linfty_opNorm_transpose_le' _
        have h3 : ‖ε • M‖ = ε * ‖M‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hε]
        have h4 : ‖F ^ T * (ε • M) * (F ^ T)ᵀ‖
            ≤ ‖F ^ T‖ * (ε * ‖M‖) * (K * ‖F ^ T‖) := by
          calc ‖F ^ T * (ε • M) * (F ^ T)ᵀ‖
              ≤ ‖F ^ T‖ * ‖ε • M‖ * ‖(F ^ T)ᵀ‖ := h1
          _ ≤ ‖F ^ T‖ * (ε * ‖M‖) * (K * ‖F ^ T‖) := by
              rw [h3]
              exact mul_le_mul_of_nonneg_left h2 (by positivity)
        calc K ^ 3 * ‖F ^ T * (ε • M) * (F ^ T)ᵀ‖
            ≤ K ^ 3 * (‖F ^ T‖ * (ε * ‖M‖) * (K * ‖F ^ T‖)) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = ε * (K ^ 3 * (‖F ^ T‖ * (K * ‖F ^ T‖) * ‖M‖)) := by
            ring
  -- the transported marginal direction and its energy
  set yv : ℕ → ix n₁ na nm → ℝ :=
    fun T => embM n₁ na nm *ᵥ (((S.Amᵀ)⁻¹) ^ T *ᵥ u) with hyv
  have hyvb : ∀ T, ‖yv T‖ ≤ ‖embM n₁ na nm‖
      * ((Fintype.card (Fin nm) : ℝ) * cm₂) := by
    intro T
    have h1 : ‖yv T‖ ≤ ‖embM n₁ na nm‖
        * ‖((S.Amᵀ)⁻¹) ^ T *ᵥ u‖ := by
      rw [hyv]
      exact Matrix.linfty_opNorm_mulVec _ _
    have h2 : ‖((S.Amᵀ)⁻¹) ^ T *ᵥ u‖
        ≤ ‖((S.Amᵀ)⁻¹) ^ T‖ * ‖u‖ := Matrix.linfty_opNorm_mulVec _ _
    have h3 : ‖((S.Amᵀ)⁻¹) ^ T‖
        ≤ (Fintype.card (Fin nm) : ℝ) * cm₂ := by
      have he : ((S.Amᵀ)⁻¹) ^ T = ((S.Am⁻¹) ^ T)ᵀ := by
        rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_pow]
      rw [he]
      calc ‖((S.Am⁻¹) ^ T)ᵀ‖
          ≤ (Fintype.card (Fin nm) : ℝ) * ‖(S.Am⁻¹) ^ T‖ :=
            linfty_opNorm_transpose_le' _
      _ ≤ (Fintype.card (Fin nm) : ℝ) * cm₂ :=
          mul_le_mul_of_nonneg_left (hPBi T) (Nat.cast_nonneg _)
    have h4 : ‖u‖ ≤ 1 := by
      rw [hu]
      exact norm_single_le_one i0
    calc ‖yv T‖ ≤ ‖embM n₁ na nm‖ * ‖((S.Amᵀ)⁻¹) ^ T *ᵥ u‖ := h1
    _ ≤ ‖embM n₁ na nm‖ * ((Fintype.card (Fin nm) : ℝ) * cm₂) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        calc ‖((S.Amᵀ)⁻¹) ^ T *ᵥ u‖
            ≤ ‖((S.Amᵀ)⁻¹) ^ T‖ * ‖u‖ := h2
        _ ≤ ((Fintype.card (Fin nm) : ℝ) * cm₂) * 1 :=
            mul_le_mul h3 h4 (norm_nonneg _)
              (mul_nonneg (Nat.cast_nonneg _) hcm₂)
        _ = (Fintype.card (Fin nm) : ℝ) * cm₂ := mul_one _
  -- the transported direction is F∞ᵀ-invariant
  have hFy : ∀ T, Fᵀ *ᵥ yv (T + 1) = yv T := by
    intro T
    rw [hyv]
    dsimp only
    rw [Matrix.mulVec_mulVec, hF, S.errMap_transpose_mul_embM hC1 hS,
      ← Matrix.mulVec_mulVec]
    congr 1
    rw [Matrix.mulVec_mulVec]
    congr 1
    rw [pow_succ' ((S.Amᵀ)⁻¹) T, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hAmT, Matrix.one_mul]
  -- the shifted seed is the run itself
  have hSg : ∀ {ε : ℝ} (T : ℕ),
      Sinf + Δ ε T = S.dareFrom (Sinf + ε • M) T := by
    intro ε T
    rw [hΔ]
    dsimp only
    abel
  have hSgpsd : ∀ {ε : ℝ}, 0 ≤ ε → ∀ T,
      (Sinf + Δ ε T).PosSemidef := by
    intro ε hε T
    rw [hSg]
    exact dareIter_posSemidef S.hR S.Qw_posSemidef (hseedpsd hε) T
  -- the exact marginal-energy recursion (`eq:gap-ric` transported)
  have hφrec : ∀ {ε : ℝ}, 0 ≤ ε → ∀ T,
      quadForm (Δ ε (T + 1)) (yv (T + 1))
        = quadForm (Δ ε T) (yv T)
          - quadForm (innov S.fullC S.R (Sinf + Δ ε T))⁻¹
              (S.fullC *ᵥ (Δ ε T *ᵥ yv T)) := by
    intro ε hε T
    have hgap := gapRic (C := S.fullC) (A := S.fullA) (Qw := S.Qw)
      S.hR hS.posSemidef (hS.posSemidef.add (hΔpsd hε T)) hS.fixed
    have hstepeq : Δ ε (T + 1)
        = F * (Δ ε T - Δ ε T * S.fullCᵀ
            * (innov S.fullC S.R (Sinf + Δ ε T))⁻¹
            * (S.fullC * Δ ε T)) * Fᵀ := by
      have h1 : dareStep S.fullC S.R S.fullA S.Qw
          (Sinf + Δ ε T) - Sinf = Δ ε (T + 1) := by
        rw [hSg]
        rfl
      rw [← h1, hgap, hF]
    rw [hstepeq]
    have hq1 := quadForm_mulVec (Δ ε T - Δ ε T * S.fullCᵀ
        * (innov S.fullC S.R (Sinf + Δ ε T))⁻¹
        * (S.fullC * Δ ε T)) Fᵀ (yv (T + 1))
    rw [Matrix.transpose_transpose, hFy T] at hq1
    rw [← hq1, quadForm_sub_matrix]
    congr 1
    -- the decrement is the S⁻¹-energy of `C·Δ·y`
    have hΔsym : (Δ ε T)ᵀ = Δ ε T := (hΔpsd hε T).1.transpose_eq_self
    have h2 : (Δ ε T * S.fullCᵀ
          * (innov S.fullC S.R (Sinf + Δ ε T))⁻¹
          * (S.fullC * Δ ε T)) *ᵥ yv T
        = (Δ ε T * S.fullCᵀ)
            *ᵥ ((innov S.fullC S.R (Sinf + Δ ε T))⁻¹
              *ᵥ (S.fullC *ᵥ (Δ ε T *ᵥ yv T))) := by
      simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [quadForm, h2, dotProduct_mulVec_eq, Matrix.transpose_mul,
      Matrix.transpose_transpose, hΔsym]
    rw [show (S.fullC * Δ ε T) *ᵥ yv T
        = S.fullC *ᵥ (Δ ε T *ᵥ yv T) from
      (Matrix.mulVec_mulVec _ _ _).symm]
    rfl
  have hdecnn : ∀ {ε : ℝ}, 0 ≤ ε → ∀ T,
      0 ≤ quadForm (innov S.fullC S.R (Sinf + Δ ε T))⁻¹
        (S.fullC *ᵥ (Δ ε T *ᵥ yv T)) := fun {ε} hε T =>
    ((innov_posDef S.hR (hSgpsd hε T)).inv.posSemidef).quadForm_nonneg _
  -- telescope
  have hφtel : ∀ {ε : ℝ}, 0 ≤ ε → ∀ T,
      quadForm (Δ ε T) (yv T)
        = quadForm (Δ ε 0) (yv 0)
          - ∑ j ∈ Finset.range T,
              quadForm (innov S.fullC S.R (Sinf + Δ ε j))⁻¹
                (S.fullC *ᵥ (Δ ε j *ᵥ yv j)) := by
    intro ε hε T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [hφrec hε T, ih, Finset.sum_range_succ]
      ring
  have hφle0 : ∀ {ε : ℝ}, 0 ≤ ε → ∀ T,
      quadForm (Δ ε T) (yv T) ≤ quadForm (Δ ε 0) (yv 0) := by
    intro ε hε T
    rw [hφtel hε T]
    have h := Finset.sum_nonneg
      (fun j (_ : j ∈ Finset.range T) => hdecnn hε j)
    linarith
  -- the decrement is at most `c₅·‖Δ‖·φ`
  set bY : ℝ := ‖embM n₁ na nm‖
    * ((Fintype.card (Fin nm) : ℝ) * cm₂) with hbY
  have hbYnn : 0 ≤ bY := by
    rw [hbY]
    exact mul_nonneg (norm_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) hcm₂)
  have hdecle : ∀ {ε : ℝ}, 0 ≤ ε → ∀ T,
      quadForm (innov S.fullC S.R (Sinf + Δ ε T))⁻¹
        (S.fullC *ᵥ (Δ ε T *ᵥ yv T))
      ≤ c₅ * ‖Δ ε T‖ * quadForm (Δ ε T) (yv T) := by
    intro ε hε T
    have hφnn : 0 ≤ quadForm (Δ ε T) (yv T) :=
      (hΔpsd hε T).quadForm_nonneg _
    have hB : (0:ℝ) ≤ K * cC ^ 2 * (‖Δ ε T‖ * quadForm (Δ ε T)
        (yv T)) := by
      have := norm_nonneg (Δ ε T)
      positivity
    -- entrywise Cauchy–Schwarz for the output energy
    have hw2 : ‖S.fullC *ᵥ (Δ ε T *ᵥ yv T)‖ ^ 2
        ≤ K * cC ^ 2 * (‖Δ ε T‖ * quadForm (Δ ε T) (yv T)) := by
      have hentry : ∀ i : Fin p,
          ((S.fullC *ᵥ (Δ ε T *ᵥ yv T)) i) ^ 2
            ≤ K * cC ^ 2 * (‖Δ ε T‖
                * quadForm (Δ ε T) (yv T)) := by
        intro i
        have hcs := sq_dotProduct_mulVec_le (hΔpsd hε T)
          (yv T) (fun j => S.fullC i j)
        have hci : ‖(fun j => S.fullC i j)‖ ≤ cC := by
          refine (pi_norm_le_iff_of_nonneg
            (by rw [hcC]; exact norm_nonneg _)).mpr fun j => ?_
          rw [Real.norm_eq_abs, hcC]
          exact abs_entry_le_linfty S.fullC i j
        have hqc : quadForm (Δ ε T) (fun j => S.fullC i j)
            ≤ K * ‖Δ ε T‖ * cC ^ 2 := by
          calc quadForm (Δ ε T) (fun j => S.fullC i j)
              ≤ K * ‖Δ ε T‖ * ‖(fun j => S.fullC i j)‖ ^ 2 :=
                quadForm_le_card_norm _ _
          _ ≤ K * ‖Δ ε T‖ * cC ^ 2 := by
              refine mul_le_mul_of_nonneg_left ?_ ?_
              · have h1 := norm_nonneg (fun j => S.fullC i j)
                nlinarith [hci]
              · have := norm_nonneg (Δ ε T)
                positivity
        calc ((S.fullC *ᵥ (Δ ε T *ᵥ yv T)) i) ^ 2
            = ((fun j => S.fullC i j) ⬝ᵥ (Δ ε T *ᵥ yv T)) ^ 2 := rfl
        _ ≤ quadForm (Δ ε T) (fun j => S.fullC i j)
              * quadForm (Δ ε T) (yv T) := hcs
        _ ≤ (K * ‖Δ ε T‖ * cC ^ 2) * quadForm (Δ ε T) (yv T) :=
            mul_le_mul_of_nonneg_right hqc hφnn
        _ = K * cC ^ 2 * (‖Δ ε T‖ * quadForm (Δ ε T) (yv T)) := by
            ring
      have hwle : ‖S.fullC *ᵥ (Δ ε T *ᵥ yv T)‖
          ≤ Real.sqrt (K * cC ^ 2 * (‖Δ ε T‖
              * quadForm (Δ ε T) (yv T))) := by
        refine (pi_norm_le_iff_of_nonneg
          (Real.sqrt_nonneg _)).mpr fun i => ?_
        rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
        exact Real.sqrt_le_sqrt (hentry i)
      calc ‖S.fullC *ᵥ (Δ ε T *ᵥ yv T)‖ ^ 2
          ≤ (Real.sqrt (K * cC ^ 2 * (‖Δ ε T‖
              * quadForm (Δ ε T) (yv T)))) ^ 2 := by
            nlinarith [norm_nonneg (S.fullC *ᵥ (Δ ε T *ᵥ yv T)),
              Real.sqrt_nonneg (K * cC ^ 2 * (‖Δ ε T‖
                * quadForm (Δ ε T) (yv T)))]
      _ = K * cC ^ 2 * (‖Δ ε T‖ * quadForm (Δ ε T) (yv T)) :=
          Real.sq_sqrt hB
    calc quadForm (innov S.fullC S.R (Sinf + Δ ε T))⁻¹
          (S.fullC *ᵥ (Δ ε T *ᵥ yv T))
        ≤ Kp * ‖(innov S.fullC S.R (Sinf + Δ ε T))⁻¹‖
          * ‖S.fullC *ᵥ (Δ ε T *ᵥ yv T)‖ ^ 2 :=
          quadForm_le_card_norm _ _
    _ ≤ Kp * bR * ‖S.fullC *ᵥ (Δ ε T *ᵥ yv T)‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left
          (hbRb _ (hSgpsd hε T)) hKpnn
    _ ≤ Kp * bR * (K * cC ^ 2 * (‖Δ ε T‖
          * quadForm (Δ ε T) (yv T))) := by
        refine mul_le_mul_of_nonneg_left hw2 (by positivity)
    _ = c₅ * ‖Δ ε T‖ * quadForm (Δ ε T) (yv T) := by
        rw [hc₅]
        ring
  -- the initial energy is exactly ε
  have hΔε0 : ∀ ε : ℝ, Δ ε 0 = ε • M := by
    intro ε
    rw [hΔ]
    show Sinf + ε • M - Sinf = ε • M
    abel
  have hφ0 : ∀ ε : ℝ, quadForm (Δ ε 0) (yv 0) = ε := by
    intro ε
    rw [hΔε0, hyv]
    dsimp only
    rw [pow_zero, Matrix.one_mulVec]
    unfold quadForm
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hM]
    rw [show (embM n₁ na nm * (embM n₁ na nm)ᵀ)
          *ᵥ (embM n₁ na nm *ᵥ u)
        = embM n₁ na nm *ᵥ ((embM n₁ na nm)ᵀ
            *ᵥ (embM n₁ na nm *ᵥ u)) from by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]]
    rw [dotProduct_mulVec_eq, Matrix.mulVec_mulVec, embMt_mul_embM,
      Matrix.one_mulVec]
    rw [hu]
    simp [dotProduct, Pi.single_apply]
  -- choose the split point and the seed size
  set G : ℕ → ℝ := fun T => K ^ 3 * (‖F ^ T‖
    * (K * ‖F ^ T‖) * ‖M‖) with hG
  have hGnn : ∀ T, 0 ≤ G T := by
    intro T
    rw [hG]
    positivity
  have htailJ : Tendsto (fun J : ℕ =>
      c₅ * (K ^ 3 * C) * (ρ ^ J * (1 - ρ)⁻¹)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
    have h2 := (h.mul_const (1 - ρ)⁻¹).const_mul (c₅ * (K ^ 3 * C))
    simpa using h2
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.mp
    (htailJ.eventually_lt_const (by norm_num : (0:ℝ) < 1/4))
  have hJ4 : c₅ * (K ^ 3 * C) * (ρ ^ J * (1 - ρ)⁻¹) < 1/4 :=
    hJ J le_rfl
  set GJ : ℝ := ∑ j ∈ Finset.range J, G j with hGJ
  have hGJnn : 0 ≤ GJ := Finset.sum_nonneg fun j _ => hGnn j
  obtain ⟨ε, hε0, hε1, hεGJ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1
      ∧ c₅ * GJ * ε ≤ 1/4 := by
    have h1 : (0:ℝ) < 4 * (c₅ * GJ + 1) := by
      nlinarith [mul_nonneg hc₅nn hGJnn]
    refine ⟨min 1 (1 / (4 * (c₅ * GJ + 1))), lt_min one_pos
      (one_div_pos.mpr h1), min_le_left _ _, ?_⟩
    have h2 : min 1 (1 / (4 * (c₅ * GJ + 1)))
        ≤ 1 / (4 * (c₅ * GJ + 1)) := min_le_right _ _
    calc c₅ * GJ * min 1 (1 / (4 * (c₅ * GJ + 1)))
        ≤ c₅ * GJ * (1 / (4 * (c₅ * GJ + 1))) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hc₅nn hGJnn)
    _ ≤ 1/4 := by
        rw [mul_one_div, div_le_iff₀ h1]
        nlinarith [mul_nonneg hc₅nn hGJnn]
  -- the total loss is at most half the seed
  have hloss : ∀ T, ∑ j ∈ Finset.range T, c₅ * ‖Δ ε j‖ ≤ 1/2 := by
    have hhead : ∀ T', T' ≤ J →
        ∑ j ∈ Finset.range T', c₅ * ‖Δ ε j‖ ≤ 1/4 := by
      intro T' hT'
      calc ∑ j ∈ Finset.range T', c₅ * ‖Δ ε j‖
          ≤ ∑ j ∈ Finset.range T', c₅ * (ε * G j) := by
            refine Finset.sum_le_sum fun j _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ hc₅nn
            have h := hupperF hε0.le j
            rw [hG]
            exact h
      _ ≤ ∑ j ∈ Finset.range J, c₅ * (ε * G j) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.mpr
              (lt_of_lt_of_le (Finset.mem_range.mp hx) hT'))
            fun j _ _ => ?_
          have h := hGnn j
          have h2 := hε0.le
          positivity
      _ = c₅ * ε * GJ := by
          rw [hGJ, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ 1/4 := by
          calc c₅ * ε * GJ = c₅ * GJ * ε := by ring
          _ ≤ 1/4 := hεGJ
    intro T
    rcases Nat.le_total T J with hTJ | hTJ
    · exact le_trans (hhead T hTJ) (by norm_num)
    · rw [← Finset.sum_range_add_sum_Ico
        (fun j => c₅ * ‖Δ ε j‖) hTJ]
      have h1 := hhead J le_rfl
      have h2 : ∑ j ∈ Finset.Ico J T, c₅ * ‖Δ ε j‖ ≤ 1/4 := by
        have hgeo : ∑ k ∈ Finset.range (T - J), ρ ^ k
            ≤ (1 - ρ)⁻¹ := by
          have h5 : (0:ℝ) < 1 - ρ := by linarith
          rw [inv_eq_one_div, le_div_iff₀ h5]
          nlinarith [pow_nonneg hρ0.le (T - J), geom_sum_mul ρ (T - J)]
        calc ∑ j ∈ Finset.Ico J T, c₅ * ‖Δ ε j‖
            ≤ ∑ j ∈ Finset.Ico J T, c₅ * (K ^ 3 * (C * ρ ^ j)) := by
              refine Finset.sum_le_sum fun j _ => ?_
              refine mul_le_mul_of_nonneg_left ?_ hc₅nn
              calc ‖Δ ε j‖ ≤ K ^ 3 * ‖Δ 1 j‖ := hεnorm hε0.le hε1 j
              _ ≤ K ^ 3 * (C * ρ ^ j) := by
                  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                  exact hexp1 j
        _ = c₅ * (K ^ 3 * C) * ∑ j ∈ Finset.Ico J T, ρ ^ j := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
        _ ≤ c₅ * (K ^ 3 * C) * (ρ ^ J * (1 - ρ)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_
              (mul_nonneg hc₅nn (by positivity))
            calc ∑ j ∈ Finset.Ico J T, ρ ^ j
                = ∑ k ∈ Finset.range (T - J), ρ ^ (J + k) :=
                  Finset.sum_Ico_eq_sum_range _ _ _
            _ = ρ ^ J * ∑ k ∈ Finset.range (T - J), ρ ^ k := by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun k _ => by
                  rw [pow_add]
            _ ≤ ρ ^ J * (1 - ρ)⁻¹ := by
                refine mul_le_mul_of_nonneg_left hgeo (by positivity)
        _ ≤ 1/4 := hJ4.le
      linarith
  -- the energy is pinned above ε/2 …
  have hpin : ∀ T, ε / 2 ≤ quadForm (Δ ε T) (yv T) := by
    intro T
    have h1 := hφtel hε0.le T
    have h2 : ∑ j ∈ Finset.range T,
        quadForm (innov S.fullC S.R (Sinf + Δ ε j))⁻¹
          (S.fullC *ᵥ (Δ ε j *ᵥ yv j))
        ≤ ∑ j ∈ Finset.range T, c₅ * ‖Δ ε j‖ * ε := by
      refine Finset.sum_le_sum fun j _ => ?_
      calc quadForm (innov S.fullC S.R (Sinf + Δ ε j))⁻¹
            (S.fullC *ᵥ (Δ ε j *ᵥ yv j))
          ≤ c₅ * ‖Δ ε j‖ * quadForm (Δ ε j) (yv j) :=
            hdecle hε0.le j
      _ ≤ c₅ * ‖Δ ε j‖ * ε := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg hc₅nn (norm_nonneg _))
          calc quadForm (Δ ε j) (yv j)
              ≤ quadForm (Δ ε 0) (yv 0) := hφle0 hε0.le j
          _ = ε := hφ0 ε
    have h3 : ∑ j ∈ Finset.range T, c₅ * ‖Δ ε j‖ * ε
        = (∑ j ∈ Finset.range T, c₅ * ‖Δ ε j‖) * ε :=
      (Finset.sum_mul _ _ _).symm
    have h4 : (∑ j ∈ Finset.range T, c₅ * ‖Δ ε j‖) * ε
        ≤ (1/2) * ε :=
      mul_le_mul_of_nonneg_right (hloss T) hε0.le
    rw [h1, hφ0]
    have h5 : ∑ j ∈ Finset.range T,
        quadForm (innov S.fullC S.R (Sinf + Δ ε j))⁻¹
          (S.fullC *ᵥ (Δ ε j *ᵥ yv j)) ≤ (1/2) * ε := by
      calc _ ≤ ∑ j ∈ Finset.range T, c₅ * ‖Δ ε j‖ * ε := h2
      _ = (∑ j ∈ Finset.range T, c₅ * ‖Δ ε j‖) * ε := h3
      _ ≤ (1/2) * ε := h4
    linarith
  -- … but must vanish geometrically. Contradiction.
  have hup : ∀ T, quadForm (Δ ε T) (yv T)
      ≤ (K * (K ^ 3 * C) * bY ^ 2) * ρ ^ T := by
    intro T
    have hΔle : ‖Δ ε T‖ ≤ K ^ 3 * (C * ρ ^ T) := by
      calc ‖Δ ε T‖ ≤ K ^ 3 * ‖Δ 1 T‖ := hεnorm hε0.le hε1 T
      _ ≤ K ^ 3 * (C * ρ ^ T) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hexp1 T
    have hy2 : ‖yv T‖ ^ 2 ≤ bY ^ 2 := by
      have h := hyvb T
      nlinarith [norm_nonneg (yv T), hbYnn]
    calc quadForm (Δ ε T) (yv T)
        ≤ K * ‖Δ ε T‖ * ‖yv T‖ ^ 2 := quadForm_le_card_norm _ _
    _ ≤ K * (K ^ 3 * (C * ρ ^ T)) * bY ^ 2 := by
        refine mul_le_mul ?_ hy2 (by positivity) ?_
        · exact mul_le_mul_of_nonneg_left hΔle hKnn
        · refine mul_nonneg hKnn (mul_nonneg (by positivity)
            (mul_nonneg hC0 (by positivity)))
    _ = (K * (K ^ 3 * C) * bY ^ 2) * ρ ^ T := by ring
  have htend : Tendsto (fun T : ℕ =>
      (K * (K ^ 3 * C) * bY ^ 2) * ρ ^ T) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
    simpa using h.const_mul (K * (K ^ 3 * C) * bY ^ 2)
  obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp
    (htend.eventually_lt_const (half_pos hε0))
  have h1 := hpin T0
  have h2 := lt_of_le_of_lt (hup T0) (hT0 T0 le_rfl)
  linarith

/-- **The counterexample mechanism** (why the per-prior converse of
`eq:main-stab` fails): a prior with exactly known marginal block keeps
its marginal rows zero forever — the run coincides with a marginal-free
subsystem run and can converge exponentially despite `nm > 0`. -/
lemma marg_rows_stay_zero
    {L₀ : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (h0 : (embM n₁ na nm)ᵀ * L₀ = 0) :
    ∀ T, (embM n₁ na nm)ᵀ * S.dareFrom L₀ T = 0 := by
  intro T
  have hbase : RowSlaved (0 : Matrix (Fin nm) (Fin na) ℝ) L₀ := by
    unfold RowSlaved
    rw [h0, Matrix.zero_mul]
  have h := S.rowSlaved_dareIter hbase T
  unfold RowSlaved at h
  rw [show S.Am ^ T * (0 : Matrix (Fin nm) (Fin na) ℝ)
      * (S.Aa⁻¹) ^ T = 0 by
    rw [Matrix.mul_zero, Matrix.zero_mul], Matrix.zero_mul] at h
  exact h

end DareSystem

end Dare
end Estimation
