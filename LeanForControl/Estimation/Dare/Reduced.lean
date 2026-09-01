import LeanForControl.Estimation.Dare.RateFloor
import Architect

/-!
# The reduced stabilizing solution (D2: the reduced `fact:dare-strong`)

The `e₁`-block foothold of the odyssey chart, now constructed rather
than imported. For a general detectable–stabilizable pair:

* `monotone_psd_tendsto` — a monotone, bounded sequence of PSD
  matrices converges (quadratic forms are monotone bounded, hence
  convergent; polarization recovers the entries; entrywise limits
  give the `L∞` norm).
* `exists_stabilizing_solution` — the zero-seed DARE run is monotone
  (comparison from `0 ⪯ Q_w`) and bounded (`eq:bounded`), so it has a
  PSD limit; the limit is a fixed point (`dareStep_diff` makes the
  step Lipschitz along the run — no inverse-continuity needed); and
  **every** PSD fixed point has a Schur loop (`fixed_point_schur`):
  the one-step PBH–Stein kill of `Dare/Spectrum.lean`, marginal-free,
  needs only stabilizability — at `|μ| ≥ 1` the transported
  predictor-Joseph identity forces the noise inputs of a left
  eigenvector to vanish, so it is a left eigenvector of `A` unexcited
  by `G`, dead by PBH.
* `stabilizing_fixed_unique` — two Schur fixed points agree:
  `Δ = F^k Δ (F'ᵀ)^k` (iterated `dareStep_diff`) is squeezed by the
  two geometric decays.

Instantiated to the frame: `redP_exists_stabilizing` (reduced
detectability comes from C1 through `emb1`).
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

variable {ι κ σ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] [Fintype σ] [DecidableEq σ]

variable {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ}

/-! ### Entrywise limits and monotone PSD convergence -/

/-- Entrywise convergence gives `L∞`-norm convergence. -/
lemma tendsto_norm_sub_of_entry {κ' : Type*} [Fintype κ']
    {M : ℕ → Matrix ι κ' ℝ} {Minf : Matrix ι κ' ℝ}
    (h : ∀ i j, Tendsto (fun T => M T i j) atTop (nhds (Minf i j))) :
    Tendsto (fun T => ‖M T - Minf‖) atTop (nhds 0) := by
  have hsum : Tendsto (fun T => ∑ i, ∑ j, |(M T - Minf) i j|)
      atTop (nhds 0) := by
    have h0 : (0 : ℝ) = ∑ _i : ι, ∑ _j : κ', (0 : ℝ) := by simp
    rw [h0]
    refine tendsto_finset_sum _ fun i _ => ?_
    refine tendsto_finset_sum _ fun j _ => ?_
    have h1 : Tendsto (fun T => (M T - Minf) i j) atTop (nhds 0) := by
      have h2 := (h i j).sub (tendsto_const_nhds (x := Minf i j))
      simpa [Matrix.sub_apply] using h2
    simpa using h1.abs
  exact squeeze_zero (fun T => norm_nonneg _)
    (fun T => linfty_opNorm_le_sum_abs _) hsum

/-- **Monotone bounded PSD convergence**: a Löwner-nondecreasing,
quadratically bounded sequence of PSD matrices converges in norm to a
PSD limit dominating every iterate. -/
theorem monotone_psd_tendsto {M : ℕ → Matrix ι ι ℝ}
    (hpsd : ∀ T, (M T).PosSemidef)
    (hmono : ∀ T, (M (T + 1) - M T).PosSemidef)
    {b : ℝ} (hbdd : ∀ (T : ℕ) (x : ι → ℝ),
      quadForm (M T) x ≤ b * ‖x‖ ^ 2) :
    ∃ Minf : Matrix ι ι ℝ, Minf.PosSemidef
      ∧ (∀ T, (Minf - M T).PosSemidef)
      ∧ Tendsto (fun T => ‖M T - Minf‖) atTop (nhds 0) := by
  classical
  have hqmono : ∀ x : ι → ℝ, Monotone fun T => quadForm (M T) x := by
    intro x
    exact monotone_nat_of_le_succ fun T =>
      quadForm_le_quadForm_of_posSemidef_sub (hmono T) x
  have hqbdd : ∀ x : ι → ℝ,
      BddAbove (Set.range fun T => quadForm (M T) x) := by
    intro x
    refine ⟨b * ‖x‖ ^ 2, ?_⟩
    rintro y ⟨T, rfl⟩
    exact hbdd T x
  have hqlim : ∀ x : ι → ℝ, Tendsto (fun T => quadForm (M T) x)
      atTop (nhds (⨆ T, quadForm (M T) x)) :=
    fun x => tendsto_atTop_ciSup (hqmono x) (hqbdd x)
  -- polarization: entries from quadratic forms
  have hpolar : ∀ (T : ℕ) (i j : ι), M T i j
      = (quadForm (M T) (Pi.single i 1 + Pi.single j 1)
        - quadForm (M T) (Pi.single i 1 - Pi.single j 1)) / 4 := by
    intro T i j
    have hsym := (hpsd T).1
    have hsub : (Pi.single i 1 : ι → ℝ) - Pi.single j 1
        = (Pi.single i 1 : ι → ℝ)
          + (-1 : ℝ) • (Pi.single j 1 : ι → ℝ) := by module
    have hentry : (Pi.single i 1 : ι → ℝ)
        ⬝ᵥ (M T *ᵥ Pi.single j 1) = M T i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [hsub, quadForm_add_of_isHermitian hsym,
      quadForm_add_of_isHermitian hsym, quadForm_smul,
      Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hentry]
    ring
  set Minf : Matrix ι ι ℝ := Matrix.of fun i j =>
    ((⨆ T, quadForm (M T) (Pi.single i 1 + Pi.single j 1))
      - (⨆ T, quadForm (M T) (Pi.single i 1 - Pi.single j 1))) / 4
    with hMdef
  have hentry_lim : ∀ i j,
      Tendsto (fun T => M T i j) atTop (nhds (Minf i j)) := by
    intro i j
    have h1 := ((hqlim (Pi.single i 1 + Pi.single j 1)).sub
      (hqlim (Pi.single i 1 - Pi.single j 1))).div_const 4
    have h2 : (fun T =>
        (quadForm (M T) (Pi.single i 1 + Pi.single j 1)
          - quadForm (M T) (Pi.single i 1 - Pi.single j 1)) / 4)
        = fun T => M T i j :=
      funext fun T => (hpolar T i j).symm
    rw [h2] at h1
    exact h1
  -- the quadratic form of the limit is the limit of the forms
  have hquad_lim : ∀ x : ι → ℝ,
      Tendsto (fun T => quadForm (M T) x) atTop
        (nhds (quadForm Minf x)) := by
    intro x
    have hrepr : ∀ N : Matrix ι ι ℝ,
        quadForm N x = ∑ i, ∑ j, x i * (N i j * x j) := by
      intro N
      simp [quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
    have h1 : Tendsto (fun T => ∑ i, ∑ j, x i * (M T i j * x j))
        atTop (nhds (∑ i, ∑ j, x i * (Minf i j * x j))) := by
      refine tendsto_finset_sum _ fun i _ => ?_
      refine tendsto_finset_sum _ fun j _ => ?_
      exact (((hentry_lim i j).mul_const (x j)).const_mul (x i))
    have h2 : (fun T => quadForm (M T) x)
        = fun T => ∑ i, ∑ j, x i * (M T i j * x j) :=
      funext fun T => hrepr (M T)
    rw [h2, hrepr Minf]
    exact h1
  have hqeq : ∀ x : ι → ℝ,
      quadForm Minf x = ⨆ T, quadForm (M T) x := fun x =>
    tendsto_nhds_unique (hquad_lim x) (hqlim x)
  -- symmetry of the limit
  have hherm : Minf.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    have h1 : (Pi.single j 1 : ι → ℝ) + Pi.single i 1
        = Pi.single i 1 + Pi.single j 1 := by
      rw [add_comm]
    have h2 : ∀ T, quadForm (M T) (Pi.single j 1 - Pi.single i 1)
        = quadForm (M T) (Pi.single i 1 - Pi.single j 1) := by
      intro T
      have h3 : (Pi.single j 1 : ι → ℝ) - Pi.single i 1
          = -(Pi.single i 1 - Pi.single j 1) := by module
      rw [h3, quadForm_neg]
    simp only [Matrix.transpose_apply, hMdef, Matrix.of_apply, h1]
    congr 1
    congr 1
    exact iSup_congr h2
  refine ⟨Minf, ?_, ?_, tendsto_norm_sub_of_entry hentry_lim⟩
  · refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
      fun x => ?_
    rw [star_trivial]
    have h1 : (0 : ℝ) ≤ quadForm Minf x := by
      rw [hqeq]
      exact le_ciSup_of_le (hqbdd x) 0 ((hpsd 0).quadForm_nonneg x)
    exact h1
  · intro T
    refine posSemidef_sub_of_quadForm_le (hpsd T).1 hherm fun x => ?_
    rw [hqeq]
    exact le_ciSup (hqbdd x) T

/-! ### Zero-seed monotonicity and small identities -/

lemma updM_zero : updM C R (0 : Matrix ι ι ℝ) = 0 := by
  unfold updM
  simp

lemma dareStep_zero {A Qw : Matrix ι ι ℝ} :
    dareStep C R A Qw (0 : Matrix ι ι ℝ) = Qw := by
  unfold dareStep
  rw [updM_zero]
  simp

lemma dareIter_shift {A Qw L : Matrix ι ι ℝ} (T : ℕ) :
    dareIter C R A Qw L (T + 1)
      = dareIter C R A Qw (dareStep C R A Qw L) T := by
  induction T with
  | zero => rfl
  | succ T ih => rw [dareIter_succ, ih, ← dareIter_succ]

/-- The zero-seed run is Löwner-nondecreasing. -/
lemma dareIter_zero_mono {A Qw : Matrix ι ι ℝ} (hR : R.PosDef)
    (hQw : Qw.PosSemidef) (T : ℕ) :
    (dareIter C R A Qw 0 (T + 1) - dareIter C R A Qw 0 T).PosSemidef := by
  rw [dareIter_shift, dareStep_zero]
  exact dareIter_mono hR hQw Matrix.PosSemidef.zero hQw
    (by simpa using hQw) T

/-! ### The step is Lipschitz along a convergent run -/

/-- Uniform norm bound on innovation inverses over PSD arguments
(`S(Σ) ⪰ R` and Löwner inversion). -/
lemma innov_inv_norm_bound_general (hR : R.PosDef) :
    ∃ bR : ℝ, 0 ≤ bR ∧
      ∀ Sg : Matrix ι ι ℝ, Sg.PosSemidef →
        ‖(innov C R Sg)⁻¹‖ ≤ bR := by
  obtain ⟨cRi, hcRi, hcRile⟩ := exists_quadForm_le R⁻¹
  refine ⟨(Fintype.card κ : ℝ) ^ 2 * cRi, by positivity,
    fun Sg hSg => ?_⟩
  have hSt : (innov C R Sg).PosDef := innov_posDef hR hSg
  have hdiff : (innov C R Sg - R).PosSemidef := by
    have h1 : innov C R Sg - R = C * Sg * Cᵀ := by
      unfold innov
      abel
    rw [h1]
    have h := hSg.mul_mul_conjTranspose_same C
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hinv := posSemidef_inv_sub_inv hR hSt hdiff
  have hq : ∀ x, quadForm (innov C R Sg)⁻¹ x ≤ cRi * ‖x‖ ^ 2 := by
    intro x
    have h1 := quadForm_le_quadForm_of_posSemidef_sub hinv x
    linarith [hcRile x]
  exact posSemidef_norm_le_of_quadForm_le hSt.inv.posSemidef
    hcRi.le hq

/-- Along a norm-convergent PSD sequence, the DARE step converges to
the step at the limit (`dareStep_diff` + uniform loop bounds). -/
lemma dareStep_tendsto_of_tendsto {A Qw : Matrix ι ι ℝ}
    (hR : R.PosDef) {M : ℕ → Matrix ι ι ℝ} {Minf : Matrix ι ι ℝ}
    (hpsd : ∀ T, (M T).PosSemidef) (hMinf : Minf.PosSemidef)
    (h : Tendsto (fun T => ‖M T - Minf‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖dareStep C R A Qw (M T)
      - dareStep C R A Qw Minf‖) atTop (nhds 0) := by
  obtain ⟨bR, hbR, hbRb⟩ := innov_inv_norm_bound_general (C := C) hR
  obtain ⟨B, hB, hBb⟩ := exists_bound_of_tendsto_zero h
  -- uniform bound on the argument norms
  have hMbd : ∀ T, ‖M T‖ ≤ B + ‖Minf‖ := by
    intro T
    calc ‖M T‖ = ‖M T - Minf + Minf‖ := by rw [sub_add_cancel]
    _ ≤ ‖M T - Minf‖ + ‖Minf‖ := norm_add_le _ _
    _ ≤ B + ‖Minf‖ := by linarith [hBb T]
  -- uniform bound on the error-map norms
  have hFbd : ∀ (Sg : Matrix ι ι ℝ), Sg.PosSemidef → ‖Sg‖ ≤ B + ‖Minf‖ →
      ‖errMap C R A Sg‖
        ≤ ‖A‖ + ‖A‖ * ((B + ‖Minf‖) * ‖Cᵀ‖ * bR * ‖C‖) := by
    intro Sg hSg hSgB
    have hSg0 : (0:ℝ) ≤ ‖Sg‖ := norm_nonneg _
    have hBM : (0:ℝ) ≤ B + ‖Minf‖ := le_trans hSg0 hSgB
    have hCt : (0:ℝ) ≤ ‖Cᵀ‖ := norm_nonneg _
    have hK : ‖kGain C R Sg‖ ≤ (B + ‖Minf‖) * ‖Cᵀ‖ * bR := by
      unfold kGain
      calc ‖Sg * Cᵀ * (innov C R Sg)⁻¹‖
          ≤ ‖Sg‖ * ‖Cᵀ‖ * ‖(innov C R Sg)⁻¹‖ :=
            norm_triple_le _ _ _
      _ ≤ (B + ‖Minf‖) * ‖Cᵀ‖ * bR := by
          refine mul_le_mul
            (mul_le_mul_of_nonneg_right hSgB hCt)
            (hbRb Sg hSg) (norm_nonneg _)
            (mul_nonneg hBM hCt)
    have herr : errMap C R A Sg = A - A * (kGain C R Sg * C) := by
      unfold errMap
      rw [Matrix.mul_sub, Matrix.mul_one]
    rw [herr]
    calc ‖A - A * (kGain C R Sg * C)‖
        ≤ ‖A‖ + ‖A * (kGain C R Sg * C)‖ := norm_sub_le _ _
    _ ≤ ‖A‖ + ‖A‖ * ((B + ‖Minf‖) * ‖Cᵀ‖ * bR * ‖C‖) := by
        have h2 : ‖A * (kGain C R Sg * C)‖
            ≤ ‖A‖ * (‖kGain C R Sg‖ * ‖C‖) := by
          calc ‖A * (kGain C R Sg * C)‖
              ≤ ‖A‖ * ‖kGain C R Sg * C‖ :=
                Matrix.linfty_opNorm_mul _ _
          _ ≤ ‖A‖ * (‖kGain C R Sg‖ * ‖C‖) :=
              mul_le_mul_of_nonneg_left
                (Matrix.linfty_opNorm_mul _ _) (norm_nonneg A)
        have h3 : ‖kGain C R Sg‖ * ‖C‖
            ≤ (B + ‖Minf‖) * ‖Cᵀ‖ * bR * ‖C‖ :=
          mul_le_mul_of_nonneg_right hK (norm_nonneg C)
        have h4 := mul_le_mul_of_nonneg_left h3 (norm_nonneg A)
        linarith
  set cF : ℝ := ‖A‖ + ‖A‖ * ((B + ‖Minf‖) * ‖Cᵀ‖ * bR * ‖C‖) with hcF
  have hcF0 : 0 ≤ cF := by
    have h1 : (0:ℝ) ≤ ‖Minf‖ := norm_nonneg _
    have h2 : (0:ℝ) ≤ ‖Cᵀ‖ := norm_nonneg _
    have h3 : (0:ℝ) ≤ ‖C‖ := norm_nonneg _
    have h4 : (0:ℝ) ≤ ‖A‖ := norm_nonneg _
    positivity
  have hbound : ∀ T, ‖dareStep C R A Qw (M T)
      - dareStep C R A Qw Minf‖
      ≤ cF * ((Fintype.card ι : ℝ) * cF) * ‖M T - Minf‖ := by
    intro T
    rw [dareStep_diff hR (hpsd T) hMinf]
    calc ‖errMap C R A (M T) * (M T - Minf) * (errMap C R A Minf)ᵀ‖
        ≤ ‖errMap C R A (M T)‖ * ‖M T - Minf‖
          * ‖(errMap C R A Minf)ᵀ‖ := norm_triple_le _ _ _
    _ ≤ cF * ‖M T - Minf‖ * ((Fintype.card ι : ℝ) * cF) := by
        have h1 := hFbd (M T) (hpsd T) (hMbd T)
        have h3 : ‖errMap C R A Minf‖ ≤ cF := by
          refine hFbd Minf hMinf ?_
          have h4 : (0:ℝ) ≤ B := hB
          linarith
        have h2 : ‖(errMap C R A Minf)ᵀ‖
            ≤ (Fintype.card ι : ℝ) * cF :=
          le_trans (linfty_opNorm_transpose_le' _)
            (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _))
        have h6 : (0:ℝ) ≤ ‖M T - Minf‖ := norm_nonneg _
        refine mul_le_mul ?_ h2 (norm_nonneg _)
          (mul_nonneg hcF0 h6)
        exact mul_le_mul_of_nonneg_right h1 h6
    _ = cF * ((Fintype.card ι : ℝ) * cF) * ‖M T - Minf‖ := by
        ring
  have hlim := h.const_mul (cF * ((Fintype.card ι : ℝ) * cF))
  rw [mul_zero] at hlim
  exact squeeze_zero (fun T => norm_nonneg _) hbound hlim

/-! ### Every PSD fixed point has a Schur loop (PBH–Stein, marginal-free) -/

/-- The fixed point in predictor-Joseph form (general). -/
lemma fixed_predictor_stein {A Qw : Matrix ι ι ℝ} (hR : R.PosDef)
    {P : Matrix ι ι ℝ} (hP : P.PosSemidef)
    (hfix : dareStep C R A Qw P = P) :
    P = errMap C R A P * P * (errMap C R A P)ᵀ
      + (A * kGain C R P) * R * (A * kGain C R P)ᵀ + Qw := by
  conv_lhs => rw [← hfix]
  show A * updM C R P * Aᵀ + Qw = _
  rw [updM_eq_joseph hR hP]
  unfold joseph errMap
  simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]

set_option maxHeartbeats 1600000 in
/-- **Every PSD fixed point of the DARE has a Schur loop** when the
noise excites all `|λ| ≥ 1` left eigenvectors (stabilizability). The
one-step PBH–Stein kill: at `|μ| ≥ 1` the transported predictor-Joseph
identity over-balances, forcing `(AK)ᵀe = 0` and `Gᵀe = 0`, so `e` is
a left eigenvector of `A` unexcited by `G` — dead by PBH. -/
theorem fixed_point_schur {A : Matrix ι ι ℝ} {G : Matrix ι σ ℝ}
    {Qm : Matrix σ σ ℝ} (hR : R.PosDef) (hQ : Qm.PosDef)
    {P : Matrix ι ι ℝ} (hP : P.PosSemidef)
    (hfix : dareStep C R A (G * Qm * Gᵀ) P = P)
    (hstab : IsStabilizable (complexify A) (complexify G)) :
    IsSchurStable (errMap C R A P) := by
  intro μ hμ
  by_contra hlt
  rw [not_lt] at hlt
  have hμt : μ ∈ spectrum ℂ (complexify ((errMap C R A P)ᵀ)) := by
    rw [complexify_transpose]
    exact mem_spectrum_transpose_iff.mpr hμ
  obtain ⟨e, hene, heeq⟩ := exists_eigenvector_of_mem_spectrum hμt
  obtain ⟨er, herdef⟩ : ∃ er, er = fun i => (e i).re := ⟨_, rfl⟩
  obtain ⟨ei, heidef⟩ : ∃ ei, ei = fun i => (e i).im := ⟨_, rfl⟩
  -- real transported eigen-relations
  have hre1 : (errMap C R A P)ᵀ *ᵥ er = μ.re • er - μ.im • ei := by
    rw [herdef, heidef]
    funext i
    have h1 := complexify_mulVec_re ((errMap C R A P)ᵀ) e i
    rw [heeq] at h1
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h1]
  have him1 : (errMap C R A P)ᵀ *ᵥ ei = μ.im • er + μ.re • ei := by
    rw [herdef, heidef]
    funext i
    have h1 := complexify_mulVec_im ((errMap C R A P)ᵀ) e i
    rw [heeq] at h1
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h1]
    ring
  -- dissipation from the predictor-Joseph fixed point
  have hsym : P.IsHermitian := hP.1
  have hdiss : ∀ x : ι → ℝ,
      quadForm P ((errMap C R A P)ᵀ *ᵥ x)
        = quadForm P x
          - quadForm R ((A * kGain C R P)ᵀ *ᵥ x)
          - quadForm Qm (Gᵀ *ᵥ x) := by
    intro x
    have hF := quadForm_mulVec P ((errMap C R A P)ᵀ) x
    rw [Matrix.transpose_transpose] at hF
    have hK := quadForm_mulVec R ((A * kGain C R P)ᵀ) x
    rw [Matrix.transpose_transpose] at hK
    have hG := quadForm_mulVec Qm (Gᵀ) x
    rw [Matrix.transpose_transpose] at hG
    have h1 : quadForm P x
        = quadForm P ((errMap C R A P)ᵀ *ᵥ x)
          + quadForm R ((A * kGain C R P)ᵀ *ᵥ x)
          + quadForm Qm (Gᵀ *ᵥ x) := by
      conv_lhs => rw [fixed_predictor_stein hR hP hfix]
      rw [quadForm_add_matrix, quadForm_add_matrix, hF, hK, hG]
    linarith
  -- the rotation identity (exact, no drift)
  have hrot : quadForm P ((errMap C R A P)ᵀ *ᵥ er)
      + quadForm P ((errMap C R A P)ᵀ *ᵥ ei)
      = (μ.re ^ 2 + μ.im ^ 2)
        * (quadForm P er + quadForm P ei) := by
    rw [hre1, him1]
    have hsub : μ.re • er - μ.im • ei
        = μ.re • er + (-μ.im) • ei := by
      module
    rw [hsub, quadForm_add_of_isHermitian hsym,
      quadForm_add_of_isHermitian hsym, quadForm_smul,
      quadForm_smul, quadForm_smul, quadForm_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul,
      dotProduct_smul, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  -- `|μ|² ≥ 1` over-balances: the noise terms vanish
  have hn : 1 ≤ μ.re ^ 2 + μ.im ^ 2 := by
    have h1 : Complex.normSq μ = μ.re * μ.re + μ.im * μ.im :=
      Complex.normSq_apply μ
    have h2 : Complex.normSq μ = ‖μ‖ ^ 2 := by
      rw [Complex.sq_norm]
    nlinarith [hlt]
  have hbal : quadForm R ((A * kGain C R P)ᵀ *ᵥ er)
      + quadForm Qm (Gᵀ *ᵥ er)
      + quadForm R ((A * kGain C R P)ᵀ *ᵥ ei)
      + quadForm Qm (Gᵀ *ᵥ ei) = 0 := by
    have h1 := hdiss er
    have h2 := hdiss ei
    rw [h1, h2] at hrot
    have hq1 := hP.quadForm_nonneg er
    have hq2 := hP.quadForm_nonneg ei
    have hr1 := hR.posSemidef.quadForm_nonneg
      ((A * kGain C R P)ᵀ *ᵥ er)
    have hr2 := hR.posSemidef.quadForm_nonneg
      ((A * kGain C R P)ᵀ *ᵥ ei)
    have hg1 := hQ.posSemidef.quadForm_nonneg (Gᵀ *ᵥ er)
    have hg2 := hQ.posSemidef.quadForm_nonneg (Gᵀ *ᵥ ei)
    nlinarith
  have hr1 := hR.posSemidef.quadForm_nonneg
    ((A * kGain C R P)ᵀ *ᵥ er)
  have hr2 := hR.posSemidef.quadForm_nonneg
    ((A * kGain C R P)ᵀ *ᵥ ei)
  have hg1 := hQ.posSemidef.quadForm_nonneg (Gᵀ *ᵥ er)
  have hg2 := hQ.posSemidef.quadForm_nonneg (Gᵀ *ᵥ ei)
  have hKr : (A * kGain C R P)ᵀ *ᵥ er = 0 :=
    eq_zero_of_quadForm_eq_zero_of_posDef hR (by linarith)
  have hKi : (A * kGain C R P)ᵀ *ᵥ ei = 0 :=
    eq_zero_of_quadForm_eq_zero_of_posDef hR (by linarith)
  have hGr : Gᵀ *ᵥ er = 0 :=
    eq_zero_of_quadForm_eq_zero_of_posDef hQ (by linarith)
  have hGi : Gᵀ *ᵥ ei = 0 :=
    eq_zero_of_quadForm_eq_zero_of_posDef hQ (by linarith)
  -- recombine and kill by PBH
  have hKc : complexify ((A * kGain C R P)ᵀ) *ᵥ e = 0 := by
    refine complexify_mulVec_eq_zero _ _ ?_ ?_
    · rw [← herdef]; exact hKr
    · rw [← heidef]; exact hKi
  have hGc : complexify (Gᵀ) *ᵥ e = 0 := by
    refine complexify_mulVec_eq_zero _ _ ?_ ?_
    · rw [← herdef]; exact hGr
    · rw [← heidef]; exact hGi
  have hAt : complexify (Aᵀ) *ᵥ e = μ • e := by
    have hFt : (errMap C R A P)ᵀ
        = Aᵀ - Cᵀ * (A * kGain C R P)ᵀ := by
      unfold errMap
      rw [Matrix.transpose_mul, Matrix.transpose_sub,
        Matrix.transpose_one, Matrix.transpose_mul, Matrix.sub_mul,
        Matrix.one_mul, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have h1 : complexify ((errMap C R A P)ᵀ) *ᵥ e
        = complexify (Aᵀ) *ᵥ e
          - complexify (Cᵀ)
            *ᵥ (complexify ((A * kGain C R P)ᵀ) *ᵥ e) := by
      rw [hFt, complexify_sub, Matrix.sub_mulVec, complexify_mul,
        ← Matrix.mulVec_mulVec]
    rw [hKc, Matrix.mulVec_zero, sub_zero] at h1
    rw [← h1, heeq]
  have h0 : e = 0 := by
    refine hstab μ e hlt ?_ ?_
    · rw [complexify_transpose] at hAt
      exact hAt
    · rw [complexify_transpose] at hGc
      exact hGc
  exact hene h0

/-! ### Uniqueness of stabilizing fixed points -/

/-- Two fixed points with Schur loops coincide: the exact cross-loop
identity `Δ = F^kΔ(F'^k)ᵀ` is squeezed by the geometric decays. -/
theorem stabilizing_fixed_unique {A Qw : Matrix ι ι ℝ}
    (hR : R.PosDef) {P P' : Matrix ι ι ℝ}
    (hP : P.PosSemidef) (hP' : P'.PosSemidef)
    (hfix : dareStep C R A Qw P = P)
    (hfix' : dareStep C R A Qw P' = P')
    (hS : IsSchurStable (errMap C R A P))
    (hS' : IsSchurStable (errMap C R A P')) :
    P = P' := by
  have hone : P - P'
      = errMap C R A P * (P - P') * (errMap C R A P')ᵀ := by
    conv_lhs => rw [← hfix, ← hfix']
    exact dareStep_diff hR hP hP'
  have hdiff : ∀ k : ℕ, P - P'
      = errMap C R A P ^ k * (P - P')
        * ((errMap C R A P' ^ k)ᵀ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc P - P'
          = errMap C R A P * (P - P') * (errMap C R A P')ᵀ := hone
      _ = errMap C R A P
            * (errMap C R A P ^ k * (P - P')
              * (errMap C R A P' ^ k)ᵀ)
            * (errMap C R A P')ᵀ := by rw [← ih]
      _ = (errMap C R A P * errMap C R A P ^ k) * (P - P')
            * ((errMap C R A P' ^ k)ᵀ * (errMap C R A P')ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = errMap C R A P ^ (k + 1) * (P - P')
            * ((errMap C R A P' ^ (k + 1))ᵀ) := by
          rw [← pow_succ', ← Matrix.transpose_mul, ← pow_succ']
  obtain ⟨c, ρ, hc, hρ0, hρ1, hpow⟩ := hS.exists_pow_norm_le
  obtain ⟨c', ρ', hc', hρ0', hρ1', hpow'⟩ := hS'.exists_pow_norm_le
  have hbound : ∀ k : ℕ, ‖P - P'‖
      ≤ (c * c' * (Fintype.card ι : ℝ) * ‖P - P'‖) * (ρ * ρ') ^ k := by
    intro k
    calc ‖P - P'‖
        = ‖errMap C R A P ^ k * (P - P')
            * ((errMap C R A P' ^ k)ᵀ)‖ := by rw [← hdiff k]
    _ ≤ ‖errMap C R A P ^ k‖ * ‖P - P'‖
          * ‖(errMap C R A P' ^ k)ᵀ‖ := norm_triple_le _ _ _
    _ ≤ (c * ρ ^ k * ‖P - P'‖)
          * ((Fintype.card ι : ℝ) * (c' * ρ' ^ k)) := by
        have h1 := hpow k
        have h3 := hpow' k
        have h6 : (0:ℝ) ≤ ‖P - P'‖ := norm_nonneg _
        have h2 : ‖(errMap C R A P' ^ k)ᵀ‖
            ≤ (Fintype.card ι : ℝ) * (c' * ρ' ^ k) :=
          le_trans (linfty_opNorm_transpose_le' _)
            (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _))
        refine mul_le_mul ?_ h2 (norm_nonneg _) ?_
        · exact mul_le_mul_of_nonneg_right h1 h6
        · have h4 : (0:ℝ) ≤ ρ ^ k := by positivity
          positivity
    _ = (c * c' * (Fintype.card ι : ℝ) * ‖P - P'‖)
          * (ρ * ρ') ^ k := by
        rw [mul_pow]
        ring
  have hρρ : ρ * ρ' < 1 := by nlinarith
  have hρρ0 : 0 ≤ ρ * ρ' := by positivity
  have hlim : Tendsto
      (fun k => (c * c' * (Fintype.card ι : ℝ) * ‖P - P'‖)
        * (ρ * ρ') ^ k) atTop (nhds 0) := by
    have h1 := tendsto_pow_atTop_nhds_zero_of_lt_one hρρ0 hρρ
    have h2 := h1.const_mul (c * c' * (Fintype.card ι : ℝ) * ‖P - P'‖)
    simpa using h2
  have hle : ‖P - P'‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  have h0 : P - P' = 0 := by
    rw [← norm_le_zero_iff]
    exact hle
  exact sub_eq_zero.mp h0

/-! ### Assembly: the stabilizing solution exists -/

/-- **The reduced `fact:dare-strong` (D2)**: for a detectable,
stabilizable pair with `R, Q ≻ 0`, the zero-seed DARE run converges
to a PSD fixed point with Schur loop — the (unique) stabilizing
solution. -/
theorem exists_stabilizing_solution {A : Matrix ι ι ℝ}
    {G : Matrix ι σ ℝ} {Qm : Matrix σ σ ℝ}
    (hR : R.PosDef) (hQ : Qm.PosDef)
    (hdet : IsDetectable (complexify A) (complexify C))
    (hstab : IsStabilizable (complexify A) (complexify G)) :
    ∃ P : Matrix ι ι ℝ, P.PosSemidef
      ∧ dareStep C R A (G * Qm * Gᵀ) P = P
      ∧ IsSchurStable (errMap C R A P)
      ∧ Tendsto (fun T => ‖dareIter C R A (G * Qm * Gᵀ) 0 T - P‖)
          atTop (nhds 0) := by
  have hQw : (G * Qm * Gᵀ).PosSemidef := by
    have h := hQ.posSemidef.mul_mul_conjTranspose_same G
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  obtain ⟨b, hb, hbdd⟩ :=
    exists_dare_bound hR hQw Matrix.PosSemidef.zero hdet
  obtain ⟨P, hPpsd, hdom, htend⟩ := monotone_psd_tendsto
    (M := fun T => dareIter C R A (G * Qm * Gᵀ) 0 T)
    (fun T => dareIter_posSemidef hR hQw Matrix.PosSemidef.zero T)
    (fun T => dareIter_zero_mono hR hQw T)
    (fun T x => hbdd T x)
  have hstep := dareStep_tendsto_of_tendsto (C := C) (A := A)
    (Qw := G * Qm * Gᵀ) hR
    (fun T => dareIter_posSemidef hR hQw Matrix.PosSemidef.zero T)
    hPpsd htend
  -- the limit is a fixed point
  have hshift : Tendsto
      (fun T => ‖dareIter C R A (G * Qm * Gᵀ) 0 (T + 1) - P‖)
      atTop (nhds 0) := by
    have h1 : (fun T => ‖dareIter C R A (G * Qm * Gᵀ) 0 (T + 1) - P‖)
        = (fun T => ‖dareIter C R A (G * Qm * Gᵀ) 0 T - P‖)
          ∘ (fun T => T + 1) := rfl
    rw [h1]
    exact htend.comp (tendsto_add_atTop_nat 1)
  have hfix : dareStep C R A (G * Qm * Gᵀ) P = P := by
    have hb2 : ∀ T, ‖dareStep C R A (G * Qm * Gᵀ) P - P‖
        ≤ ‖dareStep C R A (G * Qm * Gᵀ)
              (dareIter C R A (G * Qm * Gᵀ) 0 T)
            - dareStep C R A (G * Qm * Gᵀ) P‖
          + ‖dareIter C R A (G * Qm * Gᵀ) 0 (T + 1) - P‖ := by
      intro T
      have h1 : dareStep C R A (G * Qm * Gᵀ) P - P
          = -(dareStep C R A (G * Qm * Gᵀ)
                (dareIter C R A (G * Qm * Gᵀ) 0 T)
              - dareStep C R A (G * Qm * Gᵀ) P)
            + (dareIter C R A (G * Qm * Gᵀ) 0 (T + 1) - P) := by
        rw [dareIter_succ]
        abel
      calc ‖dareStep C R A (G * Qm * Gᵀ) P - P‖
          = ‖-(dareStep C R A (G * Qm * Gᵀ)
                  (dareIter C R A (G * Qm * Gᵀ) 0 T)
                - dareStep C R A (G * Qm * Gᵀ) P)
              + (dareIter C R A (G * Qm * Gᵀ) 0 (T + 1) - P)‖ := by
            rw [← h1]
      _ ≤ ‖-(dareStep C R A (G * Qm * Gᵀ)
                (dareIter C R A (G * Qm * Gᵀ) 0 T)
              - dareStep C R A (G * Qm * Gᵀ) P)‖
            + ‖dareIter C R A (G * Qm * Gᵀ) 0 (T + 1) - P‖ :=
          norm_add_le _ _
      _ = _ := by rw [norm_neg]
    have hsum : Tendsto (fun T =>
        ‖dareStep C R A (G * Qm * Gᵀ)
            (dareIter C R A (G * Qm * Gᵀ) 0 T)
          - dareStep C R A (G * Qm * Gᵀ) P‖
        + ‖dareIter C R A (G * Qm * Gᵀ) 0 (T + 1) - P‖)
        atTop (nhds 0) := by
      have h := hstep.add hshift
      simpa using h
    have hle : ‖dareStep C R A (G * Qm * Gᵀ) P - P‖ ≤ 0 :=
      ge_of_tendsto hsum (Filter.Eventually.of_forall hb2)
    have h0 : dareStep C R A (G * Qm * Gᵀ) P - P = 0 := by
      rw [← norm_le_zero_iff]
      exact hle
    exact sub_eq_zero.mp h0
  exact ⟨P, hPpsd, hfix,
    fixed_point_schur hR hQ hPpsd hfix hstab, htend⟩

/-! ### The frame instantiation -/

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- Reduced detectability: C1 restricts through `emb1`. -/
lemma reduced_detectable (hC1 : S.C1) :
    IsDetectable (complexify S.A₁) (complexify S.C₁) := by
  intro μ v hμ hAv hCv
  have he1 : complexify S.fullA
      *ᵥ (complexify (emb1 n₁ na nm) *ᵥ v)
      = μ • (complexify (emb1 n₁ na nm) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← complexify_mul, S.fullA_mul_emb1,
      complexify_mul, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul]
  have hc : complexify S.fullC
      *ᵥ (complexify (emb1 n₁ na nm) *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, ← complexify_mul, S.fullC_mul_emb1, hCv]
  have h0 := hC1 μ _ hμ he1 hc
  have hv : v = complexify ((emb1 n₁ na nm)ᵀ)
      *ᵥ (complexify (emb1 n₁ na nm) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← complexify_mul, emb1t_mul_emb1,
      complexify_one, Matrix.one_mulVec]
  rw [hv, h0, Matrix.mulVec_zero]

/-- **D2, instantiated**: the reduced zero-seed run `redP` converges
to the (unique) reduced stabilizing solution. -/
theorem redP_exists_stabilizing (hC1 : S.C1) :
    ∃ P : Matrix (Fin n₁) (Fin n₁) ℝ, P.PosSemidef
      ∧ dareStep S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ) P = P
      ∧ IsSchurStable (errMap S.C₁ S.R S.A₁ P)
      ∧ Tendsto (fun T => ‖S.redP T - P‖) atTop (nhds 0) :=
  exists_stabilizing_solution S.hR S.hQ
    (S.reduced_detectable hC1) S.hStab

end DareSystem

end Dare
end Estimation
