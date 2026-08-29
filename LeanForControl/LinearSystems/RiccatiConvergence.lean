import LeanForControl.LinearSystems.LQ
import LeanForControl.LinearSystems.Schur
import LeanForControl.LinearSystems.Detectability
import LeanForControl.LinearSystems.LQStability
import Mathlib.Topology.Instances.Matrix
import Architect

/-!
# Convergence of the Riccati value iteration (M2 layer)

The classical convergence theory behind `fact:lqr`, staged for
discharge: the value iterates are Loewner-monotone; under a uniform
quadratic bound they converge entrywise (by polarization) to a positive
semidefinite fixed point of the Riccati step, whose closed loop is
Schur whenever the state penalty is detectable (an eigenvector argument
on the Joseph form).
-/

set_option linter.style.show false

namespace LinearSystems

open Matrix Filter

open scoped Matrix.Norms.Operator

namespace LQSystem

variable {d m' : ℕ} (S : LQSystem (Fin d) (Fin m'))

private lemma single_dot_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (i j : ι) :
    (Pi.single i 1 : ι → ℝ) ⬝ᵥ (M *ᵥ (Pi.single j 1 : ι → ℝ))
      = M i j := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite,
    Finset.sum_ite_eq']

private lemma entry_eq_polarization {ι : Type*} [Fintype ι]
    [DecidableEq ι] {M : Matrix ι ι ℝ} (hM : Mᵀ = M) (i j : ι) :
    M i j = (quadForm M (Pi.single i 1 + Pi.single j 1)
      - quadForm M (Pi.single i 1) - quadForm M (Pi.single j 1)) / 2 := by
  rw [quadForm_add]
  have h1 : (Pi.single j 1 : ι → ℝ) ⬝ᵥ (M *ᵥ (Pi.single i 1 : ι → ℝ))
      = M i j := by
    rw [single_dot_mulVec]
    calc M j i = Mᵀ i j := rfl
    _ = M i j := by rw [hM]
  rw [single_dot_mulVec, h1]
  ring

/-- **Monotone bounded convergence of the value iterates**: a uniform
quadratic bound turns Loewner monotonicity into entrywise convergence,
by polarization. -/
theorem exists_ric_limit_of_bounded {c : ℝ}
    (hb : ∀ (T : ℕ) (x : Fin d → ℝ),
      quadForm (S.ric T) x ≤ c * ‖x‖ ^ 2) :
    ∃ P : Matrix (Fin d) (Fin d) ℝ, P.PosSemidef ∧
      Tendsto (fun T => S.ric T) atTop (nhds P) := by
  classical
  -- pointwise limits of the quadratic forms
  have hmono : ∀ x : Fin d → ℝ, Monotone fun T => quadForm (S.ric T) x := by
    intro x
    refine monotone_nat_of_le_succ fun T => S.quadForm_ric_mono x T
  have hbdd : ∀ x : Fin d → ℝ,
      BddAbove (Set.range fun T => quadForm (S.ric T) x) := by
    intro x
    exact ⟨c * ‖x‖ ^ 2, by rintro y ⟨T, rfl⟩; exact hb T x⟩
  have hqtend : ∀ x : Fin d → ℝ,
      Tendsto (fun T => quadForm (S.ric T) x) atTop
        (nhds (⨆ T, quadForm (S.ric T) x)) := by
    intro x
    exact tendsto_atTop_ciSup (hmono x) (hbdd x)
  -- the limit matrix, defined entrywise by polarization
  set P : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i j =>
    ((⨆ T, quadForm (S.ric T) (Pi.single i 1 + Pi.single j 1))
      - (⨆ T, quadForm (S.ric T) (Pi.single i 1))
      - (⨆ T, quadForm (S.ric T) (Pi.single j 1))) / 2 with hP
  have hrict : ∀ T, (S.ric T)ᵀ = S.ric T := fun T => by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact S.ric_isHermitian T
  have hkey : ∀ i j, Tendsto (fun T => S.ric T i j) atTop
      (nhds (P i j)) := by
    intro i j
    have hentry : ∀ T, S.ric T i j
        = (quadForm (S.ric T) (Pi.single i 1 + Pi.single j 1)
          - quadForm (S.ric T) (Pi.single i 1)
          - quadForm (S.ric T) (Pi.single j 1)) / 2 := fun T =>
      entry_eq_polarization (hrict T) i j
    simp only [hentry]
    exact (((hqtend _).sub (hqtend _)).sub (hqtend _)).div_const 2
  have htend : Tendsto (fun T => S.ric T) atTop (nhds P) :=
    tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => hkey i j
  -- the limit is positive semidefinite
  have hqf : ∀ x : Fin d → ℝ, Tendsto (fun T => quadForm (S.ric T) x)
      atTop (nhds (quadForm P x)) := by
    intro x
    have hcont : Continuous fun M : Matrix (Fin d) (Fin d) ℝ =>
        quadForm M x :=
      Continuous.dotProduct continuous_const
        (continuous_id.matrix_mulVec continuous_const)
    exact (hcont.tendsto _).comp htend
  have hPpsd : P.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · -- symmetric limit of symmetric matrices
      have hPt : Pᵀ = P := by
        funext i j
        show P j i = P i j
        show ((⨆ T, quadForm (S.ric T)
              (Pi.single j 1 + Pi.single i 1))
            - (⨆ T, quadForm (S.ric T) (Pi.single j 1))
            - (⨆ T, quadForm (S.ric T) (Pi.single i 1))) / 2
          = ((⨆ T, quadForm (S.ric T)
              (Pi.single i 1 + Pi.single j 1))
            - (⨆ T, quadForm (S.ric T) (Pi.single i 1))
            - (⨆ T, quadForm (S.ric T) (Pi.single j 1))) / 2
        have h1 : (Pi.single j 1 : Fin d → ℝ) + Pi.single i 1
            = Pi.single i 1 + Pi.single j 1 := add_comm _ _
        rw [h1]
        ring
      rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
      exact hPt
    · have h1 := ge_of_tendsto (hqf x) (Filter.Eventually.of_forall
        fun T => (S.ric_posSemidef T).quadForm_nonneg x)
      simpa [quadForm] using h1
  exact ⟨P, hPpsd, htend⟩

/-! ### The limit is a fixed point (continuity of the Riccati step) -/

/-- The Riccati step is continuous wherever the curvature is
invertible — in particular at any PSD point. -/
theorem continuousAt_step {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosSemidef) : ContinuousAt S.step P := by
  have hdet : (S.gainΓ P).det ≠ 0 := (S.gainΓ_posDef hP).det_pos.ne'
  have hΓcont : Continuous fun Q : Matrix (Fin d) (Fin d) ℝ =>
      S.gainΓ Q := by
    unfold gainΓ
    exact continuous_const.add ((continuous_const.matrix_mul
      continuous_id).matrix_mul continuous_const)
  have hinv : ContinuousAt
      (fun Q : Matrix (Fin d) (Fin d) ℝ => (S.gainΓ Q)⁻¹) P := by
    refine ContinuousAt.comp ?_ hΓcont.continuousAt
    refine continuousAt_matrix_inv _ ?_
    have h1 : (Ring.inverse : ℝ → ℝ) = Inv.inv := by
      funext x
      exact Ring.inverse_eq_inv x
    rw [h1]
    exact continuousAt_inv₀ hdet
  -- assemble `step` from continuous pieces and the inverse
  have h2 : ContinuousAt (fun Q : Matrix (Fin d) (Fin d) ℝ =>
      S.Aᵀ * Q * S.B * (S.gainΓ Q)⁻¹ * S.Bᵀ * Q * S.A) P := by
    have hL : Continuous fun Q : Matrix (Fin d) (Fin d) ℝ =>
        S.Aᵀ * Q * S.B :=
      (continuous_const.matrix_mul continuous_id).matrix_mul
        continuous_const
    have hR : Continuous fun Q : Matrix (Fin d) (Fin d) ℝ =>
        S.Bᵀ * Q * S.A :=
      (continuous_const.matrix_mul continuous_id).matrix_mul
        continuous_const
    have hmul2 : ContinuousAt (fun Q : Matrix (Fin d) (Fin d) ℝ =>
        S.Aᵀ * Q * S.B * (S.gainΓ Q)⁻¹) P := by
      have hpair : ContinuousAt (fun Q : Matrix (Fin d) (Fin d) ℝ =>
          (S.Aᵀ * Q * S.B, (S.gainΓ Q)⁻¹)) P :=
        hL.continuousAt.prodMk hinv
      have hbil : Continuous fun p :
          Matrix (Fin d) (Fin m') ℝ × Matrix (Fin m') (Fin m') ℝ =>
            p.1 * p.2 :=
        continuous_fst.matrix_mul continuous_snd
      exact hbil.continuousAt.comp hpair
    have hpair2 : ContinuousAt (fun Q : Matrix (Fin d) (Fin d) ℝ =>
        (S.Aᵀ * Q * S.B * (S.gainΓ Q)⁻¹, S.Bᵀ * Q * S.A)) P :=
      hmul2.prodMk hR.continuousAt
    have hbil2 : Continuous fun p :
        Matrix (Fin d) (Fin m') ℝ × Matrix (Fin m') (Fin d) ℝ =>
          p.1 * p.2 :=
      continuous_fst.matrix_mul continuous_snd
    have h3 := hbil2.continuousAt.comp hpair2
    have heq : (fun Q : Matrix (Fin d) (Fin d) ℝ =>
        S.Aᵀ * Q * S.B * (S.gainΓ Q)⁻¹ * S.Bᵀ * Q * S.A)
        = fun Q =>
          S.Aᵀ * Q * S.B * (S.gainΓ Q)⁻¹ * (S.Bᵀ * Q * S.A) := by
      funext Q
      simp only [Matrix.mul_assoc]
    rw [heq]
    exact h3
  have h4 : ContinuousAt (fun Q : Matrix (Fin d) (Fin d) ℝ =>
      S.Qs + S.Aᵀ * Q * S.A) P :=
    (continuous_const.add ((continuous_const.matrix_mul
      continuous_id).matrix_mul continuous_const)).continuousAt
  exact h4.sub h2

/-- The limit of the value iterates is a Riccati fixed point. -/
theorem step_fixed_of_tendsto {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosSemidef)
    (htend : Tendsto (fun T => S.ric T) atTop (nhds P)) :
    S.step P = P := by
  have h1 : Tendsto (fun T => S.step (S.ric T)) atTop
      (nhds (S.step P)) := (S.continuousAt_step hP).tendsto.comp htend
  have h2 : Tendsto (fun T => S.ric (T + 1)) atTop (nhds P) :=
    htend.comp (tendsto_add_atTop_nat 1)
  have h3 : (fun T => S.step (S.ric T)) = fun T => S.ric (T + 1) := rfl
  rw [h3] at h1
  exact tendsto_nhds_unique h1 h2

/-- The gains converge along with the iterates. -/
theorem gainK_tendsto_of_tendsto {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosSemidef)
    (htend : Tendsto (fun T => S.ric T) atTop (nhds P)) :
    Tendsto (fun T => S.gainK (S.ric T)) atTop
      (nhds (S.gainK P)) := by
  have hdet : (S.gainΓ P).det ≠ 0 := (S.gainΓ_posDef hP).det_pos.ne'
  have hΓcont : Continuous fun Q : Matrix (Fin d) (Fin d) ℝ =>
      S.gainΓ Q := by
    unfold gainΓ
    exact continuous_const.add ((continuous_const.matrix_mul
      continuous_id).matrix_mul continuous_const)
  have hinv : ContinuousAt
      (fun Q : Matrix (Fin d) (Fin d) ℝ => (S.gainΓ Q)⁻¹) P := by
    refine ContinuousAt.comp ?_ hΓcont.continuousAt
    refine continuousAt_matrix_inv _ ?_
    have h1 : (Ring.inverse : ℝ → ℝ) = Inv.inv := by
      funext x
      exact Ring.inverse_eq_inv x
    rw [h1]
    exact continuousAt_inv₀ hdet
  have hR : Continuous fun Q : Matrix (Fin d) (Fin d) ℝ =>
      S.Bᵀ * Q * S.A :=
    (continuous_const.matrix_mul continuous_id).matrix_mul
      continuous_const
  have hpair : ContinuousAt (fun Q : Matrix (Fin d) (Fin d) ℝ =>
      ((S.gainΓ Q)⁻¹, S.Bᵀ * Q * S.A)) P := hinv.prodMk hR.continuousAt
  have hbil : Continuous fun p :
      Matrix (Fin m') (Fin m') ℝ × Matrix (Fin m') (Fin d) ℝ =>
        p.1 * p.2 :=
    continuous_fst.matrix_mul continuous_snd
  have h2 := (hbil.continuousAt.comp hpair).tendsto.comp htend
  have heq : (fun T => S.gainK (S.ric T))
      = fun T => (S.gainΓ (S.ric T))⁻¹ * (S.Bᵀ * S.ric T * S.A) := by
    funext T
    unfold gainK
    simp only [Matrix.mul_assoc]
  have h3 : S.gainK P = (S.gainΓ P)⁻¹ * (S.Bᵀ * P * S.A) := by
    unfold gainK
    simp only [Matrix.mul_assoc]
  rw [heq, h3]
  exact h2

/-! ### The closed loop at a fixed point is Schur (detectability) -/

private lemma re_star_dotProduct_complexify' {k : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ) (x : Fin k → ℂ) :
    (star x ⬝ᵥ (complexify M *ᵥ x)).re
      = quadForm M (fun i => (x i).re) + quadForm M (fun i => (x i).im) := by
  have hL : (star x ⬝ᵥ (complexify M *ᵥ x)).re
      = ∑ i, ∑ j, M i j * ((x i).re * (x j).re + (x i).im * (x j).im) := by
    simp only [dotProduct, Matrix.mulVec, complexify_apply, Pi.star_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hR : quadForm M (fun i => (x i).re) + quadForm M (fun i => (x i).im)
      = ∑ i, ∑ j, M i j * ((x i).re * (x j).re + (x i).im * (x j).im) := by
    simp only [quadForm, dotProduct, Matrix.mulVec]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL, hR]

/-- **The closed loop at a detectable fixed point is Schur**: an
eigenvector with `‖μ‖ ≥ 1` would make the Joseph decrement vanish,
exposing an undetectable unstable mode. -/
theorem acl_schur_of_fixed {P : Matrix (Fin d) (Fin d) ℝ}
    (hP : P.PosSemidef) (hfix : S.step P = P) (hdet : S.QsDetectable) :
    IsSchurStable (S.Acl P) := by
  intro μ hμ
  by_contra hge
  push Not at hge
  -- extract an eigenvector
  have hspec : μ ∈ spectrum ℂ (Matrix.toLin' (complexify (S.Acl P))) := by
    rw [Matrix.spectrum_toLin']
    exact hμ
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    hspec).exists_hasEigenvector
  have hAv : complexify (S.Acl P) *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  set vr : Fin d → ℝ := fun i => (v i).re with hvr
  set vi : Fin d → ℝ := fun i => (v i).im with hvi
  -- the Joseph identity evaluated on the eigenvector
  have hjoseph := S.step_eq_joseph hP
  rw [hfix] at hjoseph
  -- real quadratic forms of the real and imaginary parts
  have hAclr : ∀ x : Fin d → ℝ,
      quadForm P (S.Acl P *ᵥ x) = quadForm ((S.Acl P)ᵀ * P * S.Acl P) x :=
    fun x => quadForm_mulVec _ _ _
  have hqf : ∀ x : Fin d → ℝ, quadForm P x
      = quadForm P (S.Acl P *ᵥ x) + quadForm S.Qs x
        + quadForm ((S.gainK P)ᵀ * S.Ru * S.gainK P) x := by
    intro x
    conv_lhs => rw [hjoseph]
    rw [quadForm_add_matrix, quadForm_add_matrix, hAclr]
  -- the eigen-relation moves the closed loop across the real parts
  have hre : S.Acl P *ᵥ vr = fun i => (μ • v : Fin d → ℂ) i |>.re := by
    funext i
    rw [← hAv]
    exact (complexify_mulVec_re _ v i).symm
  have him : S.Acl P *ᵥ vi = fun i => (μ • v : Fin d → ℂ) i |>.im := by
    funext i
    rw [← hAv]
    exact (complexify_mulVec_im _ v i).symm
  -- `‖μ‖ ≥ 1` forces the quadratic decrement to vanish
  have hgrow : quadForm P (S.Acl P *ᵥ vr) + quadForm P (S.Acl P *ᵥ vi)
      = ‖μ‖ ^ 2 * (quadForm P vr + quadForm P vi) := by
    have h1 : (star v ⬝ᵥ (complexify P *ᵥ v)).re
        = quadForm P vr + quadForm P vi :=
      re_star_dotProduct_complexify' P v
    have h2 : (star (μ • v) ⬝ᵥ (complexify P *ᵥ (μ • v))).re
        = quadForm P (fun i => ((μ • v : Fin d → ℂ) i).re)
          + quadForm P (fun i => ((μ • v : Fin d → ℂ) i).im) :=
      re_star_dotProduct_complexify' P (μ • v)
    have h3 : star (μ • v) ⬝ᵥ (complexify P *ᵥ (μ • v))
        = (star μ * μ) • (star v ⬝ᵥ (complexify P *ᵥ v)) := by
      rw [Matrix.mulVec_smul, star_smul, smul_dotProduct,
        dotProduct_smul, smul_smul]
    have h4 : (star μ * μ : ℂ) = ((‖μ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, mul_comm, Complex.mul_conj,
        Complex.normSq_eq_norm_sq]
    have h5 : (star (μ • v) ⬝ᵥ (complexify P *ᵥ (μ • v))).re
        = ‖μ‖ ^ 2 * (star v ⬝ᵥ (complexify P *ᵥ v)).re := by
      rw [h3, h4]
      exact Complex.re_ofReal_mul _ _
    rw [h2, h1] at h5
    rw [hre, him]
    exact h5
  -- sum the Joseph identities on `vr` and `vi`
  have hqvr := hqf vr
  have hqvi := hqf vi
  have hpnn : 0 ≤ quadForm P vr + quadForm P vi :=
    add_nonneg (hP.quadForm_nonneg _) (hP.quadForm_nonneg _)
  have hqnn : 0 ≤ quadForm S.Qs vr + quadForm S.Qs vi :=
    add_nonneg (S.hQs.quadForm_nonneg _) (S.hQs.quadForm_nonneg _)
  have hkr : ∀ x : Fin d → ℝ,
      quadForm ((S.gainK P)ᵀ * S.Ru * S.gainK P) x
        = quadForm S.Ru (S.gainK P *ᵥ x) :=
    fun x => (quadForm_mulVec _ _ _).symm
  have hrnn : 0 ≤ quadForm S.Ru (S.gainK P *ᵥ vr)
      + quadForm S.Ru (S.gainK P *ᵥ vi) :=
    add_nonneg (S.hRu.posSemidef.quadForm_nonneg _)
      (S.hRu.posSemidef.quadForm_nonneg _)
  have hμ2 : 1 ≤ ‖μ‖ ^ 2 := one_le_pow₀ hge
  have hzero : quadForm S.Qs vr + quadForm S.Qs vi = 0
      ∧ quadForm S.Ru (S.gainK P *ᵥ vr)
        + quadForm S.Ru (S.gainK P *ᵥ vi) = 0 := by
    rw [hkr] at hqvr hqvi
    constructor <;> nlinarith [hgrow, hqvr, hqvi]
  -- kernel extraction: the mode is invisible and uncontrolled
  have hQsvr : S.Qs *ᵥ vr = 0 :=
    S.hQs.mulVec_eq_zero_of_quadForm_eq_zero (by
      have := S.hQs.quadForm_nonneg vr
      have := S.hQs.quadForm_nonneg vi
      linarith [hzero.1])
  have hQsvi : S.Qs *ᵥ vi = 0 :=
    S.hQs.mulVec_eq_zero_of_quadForm_eq_zero (by
      have := S.hQs.quadForm_nonneg vr
      have := S.hQs.quadForm_nonneg vi
      linarith [hzero.1])
  have hKvr : S.gainK P *ᵥ vr = 0 := by
    by_contra hne
    have h1 := S.hRu.quadForm_pos hne
    have := S.hRu.posSemidef.quadForm_nonneg (S.gainK P *ᵥ vi)
    linarith [hzero.2]
  have hKvi : S.gainK P *ᵥ vi = 0 := by
    by_contra hne
    have h1 := S.hRu.quadForm_pos hne
    have := S.hRu.posSemidef.quadForm_nonneg (S.gainK P *ᵥ vr)
    linarith [hzero.2]
  -- assemble the complex kernel facts
  have hQsv : complexify S.Qs *ᵥ v = 0 := by
    funext i
    refine Complex.ext ?_ ?_
    · rw [complexify_mulVec_re]
      have h1 : (fun j => (v j).re) = vr := rfl
      rw [h1, hQsvr]
      rfl
    · rw [complexify_mulVec_im]
      have h1 : (fun j => (v j).im) = vi := rfl
      rw [h1, hQsvi]
      rfl
  have hKv : complexify (S.gainK P) *ᵥ v = 0 := by
    funext i
    refine Complex.ext ?_ ?_
    · rw [complexify_mulVec_re]
      have h1 : (fun j => (v j).re) = vr := rfl
      rw [h1, hKvr]
      rfl
    · rw [complexify_mulVec_im]
      have h1 : (fun j => (v j).im) = vi := rfl
      rw [h1, hKvi]
      rfl
  -- the mode is an eigenvector of the open loop
  have hAv' : complexify S.A *ᵥ v = μ • v := by
    have h1 : S.A = S.Acl P + S.B * S.gainK P := by
      unfold Acl
      abel
    rw [h1, complexify_add, Matrix.add_mulVec, hAv, complexify_mul,
      ← Matrix.mulVec_mulVec, hKv, Matrix.mulVec_zero, add_zero]
  exact hv.2 (hdet μ v hge hAv' hQsv)

end LQSystem

end LinearSystems
