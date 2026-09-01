import LeanForControl.Estimation.Dare.RateFloor
import Architect

/-!
# The spectrum of the strong loop (`eq:Finf-spec`, verified core)

`thm:main`'s spectral import discharged: the strong error loop
`F∞ = A(I − K∞C)` is block-triangular with respect to the
`(e₁ ⊕ a | m)` split — `embMᵀF∞embS = 0`, a consequence of marginal
extinction — and its `(e₁ ⊕ a)`-compression
`Fs = embSᵀF∞embS` is **Schur stable** (`strong_Fs_schur`).

The proof is a PBH–Stein argument on the unit circle:

* `|μ| > 1` is impossible outright: a right eigenvector of `Fs`
  embeds through `F∞·embS = embS·Fs` into an eigenvector of `F∞`,
  contradicting `ρ(F∞) ≤ 1` (the bundle's `specLe`).
* `|μ| = 1` collapses the predictor Stein relation
  (`strong_predictor_stein`, the fixed point in Joseph form): one
  step of the transported energy identity forces the noise terms of
  a left quasi-eigenvector to vanish — `(AK∞)ᵀe = 0`, `Gᵀe = 0` —
  so `e` is a left eigenvector of `A` unexcited by `G`. Its `e₁`
  part dies by stabilizability (PBH), its `a` part by `|λ(Aa)| > 1`,
  its `m` part was never there (`embMᵀembS = 0`), so `e = 0`:
  contradiction.

No induction over powers is needed: the marginal correction of the
quasi-eigenvector is annihilated by `Σ∞·embM = 0` inside the energy,
and the rotation `μ` cancels in `re² + im²`, so a single Stein step
already balances exactly.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

/-! ### Helpers: eigenvectors, complexification, PD extraction -/

section Helpers

set_option linter.unusedSectionVars false

variable {ι' κ' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ']

/-- A spectrum member of a complex matrix has an eigenvector. -/
lemma exists_eigenvector_of_mem_spectrum {M : Matrix ι' ι' ℂ} {μ : ℂ}
    (h : μ ∈ spectrum ℂ M) :
    ∃ v : ι' → ℂ, v ≠ 0 ∧ M *ᵥ v = μ • v := by
  rw [← Matrix.spectrum_toLin'] at h
  have hE : Module.End.HasEigenvalue (Matrix.toLin' M) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr h
  obtain ⟨v, hv⟩ := hE.exists_hasEigenvector
  refine ⟨v, hv.2, ?_⟩
  have h1 := hv.apply_eq_smul
  simpa [Matrix.toLin'_apply] using h1

/-- Complexification of a difference. -/
lemma complexify_sub (A B : Matrix ι' κ' ℝ) :
    complexify (A - B) = complexify A - complexify B := by
  ext i j
  simp

/-- A complexified action vanishes when it kills both real parts. -/
lemma complexify_mulVec_eq_zero (M : Matrix ι' κ' ℝ) (w : κ' → ℂ)
    (hre : M *ᵥ (fun j => (w j).re) = 0)
    (him : M *ᵥ (fun j => (w j).im) = 0) :
    complexify M *ᵥ w = 0 := by
  funext i
  refine Complex.ext ?_ ?_
  · rw [complexify_mulVec_re M w i, hre]
    rfl
  · rw [complexify_mulVec_im M w i, him]
    rfl

/-- A positive definite quadratic form vanishes only at zero. -/
lemma eq_zero_of_quadForm_eq_zero_of_posDef {M : Matrix ι' ι' ℝ}
    (hM : M.PosDef) {y : ι' → ℝ} (hy : quadForm M y = 0) : y = 0 := by
  by_contra hne
  exact absurd hy (ne_of_gt (hM.quadForm_pos hne))

end Helpers

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-! ### Table extensions for `embS` -/

lemma embSt_mul_embS :
    (embS n₁ na nm)ᵀ * embS n₁ na nm = 1 := by
  ext i j
  rcases i with i₁ | ia <;> rcases j with j₁ | ja <;>
    simp [embS, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.transpose_apply, Matrix.one_apply, Finset.sum_ite_eq,
      eq_comm]

lemma embMt_mul_embS :
    (embM n₁ na nm)ᵀ * embS n₁ na nm = 0 := by
  ext i j
  rcases j with j₁ | ja <;>
    simp [embS, embM, Matrix.mul_apply, Fintype.sum_sum_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.transpose_apply]

/-! ### Block-triangularity of the strong loop -/

/-- **`F∞` is `(e₁⊕a)`-invariant**: `F∞·embS = embS·Fs`. The `m`-rows
of `F∞` on the `embS`-range vanish by marginal extinction. -/
lemma errMap_mul_embS (hC1 : S.C1) (hS : S.IsStrongSolution Sinf) :
    errMap S.fullC S.R S.fullA Sinf * embS n₁ na nm
      = embS n₁ na nm
          * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
              * embS n₁ na nm) := by
  calc errMap S.fullC S.R S.fullA Sinf * embS n₁ na nm
      = (embS n₁ na nm * (embS n₁ na nm)ᵀ
          + embM n₁ na nm * (embM n₁ na nm)ᵀ)
          * (errMap S.fullC S.R S.fullA Sinf * embS n₁ na nm) := by
        rw [embS_embM_partition, Matrix.one_mul]
  _ = embS n₁ na nm
        * ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embS n₁ na nm)
      + embM n₁ na nm
        * ((embM n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
            * embS n₁ na nm) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
  _ = _ := by
        rw [S.embMt_mul_errMap hC1 hS, Matrix.mul_assoc S.Am,
          embMt_mul_embS, Matrix.mul_zero, Matrix.mul_zero, add_zero]

/-- The transpose decomposition against `embS` (any square matrix):
`Mᵀ·embS = embS·(embSᵀMembS)ᵀ + embM·(embMᵀMᵀembS)`. -/
lemma transpose_mul_embS_decomp
    (M : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) :
    Mᵀ * embS n₁ na nm
      = embS n₁ na nm * ((embS n₁ na nm)ᵀ * M * embS n₁ na nm)ᵀ
        + embM n₁ na nm
          * ((embM n₁ na nm)ᵀ * Mᵀ * embS n₁ na nm) := by
  have hSt : ((embS n₁ na nm)ᵀ * M * embS n₁ na nm)ᵀ
      = (embS n₁ na nm)ᵀ * Mᵀ * embS n₁ na nm := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hSt]
  calc Mᵀ * embS n₁ na nm
      = (embS n₁ na nm * (embS n₁ na nm)ᵀ
          + embM n₁ na nm * (embM n₁ na nm)ᵀ)
          * (Mᵀ * embS n₁ na nm) := by
        rw [embS_embM_partition, Matrix.one_mul]
  _ = _ := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]

/-! ### The predictor Stein relation -/

/-- The strong fixed point in predictor-Joseph form:
`Σ∞ = F∞Σ∞F∞ᵀ + (AK∞)R(AK∞)ᵀ + Q_w`. -/
lemma strong_predictor_stein (hS : S.IsStrongSolution Sinf) :
    Sinf
      = errMap S.fullC S.R S.fullA Sinf * Sinf
          * (errMap S.fullC S.R S.fullA Sinf)ᵀ
        + (S.fullA * kGain S.fullC S.R Sinf) * S.R
          * (S.fullA * kGain S.fullC S.R Sinf)ᵀ
        + S.Qw := by
  conv_lhs => rw [← hS.fixed]
  show S.fullA * updM S.fullC S.R Sinf * S.fullAᵀ + S.Qw = _
  rw [updM_eq_joseph S.hR hS.posSemidef]
  unfold joseph errMap
  simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_assoc]

/-- `F∞ᵀ = Aᵀ − Cᵀ(AK∞)ᵀ`. -/
lemma errMap_transpose_eq :
    (errMap S.fullC S.R S.fullA Sinf)ᵀ
      = S.fullAᵀ
        - S.fullCᵀ * (S.fullA * kGain S.fullC S.R Sinf)ᵀ := by
  unfold errMap
  rw [Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_mul, Matrix.sub_mul,
    Matrix.one_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

set_option maxHeartbeats 1600000 in
/-- **`eq:Finf-spec`, verified core (D1)**: the `(e₁⊕a)`-compression
of the strong error loop is Schur stable. Together with the
block-triangularity this is the deck's spectrum claim — `spec(F∞)`
splits into a Schur part and the marginal `spec(Aₘ)` — with the
unit-circle exclusion by the PBH–Stein argument. Discharges the
`hFs` import of `lem:supremal` / `thm:sufficiency` / `thm:main`. -/
theorem strong_Fs_schur (hC1 : S.C1) (hS : S.IsStrongSolution Sinf) :
    IsSchurStable ((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
      * embS n₁ na nm) := by
  intro μ hμ
  by_contra hlt
  rw [not_lt] at hlt
  rcases hlt.lt_or_eq with hgt | heq
  · -- `|μ| > 1`: embed a right eigenvector, contradict `specLe`.
    obtain ⟨v, hvne, hveq⟩ := exists_eigenvector_of_mem_spectrum hμ
    have hlift : complexify (errMap S.fullC S.R S.fullA Sinf)
        *ᵥ (complexify (embS n₁ na nm) *ᵥ v)
        = μ • (complexify (embS n₁ na nm) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← complexify_mul,
        S.errMap_mul_embS hC1 hS, complexify_mul,
        ← Matrix.mulVec_mulVec, hveq, Matrix.mulVec_smul]
    have hne : complexify (embS n₁ na nm) *ᵥ v ≠ 0 := by
      intro h0
      apply hvne
      have h1 : complexify ((embS n₁ na nm)ᵀ)
          *ᵥ (complexify (embS n₁ na nm) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, ← complexify_mul, embSt_mul_embS,
          complexify_one, Matrix.one_mulVec]
      rw [h0, Matrix.mulVec_zero] at h1
      exact h1.symm
    have hspec := hS.specLe μ (mem_spectrum_of_mulVec_eq_smul hne hlift)
    linarith
  · -- `|μ| = 1`: the Stein kill.
    have hμt : μ ∈ spectrum ℂ
        (complexify (((embS n₁ na nm)ᵀ * errMap S.fullC S.R S.fullA Sinf
          * embS n₁ na nm)ᵀ)) := by
      rw [complexify_transpose]
      exact mem_spectrum_transpose_iff.mpr hμ
    obtain ⟨w, hwne, hweq⟩ := exists_eigenvector_of_mem_spectrum hμt
    -- the quasi-eigenvector in the full space and its marginal drift
    obtain ⟨e, hedef⟩ :
        ∃ e, e = complexify (embS n₁ na nm) *ᵥ w := ⟨_, rfl⟩
    obtain ⟨b, hbdef⟩ :
        ∃ b, b = complexify ((embM n₁ na nm)ᵀ
          * (errMap S.fullC S.R S.fullA Sinf)ᵀ * embS n₁ na nm) *ᵥ w :=
      ⟨_, rfl⟩
    -- one-step quasi-eigen relation: `F∞ᵀe = μe + embM·b`
    have hstep : complexify ((errMap S.fullC S.R S.fullA Sinf)ᵀ) *ᵥ e
        = μ • e + complexify (embM n₁ na nm) *ᵥ b := by
      rw [hedef, hbdef, Matrix.mulVec_mulVec, ← complexify_mul,
        transpose_mul_embS_decomp, complexify_add, Matrix.add_mulVec,
        complexify_mul, ← Matrix.mulVec_mulVec, hweq,
        Matrix.mulVec_smul, complexify_mul, ← Matrix.mulVec_mulVec]
    -- real and imaginary transported one-step relations
    obtain ⟨er, herdef⟩ : ∃ er, er = fun i => (e i).re := ⟨_, rfl⟩
    obtain ⟨ei, heidef⟩ : ∃ ei, ei = fun i => (e i).im := ⟨_, rfl⟩
    have hre1 : (errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ er
        = μ.re • er - μ.im • ei
          + embM n₁ na nm *ᵥ (fun j => (b j).re) := by
      rw [herdef, heidef]
      funext i
      have h1 := complexify_mulVec_re
        ((errMap S.fullC S.R S.fullA Sinf)ᵀ) e i
      rw [hstep] at h1
      have h2 := complexify_mulVec_re (embM n₁ na nm) b i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Complex.add_re, Complex.mul_re] at h1
      rw [h2] at h1
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        smul_eq_mul]
      rw [← h1]
    have him1 : (errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ ei
        = μ.im • er + μ.re • ei
          + embM n₁ na nm *ᵥ (fun j => (b j).im) := by
      rw [herdef, heidef]
      funext i
      have h1 := complexify_mulVec_im
        ((errMap S.fullC S.R S.fullA Sinf)ᵀ) e i
      rw [hstep] at h1
      have h2 := complexify_mulVec_im (embM n₁ na nm) b i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Complex.add_im, Complex.mul_im] at h1
      rw [h2] at h1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← h1]
      ring
    -- the extinction kill: `Σ∞` ignores the marginal drift
    have hsym : Sinf.IsHermitian := hS.posSemidef.1
    have hkill : ∀ (x : ix n₁ na nm → ℝ) (z : Fin nm → ℝ),
        quadForm Sinf (x + embM n₁ na nm *ᵥ z) = quadForm Sinf x := by
      intro x z
      have hz : Sinf *ᵥ (embM n₁ na nm *ᵥ z) = 0 := by
        rw [Matrix.mulVec_mulVec, S.strong_marg_extinct hC1 hS,
          Matrix.zero_mulVec]
      rw [quadForm_add, hz, dotProduct_zero]
      have hzx : (embM n₁ na nm *ᵥ z) ⬝ᵥ (Sinf *ᵥ x) = 0 := by
        rw [← dotProduct_mulVec_comm hsym, hz, dotProduct_zero]
      have hq0 : quadForm Sinf (embM n₁ na nm *ᵥ z) = 0 := by
        rw [quadForm, hz, dotProduct_zero]
      rw [hzx, hq0]
      ring
    -- the dissipation identity from the predictor Stein relation
    have hdiss : ∀ x : ix n₁ na nm → ℝ,
        quadForm Sinf ((errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ x)
          = quadForm Sinf x
            - quadForm S.R
                ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ x)
            - quadForm S.Q (S.fullGᵀ *ᵥ x) := by
      intro x
      have hF := quadForm_mulVec Sinf
        ((errMap S.fullC S.R S.fullA Sinf)ᵀ) x
      rw [Matrix.transpose_transpose] at hF
      have hK := quadForm_mulVec S.R
        ((S.fullA * kGain S.fullC S.R Sinf)ᵀ) x
      rw [Matrix.transpose_transpose] at hK
      have hG := quadForm_mulVec S.Q (S.fullGᵀ) x
      rw [Matrix.transpose_transpose] at hG
      have h1 : quadForm Sinf x
          = quadForm Sinf ((errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ x)
            + quadForm S.R
                ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ x)
            + quadForm S.Q (S.fullGᵀ *ᵥ x) := by
        conv_lhs => rw [S.strong_predictor_stein hS]
        rw [quadForm_add_matrix, quadForm_add_matrix, hF, hK, hG]
        rfl
      linarith
    -- the rotation balance: one Stein step at `|μ| = 1` is exact
    have hn : μ.re ^ 2 + μ.im ^ 2 = 1 := by
      have h1 : Complex.normSq μ = μ.re * μ.re + μ.im * μ.im :=
        Complex.normSq_apply μ
      have h2 : Complex.normSq μ = ‖μ‖ ^ 2 := by
        rw [Complex.sq_norm]
      rw [← heq] at h2
      rw [h2] at h1
      nlinarith [h1]
    have hrot : quadForm Sinf
          ((errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ er)
        + quadForm Sinf ((errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ ei)
        = quadForm Sinf er + quadForm Sinf ei := by
      rw [hre1, him1, hkill _ _, hkill _ _]
      have hsub : μ.re • er - μ.im • ei
          = μ.re • er + (-μ.im) • ei := by
        module
      rw [hsub, quadForm_add_of_isHermitian hsym,
        quadForm_add_of_isHermitian hsym, quadForm_smul,
        quadForm_smul, quadForm_smul, quadForm_smul,
        Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul,
        dotProduct_smul, smul_dotProduct, smul_dotProduct,
        smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
      linear_combination
        (quadForm Sinf er + quadForm Sinf ei) * hn
    -- the noise terms vanish
    have hbal : quadForm S.R
          ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ er)
        + quadForm S.Q (S.fullGᵀ *ᵥ er)
        + quadForm S.R
            ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ ei)
        + quadForm S.Q (S.fullGᵀ *ᵥ ei) = 0 := by
      have h1 := hdiss er
      have h2 := hdiss ei
      rw [h1, h2] at hrot
      linarith
    have hnn1 := S.hR.posSemidef.quadForm_nonneg
      ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ er)
    have hnn2 := S.hQ.posSemidef.quadForm_nonneg (S.fullGᵀ *ᵥ er)
    have hnn3 := S.hR.posSemidef.quadForm_nonneg
      ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ ei)
    have hnn4 := S.hQ.posSemidef.quadForm_nonneg (S.fullGᵀ *ᵥ ei)
    have hKr : (S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ er = 0 :=
      eq_zero_of_quadForm_eq_zero_of_posDef S.hR (by linarith)
    have hKi : (S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ ei = 0 :=
      eq_zero_of_quadForm_eq_zero_of_posDef S.hR (by linarith)
    have hGr : S.fullGᵀ *ᵥ er = 0 :=
      eq_zero_of_quadForm_eq_zero_of_posDef S.hQ (by linarith)
    have hGi : S.fullGᵀ *ᵥ ei = 0 :=
      eq_zero_of_quadForm_eq_zero_of_posDef S.hQ (by linarith)
    -- recombine over ℂ
    have hKc : complexify ((S.fullA * kGain S.fullC S.R Sinf)ᵀ)
        *ᵥ e = 0 := by
      refine complexify_mulVec_eq_zero _ _ ?_ ?_
      · rw [← herdef]; exact hKr
      · rw [← heidef]; exact hKi
    have hGc : complexify (S.fullGᵀ) *ᵥ e = 0 := by
      refine complexify_mulVec_eq_zero _ _ ?_ ?_
      · rw [← herdef]; exact hGr
      · rw [← heidef]; exact hGi
    -- `e` is a left quasi-eigenvector of `A` unexcited by `G`
    have hAt : complexify (S.fullAᵀ) *ᵥ e
        = μ • e + complexify (embM n₁ na nm) *ᵥ b := by
      have h1 : complexify ((errMap S.fullC S.R S.fullA Sinf)ᵀ) *ᵥ e
          = complexify (S.fullAᵀ) *ᵥ e
            - complexify (S.fullCᵀ)
                *ᵥ (complexify
                  ((S.fullA * kGain S.fullC S.R Sinf)ᵀ) *ᵥ e) := by
        rw [S.errMap_transpose_eq, complexify_sub, Matrix.sub_mulVec,
          complexify_mul, ← Matrix.mulVec_mulVec]
      rw [hKc, Matrix.mulVec_zero, sub_zero] at h1
      rw [← h1, hstep]
    -- the `e₁` part dies by stabilizability (PBH)
    have hv1 : complexify (S.A₁ᵀ)
        *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e)
        = μ • (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e) := by
      have h1 : (emb1 n₁ na nm)ᵀ * S.fullAᵀ
          = S.A₁ᵀ * (emb1 n₁ na nm)ᵀ := by
        have h := congrArg Matrix.transpose S.fullA_mul_emb1
        rwa [Matrix.transpose_mul, Matrix.transpose_mul] at h
      calc complexify (S.A₁ᵀ)
          *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e)
          = complexify ((emb1 n₁ na nm)ᵀ)
              *ᵥ (complexify (S.fullAᵀ) *ᵥ e) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
              ← complexify_mul, ← complexify_mul, h1]
      _ = μ • (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e)
            + complexify ((emb1 n₁ na nm)ᵀ * embM n₁ na nm) *ᵥ b := by
            rw [hAt, Matrix.mulVec_add, Matrix.mulVec_smul,
              Matrix.mulVec_mulVec, complexify_mul]
      _ = _ := by
            rw [emb1t_mul_embM, complexify_zero, Matrix.zero_mulVec,
              add_zero]
    have hG1 : complexify (S.G₁ᵀ)
        *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e) = 0 := by
      have h1 : S.fullGᵀ = S.G₁ᵀ * (emb1 n₁ na nm)ᵀ := by
        have h := congrArg Matrix.transpose S.fullG_eq
        rwa [Matrix.transpose_mul] at h
      rw [Matrix.mulVec_mulVec, ← complexify_mul, ← h1]
      exact hGc
    have hv10 : complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e = 0 :=
      S.hStab μ _ (le_of_eq heq) hv1 hG1
    -- the `a` part dies by antistability
    have hva : complexify (S.Aaᵀ)
        *ᵥ (complexify ((embA n₁ na nm)ᵀ) *ᵥ e)
        = μ • (complexify ((embA n₁ na nm)ᵀ) *ᵥ e) := by
      have h1 : (embA n₁ na nm)ᵀ * S.fullAᵀ
          = (ea2 na nm)ᵀ * S.A₁₂ᵀ * (emb1 n₁ na nm)ᵀ
            + S.Aaᵀ * (embA n₁ na nm)ᵀ := by
        have h := congrArg Matrix.transpose S.fullA_mul_embA
        simp only [Matrix.transpose_mul, Matrix.transpose_add] at h
        exact h
      have h2 : complexify ((embA n₁ na nm)ᵀ)
          *ᵥ (complexify (S.fullAᵀ) *ᵥ e)
          = complexify ((ea2 na nm)ᵀ * S.A₁₂ᵀ)
              *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e)
            + complexify (S.Aaᵀ)
              *ᵥ (complexify ((embA n₁ na nm)ᵀ) *ᵥ e) := by
        rw [Matrix.mulVec_mulVec, ← complexify_mul, h1]
        simp only [complexify_add, complexify_mul,
          Matrix.add_mulVec, Matrix.mulVec_mulVec]
      rw [hv10, Matrix.mulVec_zero, zero_add] at h2
      rw [← h2, hAt, Matrix.mulVec_add, Matrix.mulVec_smul,
        Matrix.mulVec_mulVec, ← complexify_mul, embAt_mul_embM,
        complexify_zero, Matrix.zero_mulVec, add_zero]
    have hva0 : complexify ((embA n₁ na nm)ᵀ) *ᵥ e = 0 := by
      by_contra hne
      have hspec : μ ∈ spectrum ℂ (complexify S.Aa) := by
        refine mem_spectrum_transpose_iff.mp ?_
        rw [← complexify_transpose]
        exact mem_spectrum_of_mulVec_eq_smul hne hva
      have h := S.hAnti μ hspec
      rw [← heq] at h
      exact lt_irrefl 1 h
    -- the `m` part was never there
    have hm0 : complexify ((embM n₁ na nm)ᵀ) *ᵥ e = 0 := by
      rw [hedef, Matrix.mulVec_mulVec, ← complexify_mul,
        embMt_mul_embS, complexify_zero, Matrix.zero_mulVec]
    -- so `e = 0`, hence `w = 0`: contradiction
    have he0 : e = 0 := by
      calc e = complexify
            (1 : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) *ᵥ e := by
            rw [complexify_one, Matrix.one_mulVec]
      _ = complexify (emb1 n₁ na nm * (emb1 n₁ na nm)ᵀ
            + embA n₁ na nm * (embA n₁ na nm)ᵀ
            + embM n₁ na nm * (embM n₁ na nm)ᵀ) *ᵥ e := by
            rw [partition3]
      _ = complexify (emb1 n₁ na nm)
            *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e)
          + complexify (embA n₁ na nm)
            *ᵥ (complexify ((embA n₁ na nm)ᵀ) *ᵥ e)
          + complexify (embM n₁ na nm)
            *ᵥ (complexify ((embM n₁ na nm)ᵀ) *ᵥ e) := by
            rw [complexify_add, complexify_add, Matrix.add_mulVec,
              Matrix.add_mulVec, complexify_mul, complexify_mul,
              complexify_mul, ← Matrix.mulVec_mulVec,
              ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = 0 := by
            rw [hv10, hva0, hm0, Matrix.mulVec_zero,
              Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero,
              add_zero]
    apply hwne
    have hw : w = complexify ((embS n₁ na nm)ᵀ) *ᵥ e := by
      rw [hedef, Matrix.mulVec_mulVec, ← complexify_mul,
        embSt_mul_embS, complexify_one, Matrix.one_mulVec]
    rw [hw, he0, Matrix.mulVec_zero]

end DareSystem

end Dare
end Estimation
