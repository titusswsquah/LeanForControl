import LeanForControl.Estimation.FIE
import LeanForControl.LinearSystems.StagedFacts
import Architect

/-!
# Finite-horizon structure: the reduced Riccati block (`lem:prelim`)

The `costogo` analysis runs on the block structure of the full-state value
matrices `𝐏_T = lq.ric T`: their `₁₁` block satisfies the *reduced* Riccati
recursion of the stabilizable subsystem `(A₁, G₁, C₁)` — the linchpin of
`lem:prelim`(3) — because the noise enters only the first block. This file
establishes that block extraction and instantiates the staged `fact:lqr`
for the reduced system under C1.
-/

namespace Estimation

open Matrix LinearSystems

variable {n₁ n₂ m p : ℕ}

namespace FIESystem

variable (Sys : FIESystem n₁ n₂ m p)

/-- The reduced tail LQ problem on the stabilizable block:
`e₁⁺ = A₁ e₁ - G₁ ω`, stage cost `‖C₁e₁‖²_{Ri} + ‖ω‖²_{Qi}`. -/
noncomputable def lqRed : LQSystem (Fin n₁) (Fin m) where
  A := Sys.A₁
  B := -Sys.G₁
  Qs := Sys.C₁ᵀ * Sys.Ri * Sys.C₁
  Ru := Sys.Qi
  hQs := by
    have h := Sys.hRi.posSemidef.mul_mul_conjTranspose_same Sys.C₁ᵀ
    rwa [show (Sys.C₁ᵀ)ᴴ = Sys.C₁ from by
      rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose]] at h
  hRu := Sys.hQi

@[simp]
lemma lq_A_eq : Sys.lq.A = Matrix.fromBlocks Sys.A₁ Sys.A₁₂ 0 Sys.A₂ := rfl

@[simp]
lemma lq_B_eq : Sys.lq.B = -Matrix.fromRows Sys.G₁ 0 := rfl

@[simp]
lemma lq_Ru_eq : Sys.lq.Ru = Sys.Qi := rfl

lemma lqRed_A_eq : Sys.lqRed.A = Sys.A₁ := rfl

lemma lqRed_B_eq : Sys.lqRed.B = -Sys.G₁ := rfl

/-- The full state penalty in block form. -/
lemma lq_Qs_fromBlocks :
    Sys.lq.Qs = Matrix.fromBlocks
      (Sys.C₁ᵀ * Sys.Ri * Sys.C₁) (Sys.C₁ᵀ * Sys.Ri * Sys.C₂)
      (Sys.C₂ᵀ * Sys.Ri * Sys.C₁) (Sys.C₂ᵀ * Sys.Ri * Sys.C₂) := by
  change Sys.fullCᵀ * Sys.Ri * Sys.fullC = _
  rw [fullC, Matrix.transpose_fromCols, Matrix.fromRows_mul,
    Matrix.fromRows_mul_fromCols]

/-- `Bᵀ P B` sees only the `₁₁` block. -/
lemma lq_BPB (P₁₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (P₁₂ : Matrix (Fin n₁) (Fin n₂) ℝ) (P₂₁ : Matrix (Fin n₂) (Fin n₁) ℝ)
    (P₂₂ : Matrix (Fin n₂) (Fin n₂) ℝ) :
    Sys.lq.Bᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.B
      = Sys.G₁ᵀ * P₁₁ * Sys.G₁ := by
  rw [lq_B_eq]
  simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromRows]
  simp

/-- The curvature of the full problem is the curvature of the reduced one. -/
lemma lq_gainΓ_fromBlocks (P₁₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (P₁₂ : Matrix (Fin n₁) (Fin n₂) ℝ) (P₂₁ : Matrix (Fin n₂) (Fin n₁) ℝ)
    (P₂₂ : Matrix (Fin n₂) (Fin n₂) ℝ) :
    Sys.lq.gainΓ (Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂)
      = Sys.lqRed.gainΓ P₁₁ := by
  unfold LQSystem.gainΓ
  rw [Sys.lq_BPB, lq_Ru_eq, lqRed_B_eq]
  have h : Sys.lqRed.Ru = Sys.Qi := rfl
  rw [h]
  simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]

/-- `Aᵀ P A` in block form. -/
lemma lq_APA (P₁₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (P₁₂ : Matrix (Fin n₁) (Fin n₂) ℝ) (P₂₁ : Matrix (Fin n₂) (Fin n₁) ℝ)
    (P₂₂ : Matrix (Fin n₂) (Fin n₂) ℝ) :
    Sys.lq.Aᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.A
      = Matrix.fromBlocks
        (Sys.A₁ᵀ * P₁₁ * Sys.A₁)
        (Sys.A₁ᵀ * P₁₁ * Sys.A₁₂ + Sys.A₁ᵀ * P₁₂ * Sys.A₂)
        (Sys.A₁₂ᵀ * P₁₁ * Sys.A₁ + Sys.A₂ᵀ * P₂₁ * Sys.A₁)
        (Sys.A₁₂ᵀ * P₁₁ * Sys.A₁₂ + Sys.A₁₂ᵀ * P₁₂ * Sys.A₂
          + Sys.A₂ᵀ * P₂₁ * Sys.A₁₂ + Sys.A₂ᵀ * P₂₂ * Sys.A₂) := by
  rw [lq_A_eq, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  congr 1
  · simp
  · simp [Matrix.add_mul, Matrix.mul_assoc]
  · simp [Matrix.add_mul, Matrix.mul_assoc]
  · simp [Matrix.add_mul, Matrix.mul_assoc]
    abel

/-- `Aᵀ P B` in block form. -/
lemma lq_APB (P₁₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (P₁₂ : Matrix (Fin n₁) (Fin n₂) ℝ) (P₂₁ : Matrix (Fin n₂) (Fin n₁) ℝ)
    (P₂₂ : Matrix (Fin n₂) (Fin n₂) ℝ) :
    Sys.lq.Aᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.B
      = -Matrix.fromRows (Sys.A₁ᵀ * P₁₁ * Sys.G₁)
          (Sys.A₁₂ᵀ * P₁₁ * Sys.G₁ + Sys.A₂ᵀ * P₂₁ * Sys.G₁) := by
  rw [lq_A_eq, lq_B_eq, Matrix.mul_neg, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_mul_fromRows]
  congr 2
  · simp [Matrix.mul_assoc]
  · simp [Matrix.add_mul, Matrix.mul_assoc]

/-- `Bᵀ P A` in block form. -/
lemma lq_BPA (P₁₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (P₁₂ : Matrix (Fin n₁) (Fin n₂) ℝ) (P₂₁ : Matrix (Fin n₂) (Fin n₁) ℝ)
    (P₂₂ : Matrix (Fin n₂) (Fin n₂) ℝ) :
    Sys.lq.Bᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.A
      = -Matrix.fromCols (Sys.G₁ᵀ * P₁₁ * Sys.A₁)
          (Sys.G₁ᵀ * P₁₁ * Sys.A₁₂ + Sys.G₁ᵀ * P₁₂ * Sys.A₂) := by
  rw [lq_A_eq, lq_B_eq]
  simp only [Matrix.transpose_neg, Matrix.neg_mul]
  rw [Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks,
    Matrix.fromCols_mul_fromBlocks]
  congr 2
  · simp [Matrix.mul_add, Matrix.mul_assoc]
  · simp [Matrix.mul_add, Matrix.mul_assoc]

/-- Block projections are additive. -/
lemma toBlocks₁₁_add (M N : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ) :
    (M + N).toBlocks₁₁ = M.toBlocks₁₁ + N.toBlocks₁₁ := rfl

lemma toBlocks₁₁_sub (M N : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ) :
    (M - N).toBlocks₁₁ = M.toBlocks₁₁ - N.toBlocks₁₁ := rfl

/-- **The `₁₁` block of the full Riccati step is the reduced Riccati step**
(the noise enters only the first block, so the `P`-recursion of
`lem:prelim`(1) closes on its own). -/
theorem step_fromBlocks_toBlocks₁₁ (P₁₁ : Matrix (Fin n₁) (Fin n₁) ℝ)
    (P₁₂ : Matrix (Fin n₁) (Fin n₂) ℝ) (P₂₁ : Matrix (Fin n₂) (Fin n₁) ℝ)
    (P₂₂ : Matrix (Fin n₂) (Fin n₂) ℝ) :
    (Sys.lq.step (Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂)).toBlocks₁₁
      = Sys.lqRed.step P₁₁ := by
  unfold LQSystem.step
  have hassoc : Sys.lq.Aᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.B *
        (Sys.lq.gainΓ (Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂))⁻¹ * Sys.lq.Bᵀ *
        Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.A
      = (Sys.lq.Aᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.B) *
        (Sys.lq.gainΓ (Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂))⁻¹ *
        (Sys.lq.Bᵀ * Matrix.fromBlocks P₁₁ P₁₂ P₂₁ P₂₂ * Sys.lq.A) := by
    simp only [Matrix.mul_assoc]
  rw [hassoc, Sys.lq_APB, Sys.lq_BPA, Sys.lq_gainΓ_fromBlocks, Sys.lq_APA,
    Sys.lq_Qs_fromBlocks]
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols]
  rw [toBlocks₁₁_sub, toBlocks₁₁_add, Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₁]
  show _ = Sys.lqRed.Qs + Sys.lqRed.Aᵀ * P₁₁ * Sys.lqRed.A - _
  have h1 : Sys.lqRed.Qs = Sys.C₁ᵀ * Sys.Ri * Sys.C₁ := rfl
  have h2 : Sys.lqRed.A = Sys.A₁ := rfl
  have h3 : Sys.lqRed.B = -Sys.G₁ := rfl
  rw [h1, h2, h3]
  simp only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  congr 1
  simp only [Matrix.mul_assoc]

/-- The `₁₁` block of the full Riccati step, for a general matrix. -/
theorem step_toBlocks₁₁ (P : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ) :
    (Sys.lq.step P).toBlocks₁₁ = Sys.lqRed.step P.toBlocks₁₁ := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks P]
  rw [Sys.step_fromBlocks_toBlocks₁₁]

/-- **`lem:prelim`(1), P-block**: the `₁₁` block of the full value iterates
is the reduced Riccati iteration. -/
theorem ric_toBlocks₁₁ : ∀ T, (Sys.lq.ric T).toBlocks₁₁ = Sys.lqRed.ric T
  | 0 => by
    show (0 : Matrix (Fin n₁ ⊕ Fin n₂) (Fin n₁ ⊕ Fin n₂) ℝ).toBlocks₁₁ = 0
    rfl
  | T + 1 => by
    rw [LQSystem.ric_succ, LQSystem.ric_succ, ← ric_toBlocks₁₁ T,
      Sys.step_toBlocks₁₁]


/-! ### Instantiating the staged LQR fact under C1 -/

/-- Complexification commutes with `star` on vectors (real matrices). -/
private lemma complexify_mulVec_star {k l : ℕ} (C : Matrix (Fin k) (Fin l) ℝ)
    (v : Fin l → ℂ) :
    complexify C *ᵥ star v = star (complexify C *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.star_apply, star_sum, star_mul',
    complexify_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_ofReal]

/-- Real part of a complexified real Hermitian form: splits into the real
quadratic forms of real and imaginary parts. -/
private lemma re_star_dotProduct_complexify {k : ℕ}
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
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
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

/-- Under C1, the reduced pair is `Qs`-detectable (the paper's
"`(A₁, C₁)` detectable" step of `lem:prelim`(3), with the kernel of the
penalty identified with the kernel of `C₁`). -/
lemma lqRed_qsDetectable (hC1 : Sys.C1) : Sys.lqRed.QsDetectable := by
  intro μ v hμ hAv hQv
  -- Step 1: `Qs v = 0` forces `C₁ v = 0` since `Ri ≻ 0`.
  have hC₁v : complexify Sys.C₁ *ᵥ v = 0 := by
    have hQs : Sys.lqRed.Qs = Sys.C₁ᵀ * Sys.Ri * Sys.C₁ := rfl
    rw [hQs] at hQv
    have hpair : star v ⬝ᵥ (complexify (Sys.C₁ᵀ * Sys.Ri * Sys.C₁) *ᵥ v) = 0 := by
      rw [hQv, dotProduct_zero]
    rw [complexify_mul, complexify_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, complexify_transpose, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose, complexify_mulVec_star] at hpair
    set w := complexify Sys.C₁ *ᵥ v with hw
    have hre : (star w ⬝ᵥ (complexify Sys.Ri *ᵥ w)).re = 0 := by
      rw [hpair]
      rfl
    rw [re_star_dotProduct_complexify] at hre
    have h1 : 0 ≤ quadForm Sys.Ri (fun i => (w i).re) :=
      Sys.hRi.posSemidef.quadForm_nonneg _
    have h2 : 0 ≤ quadForm Sys.Ri (fun i => (w i).im) :=
      Sys.hRi.posSemidef.quadForm_nonneg _
    have hre0 : (fun i => (w i).re) = 0 := by
      by_contra hne
      exact absurd (Sys.hRi.quadForm_pos hne) (by linarith)
    have him0 : (fun i => (w i).im) = 0 := by
      by_contra hne
      exact absurd (Sys.hRi.quadForm_pos hne) (by linarith)
    funext i
    have hri := congrFun hre0 i
    have hii := congrFun him0 i
    simp only [Pi.zero_apply] at hri hii
    exact Complex.ext hri hii
  -- Step 2: extend to an undetected unstable mode of the full system.
  set V : Fin n₁ ⊕ Fin n₂ → ℂ := Sum.elim v 0 with hV
  have hAV : complexify Sys.fullA *ᵥ V = μ • V := by
    have hfb : complexify Sys.fullA
        = Matrix.fromBlocks (complexify Sys.A₁) (complexify Sys.A₁₂)
            (complexify (0 : Matrix (Fin n₂) (Fin n₁) ℝ)) (complexify Sys.A₂) := by
      unfold fullA complexify
      exact Matrix.fromBlocks_map _ _ _ _ _
    rw [hfb, hV, Matrix.fromBlocks_mulVec]
    have hA₁red : Sys.lqRed.A = Sys.A₁ := rfl
    rw [hA₁red] at hAv
    funext i
    cases i with
    | inl i =>
      simp only [Sum.elim_inl, Sum.elim_inr]
      have := congrFun hAv i
      simpa using this
    | inr i =>
      simp [complexify_zero]
  have hCV : complexify Sys.fullC *ᵥ V = 0 := by
    have hfc : complexify Sys.fullC
        = Matrix.fromCols (complexify Sys.C₁) (complexify Sys.C₂) := by
      unfold fullC complexify
      ext i j
      cases j <;> rfl
    rw [hfc, hV, Matrix.fromCols_mulVec_sumElim]
    rw [hC₁v]
    simp
  have hV0 := hC1 μ V hμ hAV hCV
  funext i
  have := congrFun hV0 (Sum.inl i)
  simpa [hV] using this

/-- **`lem:prelim`(3), staged form**: under C1 the reduced Riccati iterates
converge to a stabilizing fixed point with Schur closed loop and convergent
gains. Consumes the staged `fact:lqr`. -/
theorem lqRed_lqr (hC1 : Sys.C1) :
    ∃ P : Matrix (Fin n₁) (Fin n₁) ℝ, P.PosSemidef ∧ Sys.lqRed.step P = P ∧
      IsSchurStable (Sys.lqRed.Acl P) ∧
      Filter.Tendsto (fun T => Sys.lqRed.ric T) Filter.atTop (nhds P) ∧
      Filter.Tendsto (fun T => Sys.lqRed.gainK (Sys.lqRed.ric T))
        Filter.atTop (nhds (Sys.lqRed.gainK P)) := by
  refine Sys.lqRed.lqr_convergence ?_ (Sys.lqRed_qsDetectable hC1)
  show IsStabilizable (complexify Sys.lqRed.A) (complexify Sys.lqRed.B)
  have h1 : Sys.lqRed.A = Sys.A₁ := rfl
  have h2 : Sys.lqRed.B = -Sys.G₁ := rfl
  rw [h1, h2, complexify_neg]
  exact Sys.hStab.neg


end FIESystem

end Estimation
