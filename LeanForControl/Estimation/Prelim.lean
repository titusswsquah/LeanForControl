import LeanForControl.Estimation.FIE
import LeanForControl.LinearSystems.StagedFacts
import LeanForControl.LinearSystems.UniformExpStability
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

open scoped Matrix.Norms.Operator

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


/-! ### The propagator bound (`lem:prelim`(4)) and uniform Riccati bounds -/

/-- A convergent sequence of matrices is bounded in norm. -/
lemma exists_norm_bound_of_tendsto {k l : ℕ}
    {f : ℕ → Matrix (Fin k) (Fin l) ℝ} {L : Matrix (Fin k) (Fin l) ℝ}
    (h : Filter.Tendsto f Filter.atTop (nhds L)) :
    ∃ c : ℝ, 0 < c ∧ ∀ T, ‖f T‖ ≤ c := by
  have h1 : ∀ᶠ T in Filter.atTop, dist (f T) L < 1 :=
    h (Metric.ball_mem_nhds L one_pos)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp h1
  refine ⟨‖L‖ + 1 + ∑ k' ∈ Finset.range K, ‖f k'‖ + 1, by positivity, fun T => ?_⟩
  have hsum : (0 : ℝ) ≤ ∑ k' ∈ Finset.range K, ‖f k'‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  rcases lt_or_ge T K with hT | hT
  · have h2 : ‖f T‖ ≤ ∑ k' ∈ Finset.range K, ‖f k'‖ :=
      Finset.single_le_sum (f := fun k' => ‖f k'‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_range.mpr hT)
    have h3 : (0 : ℝ) ≤ ‖L‖ := norm_nonneg _
    linarith
  · have h2 := hK T hT
    rw [dist_eq_norm] at h2
    have h3 : ‖f T‖ ≤ ‖f T - L‖ + ‖L‖ := by
      calc ‖f T‖ = ‖f T - L + L‖ := by rw [sub_add_cancel]
      _ ≤ ‖f T - L‖ + ‖L‖ := norm_add_le _ _
    linarith

/-- **`lem:prelim`(4)**: the reduced time-varying closed-loop propagators
decay geometrically, uniformly in start index and length. Consumes the
staged `fact:lqr` (via `lqRed_lqr`) and `fact:uniexp`. -/
theorem exists_propagator_bound (hC1 : Sys.C1) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ i l : ℕ,
      ‖revProd (fun r => Sys.lqRed.Acl (Sys.lqRed.ric r)) i l‖ ≤ c * ρ ^ l := by
  obtain ⟨P, hPpsd, hfix, hSchur, hric, hK⟩ := Sys.lqRed_lqr hC1
  have hAcl : Filter.Tendsto (fun r => Sys.lqRed.Acl (Sys.lqRed.ric r))
      Filter.atTop (nhds (Sys.lqRed.Acl P)) := by
    have h1 : Filter.Tendsto
        (fun r => Sys.lqRed.B * Sys.lqRed.gainK (Sys.lqRed.ric r))
        Filter.atTop (nhds (Sys.lqRed.B * Sys.lqRed.gainK P)) :=
      ((Continuous.matrix_mul continuous_const continuous_id).tendsto _).comp hK
    exact Filter.Tendsto.sub tendsto_const_nhds h1
  exact revProd_norm_le_of_tendsto _ _ hAcl hSchur

/-- Uniform bound on the reduced Riccati iterates, under C1. -/
theorem exists_ricRed_bound (hC1 : Sys.C1) :
    ∃ c : ℝ, 0 < c ∧ ∀ T, ‖Sys.lqRed.ric T‖ ≤ c := by
  obtain ⟨P, _, _, _, hric, _⟩ := Sys.lqRed_lqr hC1
  exact exists_norm_bound_of_tendsto hric


/-! ### The uniform value bound (`lem:unibounded`) and `eq:apriori` -/

/-- Block norms are dominated by the full norm. -/
lemma norm_blk₁_le (a : Fin n₁ ⊕ Fin n₂ → ℝ) : ‖blk₁ a‖ ≤ ‖a‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr fun i => ?_
  exact norm_le_pi_norm a (Sum.inl i)

lemma norm_blk₂_le (a : Fin n₁ ⊕ Fin n₂ → ℝ) : ‖blk₂ a‖ ≤ ‖a‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg a)).mpr fun i => ?_
  exact norm_le_pi_norm a (Sum.inr i)

/-- A trajectory started in the stabilizable block stays there and follows
the reduced dynamics. -/
lemma lq_traj_sumElim_zero (x₁ : Fin n₁ → ℝ) (ω : ℕ → Fin m → ℝ) : ∀ k,
    Sys.lq.traj (Sum.elim x₁ 0) ω k = Sum.elim (Sys.lqRed.traj x₁ ω k) 0
  | 0 => rfl
  | k + 1 => by
    rw [LQSystem.traj_succ, LQSystem.traj_succ,
      lq_traj_sumElim_zero x₁ ω k, lq_A_eq, lq_B_eq]
    rw [Matrix.fromBlocks_mulVec]
    funext i
    cases i with
    | inl i =>
      simp only [Sum.elim_inl, Pi.add_apply, Matrix.neg_mulVec,
        Matrix.fromRows_mulVec, Pi.neg_apply, Sum.elim_inr]
      have h1 : Sys.lqRed.A = Sys.A₁ := rfl
      have h2 : Sys.lqRed.B = -Sys.G₁ := rfl
      rw [h1, h2]
      simp [Matrix.neg_mulVec]
    | inr i =>
      simp [Matrix.neg_mulVec, Matrix.fromRows_mulVec]

/-- Cost of a stabilizable-block trajectory equals the reduced cost. -/
lemma lq_cost_sumElim_zero (x₁ : Fin n₁ → ℝ) (ω : ℕ → Fin m → ℝ) (T : ℕ) :
    Sys.lq.cost (Sum.elim x₁ 0) ω T = Sys.lqRed.cost x₁ ω T := by
  unfold LQSystem.cost
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Sys.lq_traj_sumElim_zero]
  congr 1
  rw [Sys.quadForm_Qs]
  have h1 : Sys.fullC *ᵥ Sum.elim (Sys.lqRed.traj x₁ ω k) 0
      = Sys.C₁ *ᵥ Sys.lqRed.traj x₁ ω k := by
    rw [fullC, Matrix.fromCols_mulVec_sumElim]
    simp
  rw [h1]
  have h2 : quadForm Sys.lqRed.Qs (Sys.lqRed.traj x₁ ω k)
      = quadForm Sys.Ri (Sys.C₁ *ᵥ Sys.lqRed.traj x₁ ω k) := by
    have h3 : Sys.lqRed.Qs = Sys.C₁ᵀ * Sys.Ri * Sys.C₁ := rfl
    rw [h3, ← quadForm_mulVec]
  rw [h2]

/-- A stabilizing state-feedback gain for the reduced pair `(A₁, G₁)`
(from the staged `detect_inj` by duality). -/
theorem exists_stabilizing_gain :
    ∃ Kt : Matrix (Fin m) (Fin n₁) ℝ,
      IsSchurStable (Sys.A₁ - Sys.G₁ * Kt) := by
  have hdet : IsDetectable (complexify Sys.A₁ᵀ) (complexify Sys.G₁ᵀ) := by
    rw [complexify_transpose, complexify_transpose]
    exact Sys.hStab
  obtain ⟨L, hL⟩ := detect_inj Sys.A₁ᵀ Sys.G₁ᵀ hdet
  refine ⟨Lᵀ, ?_⟩
  have h1 : (Sys.A₁ᵀ - L * Sys.G₁ᵀ)ᵀ = Sys.A₁ - Sys.G₁ * Lᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  have h2 := hL.transpose
  rwa [h1] at h2

/-- **Uniform value bound** (`lem:unibounded`): under C1 and C2 the optimal
value is bounded by a fixed multiple of `‖a‖²`, uniformly in the horizon. -/
theorem exists_value_bound (hC1 : Sys.C1) (hC2 : Sys.C2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ),
      Sys.value a T ≤ c * ‖a‖ ^ 2 := by
  obtain ⟨P, hPpsd, hfix, hSchur, hric, hK⟩ := Sys.lqRed_lqr hC1
  obtain ⟨c₂, hc₂, hqb₂⟩ := exists_quadForm_le (symmPinv Sys.hSig₂.1)
  obtain ⟨cP, hcP, hqbP⟩ := exists_quadForm_le P
  refine ⟨c₂ + cP, by positivity, fun a T => ?_⟩
  -- the candidate: start at `(a₁, 0)` and roll out the frozen reduced gain
  set e₀ : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim (blk₁ a) 0 with he₀
  set ω : ℕ → Fin m → ℝ := fun j =>
    -(Sys.lqRed.gainK P *ᵥ (Sys.lqRed.Acl P ^ j *ᵥ blk₁ a)) with hω
  have hfeas : Sys.Feasible a e₀ := by
    constructor
    · refine ⟨0, ?_⟩
      rw [he₀]
      funext i
      simp
    · refine ⟨Sys.Sig₂⁻¹ *ᵥ (-(blk₂ a)), ?_⟩
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hC2.isUnit), Matrix.one_mulVec,
        he₀]
      funext i
      simp
  have hval := Sys.value_le_fieCost hfeas ω T
  -- the candidate's cost
  have hprior : Sys.priorPenalty a e₀ = quadForm (symmPinv Sys.hSig₂.1) (blk₂ a) := by
    unfold priorPenalty
    have h1 : blk₁ (e₀ - a) = 0 := by
      rw [he₀]
      funext i
      simp
    have h2 : blk₂ (e₀ - a) = -(blk₂ a) := by
      rw [he₀]
      funext i
      simp
    rw [h1, h2]
    have h3 : quadForm (symmPinv Sys.hSig₂.1) (-(blk₂ a))
        = quadForm (symmPinv Sys.hSig₂.1) (blk₂ a) := quadForm_neg _ _
    rw [h3, quadForm_zero]
    ring
  have hcost : Sys.lq.cost e₀ ω T ≤ quadForm P (blk₁ a) := by
    rw [he₀, Sys.lq_cost_sumElim_zero, hω,
      Sys.lqRed.cost_fixedGain hPpsd hfix]
    have h1 : 0 ≤ quadForm P (Sys.lqRed.Acl P ^ T *ᵥ blk₁ a) :=
      hPpsd.quadForm_nonneg _
    linarith
  have h4 : quadForm (symmPinv Sys.hSig₂.1) (blk₂ a) ≤ c₂ * ‖a‖ ^ 2 := by
    refine le_trans (hqb₂ (blk₂ a)) ?_
    have h5 := norm_blk₂_le a
    have h6 : ‖blk₂ a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖blk₂ a‖ := norm_nonneg _
      gcongr
    exact mul_le_mul_of_nonneg_left h6 hc₂.le
  have h7 : quadForm P (blk₁ a) ≤ cP * ‖a‖ ^ 2 := by
    refine le_trans (hqbP (blk₁ a)) ?_
    have h5 := norm_blk₁_le a
    have h6 : ‖blk₁ a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖blk₁ a‖ := norm_nonneg _
      gcongr
    exact mul_le_mul_of_nonneg_left h6 hcP.le
  unfold fieCost at hval
  rw [hprior] at hval
  linarith

/-- **`eq:apriori`**: the optimal initial deviation of the stabilizable
block is linearly bounded by the prior mismatch, uniformly in the horizon. -/
theorem exists_optInit_blk₁_bound (hC1 : Sys.C1) (hC2 : Sys.C2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ),
      ‖blk₁ (Sys.optInit a T - a)‖ ≤ c * ‖a‖ := by
  obtain ⟨cv, hcv, hval⟩ := Sys.exists_value_bound hC1 hC2
  obtain ⟨Cr, hCr, hrb⟩ := Sys.hSig₁.exists_sq_norm_mulVec_le
  refine ⟨Real.sqrt (Cr * cv), Real.sqrt_pos.mpr (by positivity), fun a T => ?_⟩
  obtain ⟨z, hz⟩ := (Sys.optInit_feasible a T).1
  -- the prior term of the value dominates the Σ₁-energy of the deviation
  have h1 : quadForm (symmPinv Sys.hSig₁.1) (blk₁ (Sys.optInit a T - a))
      ≤ Sys.value a T := by
    have h2 : 0 ≤ quadForm (symmPinv Sys.hSig₂.1) (blk₂ (Sys.optInit a T - a)) :=
      Sys.hSig₂.symmPinv.quadForm_nonneg _
    have h3 : 0 ≤ quadForm (Sys.lq.ric T) (Sys.optInit a T) :=
      (Sys.lq.ric_posSemidef T).quadForm_nonneg _
    unfold value outerObj priorPenalty
    linarith
  have h4 : ‖blk₁ (Sys.optInit a T - a)‖ ^ 2 ≤ Cr * cv * ‖a‖ ^ 2 := by
    rw [hz] at h1 ⊢
    rw [quadForm_symmPinv_mulVec Sys.hSig₁] at h1
    calc ‖Sys.Sig₁ *ᵥ z‖ ^ 2 ≤ Cr * quadForm Sys.Sig₁ z := hrb z
    _ ≤ Cr * Sys.value a T := mul_le_mul_of_nonneg_left h1 hCr.le
    _ ≤ Cr * (cv * ‖a‖ ^ 2) := mul_le_mul_of_nonneg_left (hval a T) hCr.le
    _ = Cr * cv * ‖a‖ ^ 2 := by ring
  have h5 : ‖blk₁ (Sys.optInit a T - a)‖ ≤ Real.sqrt (Cr * cv * ‖a‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (blk₁ (Sys.optInit a T - a)))]
    exact Real.sqrt_le_sqrt h4
  calc ‖blk₁ (Sys.optInit a T - a)‖ ≤ Real.sqrt (Cr * cv * ‖a‖ ^ 2) := h5
  _ = Real.sqrt (Cr * cv) * ‖a‖ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg a)]



/-- **Uniform value bound under C2 alone** (`lem:unibounded`, corrected
hypothesis bookkeeping): detectability is not needed — any stabilizing
feedback for the stabilizable block bounds the candidate rollout cost
through the Lyapunov-free geometric estimate
`LQSystem.exists_cost_feedback_bound`. -/
theorem exists_value_bound_C2 (hC2 : Sys.C2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : Fin n₁ ⊕ Fin n₂ → ℝ) (T : ℕ),
      Sys.value a T ≤ c * ‖a‖ ^ 2 := by
  obtain ⟨Kt, hKt⟩ := Sys.exists_stabilizing_gain
  obtain ⟨cF, ρ, hcF, hρ0, hρ1, hpow⟩ := hKt.exists_pow_norm_le
  have hloop : Sys.lqRed.A + Sys.lqRed.B * Kt = Sys.A₁ - Sys.G₁ * Kt := by
    show Sys.A₁ + -Sys.G₁ * Kt = Sys.A₁ - Sys.G₁ * Kt
    rw [Matrix.neg_mul, sub_eq_add_neg]
  obtain ⟨cb, hcb, hbcost⟩ := Sys.lqRed.exists_cost_feedback_bound Kt
    hcF hρ0 hρ1 (fun k => by rw [hloop]; exact hpow k)
  obtain ⟨c₂, hc₂, hqb₂⟩ := exists_quadForm_le (symmPinv Sys.hSig₂.1)
  refine ⟨c₂ + cb, by positivity, fun a T => ?_⟩
  set e₀ : Fin n₁ ⊕ Fin n₂ → ℝ := Sum.elim (blk₁ a) 0 with he₀
  set ω : ℕ → Fin m → ℝ := fun j =>
    Kt *ᵥ ((Sys.lqRed.A + Sys.lqRed.B * Kt) ^ j *ᵥ blk₁ a) with hω
  have hfeas : Sys.Feasible a e₀ := by
    constructor
    · refine ⟨0, ?_⟩
      rw [he₀]
      funext i
      simp
    · refine ⟨Sys.Sig₂⁻¹ *ᵥ (-(blk₂ a)), ?_⟩
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp hC2.isUnit), Matrix.one_mulVec,
        he₀]
      funext i
      simp
  have hval := Sys.value_le_fieCost hfeas ω T
  have hprior : Sys.priorPenalty a e₀
      = quadForm (symmPinv Sys.hSig₂.1) (blk₂ a) := by
    unfold priorPenalty
    have h1 : blk₁ (e₀ - a) = 0 := by
      rw [he₀]
      funext i
      simp
    have h2 : blk₂ (e₀ - a) = -(blk₂ a) := by
      rw [he₀]
      funext i
      simp
    rw [h1, h2]
    have h3 : quadForm (symmPinv Sys.hSig₂.1) (-(blk₂ a))
        = quadForm (symmPinv Sys.hSig₂.1) (blk₂ a) := quadForm_neg _ _
    rw [h3, quadForm_zero]
    ring
  have hcost : Sys.lq.cost e₀ ω T ≤ cb * ‖blk₁ a‖ ^ 2 := by
    rw [he₀, Sys.lq_cost_sumElim_zero, hω]
    exact hbcost (blk₁ a) T
  have h4 : quadForm (symmPinv Sys.hSig₂.1) (blk₂ a) ≤ c₂ * ‖a‖ ^ 2 := by
    refine le_trans (hqb₂ (blk₂ a)) ?_
    have h5 := norm_blk₂_le a
    have h6 : ‖blk₂ a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖blk₂ a‖ := norm_nonneg _
      gcongr
    exact mul_le_mul_of_nonneg_left h6 hc₂.le
  have h7 : cb * ‖blk₁ a‖ ^ 2 ≤ cb * ‖a‖ ^ 2 := by
    have h5 := norm_blk₁_le a
    have h6 : ‖blk₁ a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖blk₁ a‖ := norm_nonneg _
      gcongr
    exact mul_le_mul_of_nonneg_left h6 hcb.le
  unfold fieCost at hval
  rw [hprior] at hval
  linarith


end FIESystem

end Estimation
