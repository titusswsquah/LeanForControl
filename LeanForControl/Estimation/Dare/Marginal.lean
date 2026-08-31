import LeanForControl.Estimation.Dare.Structure
import LeanForControl.Estimation.Dare.Bounded
import LeanForControl.LinearSystems.SpectralGrowth
import LeanForControl.LinearSystems.StagedFacts
import Architect

/-!
# Marginal extinction (`lem:structure-marg`, `eq:marg-extinct`)

The strong solution vanishes on the marginal columns: `Σ∞|·ₘ = 0`.
Route (Lean-first; both halves simplify the deck's prose):

1. The marginal-corner Stein relation `D = P − Am⁻¹P Am⁻ᵀ` telescopes,
   so the `D`-energy along every backward orbit is summable; the
   **orbit-kill lemma** (PSD Cauchy–Schwarz floor + `fact:no-decay`,
   no spectral factorization) forces `D = 0`.
2. `D = BₘᵀS⁻¹Bₘ` with `S⁻¹ ≻ 0` forces `Bₘ = CΣ∞|·ₘ = 0`; the
   marginal columns `Z = Σ∞·E` then satisfy the intertwining
   `(A−LC)Z = Z(Amᵀ)⁻¹` for the detectability injection `L`
   (`fact:detect-inj`), so `ZBᵏ = (A−LC)ᵏZ → 0` geometrically while
   `B` has unit-modulus spectrum — `fact:no-decay` on the rows kills
   `Z` (no unobservable-subspace decomposition needed).
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

/-! ### Generic helpers -/

/-- A PSD matrix with all quadratic forms zero is zero. -/
lemma _root_.Matrix.PosSemidef.eq_zero_of_forall_quadForm_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {D : Matrix ι ι ℝ}
    (hD : D.PosSemidef) (h : ∀ x, quadForm D x = 0) : D = 0 := by
  ext i j
  have hz := hD.mulVec_eq_zero_of_quadForm_eq_zero (h (Pi.single j (1 : ℝ)))
  have h1 := congrFun hz i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
    Finset.sum_ite_eq'] using h1

/-- A congruence by a positive-definite core vanishes only trivially:
`MᵀWM = 0`, `W ≻ 0` force `M = 0`. -/
lemma eq_zero_of_transpose_mul_mul_eq_zero
    {κ' ιm : Type*} [Fintype κ'] [DecidableEq κ'] [Fintype ιm]
    [DecidableEq ιm]
    {W : Matrix κ' κ' ℝ} (hW : W.PosDef) {M : Matrix κ' ιm ℝ}
    (h : Mᵀ * W * M = 0) : M = 0 := by
  have hcol : ∀ j, M *ᵥ Pi.single j (1 : ℝ) = 0 := by
    intro j
    by_contra hne
    have h1 := hW.quadForm_pos hne
    have h2 : quadForm W (M *ᵥ Pi.single j (1 : ℝ))
        = quadForm (Mᵀ * W * M) (Pi.single j (1 : ℝ)) :=
      quadForm_mulVec W M (Pi.single j (1 : ℝ))
    rw [h, quadForm_zero_matrix] at h2
    rw [h2] at h1
    exact lt_irrefl 0 h1
  ext i j
  have h1 := congrFun (hcol j) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
    Finset.sum_ite_eq'] using h1

/-! ### The orbit-kill lemma -/

variable {nκ : ℕ}

/-- **The orbit-kill lemma**: a PSD `D` whose energy along every
`B`-orbit has partial sums dominated by a fixed quadratic form
vanishes, provided `Bᵀ` has no spectrum inside the open unit disk.
(The deck's trace/spectral-factorization step, replaced by a PSD
Cauchy–Schwarz floor.) -/
lemma posSemidef_eq_zero_of_orbit_summable
    {B D P : Matrix (Fin nκ) (Fin nκ) ℝ} (hD : D.PosSemidef)
    (hB : ∀ μ ∈ spectrum ℂ (complexify Bᵀ), 1 ≤ ‖μ‖)
    (hsum : ∀ (u : Fin nκ → ℝ) (N : ℕ),
      ∑ k ∈ Finset.range N, quadForm D (B ^ k *ᵥ u) ≤ quadForm P u) :
    D = 0 := by
  by_contra hne
  have hx : ∃ x, 0 < quadForm D x := by
    by_contra hall
    push_neg at hall
    exact hne (hD.eq_zero_of_forall_quadForm_eq_zero fun x =>
      le_antisymm (hall x) (hD.quadForm_nonneg x))
  obtain ⟨x, hx⟩ := hx
  have hvne : D *ᵥ x ≠ 0 := by
    intro h0
    rw [quadForm, h0, dotProduct_zero] at hx
    exact lt_irrefl 0 hx
  -- Cauchy–Schwarz floor: summable pairings against Dx
  have hsq : ∀ u : Fin nκ → ℝ,
      Summable (fun k => ((D *ᵥ x) ⬝ᵥ (B ^ k *ᵥ u)) ^ 2) := by
    intro u
    refine summable_of_sum_range_le (c := quadForm D x * quadForm P u)
      (fun k => sq_nonneg _) fun N => ?_
    calc ∑ k ∈ Finset.range N, ((D *ᵥ x) ⬝ᵥ (B ^ k *ᵥ u)) ^ 2
        ≤ ∑ k ∈ Finset.range N,
            quadForm D (B ^ k *ᵥ u) * quadForm D x := by
          refine Finset.sum_le_sum fun k _ => ?_
          have h1 := sq_dotProduct_mulVec_le hD x (B ^ k *ᵥ u)
          rwa [show (D *ᵥ x) ⬝ᵥ (B ^ k *ᵥ u)
              = (B ^ k *ᵥ u) ⬝ᵥ (D *ᵥ x) from dotProduct_comm _ _]
    _ = quadForm D x * ∑ k ∈ Finset.range N,
          quadForm D (B ^ k *ᵥ u) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    _ ≤ quadForm D x * quadForm P u :=
          mul_le_mul_of_nonneg_left (hsum u N) hx.le
  -- pairings tend to zero
  have hto : ∀ u : Fin nκ → ℝ,
      Tendsto (fun k => (D *ᵥ x) ⬝ᵥ (B ^ k *ᵥ u)) atTop (nhds 0) := by
    intro u
    have h1 := (hsq u).tendsto_atTop_zero
    have h2 : Tendsto (fun k => |(D *ᵥ x) ⬝ᵥ (B ^ k *ᵥ u)|)
        atTop (nhds 0) := by
      have h3 : (fun k => |(D *ᵥ x) ⬝ᵥ (B ^ k *ᵥ u)|)
          = fun k => Real.sqrt (((D *ᵥ x) ⬝ᵥ (B ^ k *ᵥ u)) ^ 2) := by
        funext k
        rw [Real.sqrt_sq_eq_abs]
      rw [h3]
      have h4 := (Real.continuous_sqrt.tendsto 0).comp h1
      simpa [Real.sqrt_zero, Function.comp] using h4
    exact squeeze_zero_norm (fun k => le_of_eq (Real.norm_eq_abs _)) h2
  -- the transposed orbit of Dx tends to zero, componentwise
  have hcomp : Tendsto (fun k => Bᵀ ^ k *ᵥ (D *ᵥ x)) atTop
      (nhds (0 : Fin nκ → ℝ)) := by
    rw [tendsto_pi_nhds]
    intro i
    have h1 := hto (Pi.single i 1)
    have h2 : (fun k => (Bᵀ ^ k *ᵥ (D *ᵥ x)) i)
        = fun k => (D *ᵥ x) ⬝ᵥ (B ^ k *ᵥ Pi.single i 1) := by
      funext k
      rw [dotProduct_mulVec_eq, Matrix.transpose_pow]
      simp [dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
    rw [h2]
    simpa using h1
  exact hvne (no_decay Bᵀ hB hcomp)

/-! ### The marginal frame plumbing -/

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The inclusion of the marginal coordinates,
`E : ℝ^{n_m} → e₁ ⊕ (eₐ ⊕ eₘ)`. -/
def embM (n₁ na nm : ℕ) : Matrix (ix n₁ na nm) (Fin nm) ℝ :=
  Matrix.fromRows 0 (Matrix.fromRows 0 1)

/-- The intertwining `AᵀE = EAₘᵀ`. -/
lemma fullA_transpose_mul_embM :
    S.fullAᵀ * embM n₁ na nm = embM n₁ na nm * S.Amᵀ := by
  ext i j
  cases i with
  | inl i₁ =>
    simp [embM, fullA, A₂, Matrix.mul_apply, Matrix.transpose_apply,
      Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr]
  | inr i₂ =>
    cases i₂ with
    | inl ia =>
      simp [embM, fullA, A₂, Matrix.mul_apply, Matrix.transpose_apply,
        Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
        Matrix.fromRows_apply_inr]
    | inr im =>
      simp [embM, fullA, A₂, Matrix.mul_apply, Matrix.transpose_apply,
        Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
        Matrix.fromRows_apply_inr, Matrix.one_apply]

/-- No noise reaches the marginal coordinates. -/
lemma embM_transpose_mul_fullG :
    (embM n₁ na nm)ᵀ * S.fullG = 0 := by
  ext i j
  simp [embM, fullG, Matrix.mul_apply, Matrix.transpose_apply,
    Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr]

lemma embM_Qw_corner :
    (embM n₁ na nm)ᵀ * S.Qw * embM n₁ na nm = 0 := by
  unfold Qw
  calc (embM n₁ na nm)ᵀ * (S.fullG * S.Q * S.fullGᵀ) * embM n₁ na nm
      = ((embM n₁ na nm)ᵀ * S.fullG) * S.Q
          * (S.fullGᵀ * embM n₁ na nm) := by
        simp only [Matrix.mul_assoc]
  _ = 0 := by
      rw [S.embM_transpose_mul_fullG]
      have h : S.fullGᵀ * embM n₁ na nm
          = ((embM n₁ na nm)ᵀ * S.fullG)ᵀ := by
        rw [Matrix.transpose_mul, Matrix.transpose_transpose]
      rw [h, S.embM_transpose_mul_fullG]
      simp

/-- The marginal block is nonsingular. -/
lemma isUnit_Am_det : IsUnit S.Am.det := by
  rw [isUnit_iff_ne_zero]
  refine LinearSystems.det_ne_zero_of_zero_notMem_spectrum fun h0 => ?_
  have := S.hMarg 0 h0
  rw [norm_zero] at this
  norm_num at this

/-- The inverse marginal dynamics stay on the unit circle:
`|λ(Aₘ⁻¹)| = 1 ≥ 1`. -/
lemma Am_inv_spectrum :
    ∀ μ ∈ spectrum ℂ (complexify S.Am⁻¹), 1 ≤ ‖μ‖ := by
  intro μ hμ
  have hspec : μ ∈ spectrum ℂ
      (Matrix.toLin' (complexify S.Am⁻¹)) := by
    rw [Matrix.spectrum_toLin']
    exact hμ
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
    hspec).exists_hasEigenvector
  have hAv : complexify S.Am⁻¹ *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  have hvne : v ≠ 0 := hv.2
  have hinv : complexify S.Am * complexify S.Am⁻¹ = 1 := by
    rw [← complexify_mul, Matrix.mul_nonsing_inv _ S.isUnit_Am_det,
      complexify_one]
  rcases eq_or_ne μ 0 with h0 | hne
  · exfalso
    apply hvne
    have h1 : complexify S.Am⁻¹ *ᵥ v = 0 := by
      rw [hAv, h0, zero_smul]
    have h2 := congrArg (fun w => complexify S.Am *ᵥ w) h1
    simpa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec,
      Matrix.mulVec_zero] using h2
  · have h1 : complexify S.Am *ᵥ v = μ⁻¹ • v := by
      have h2 := congrArg (fun w => complexify S.Am *ᵥ w) hAv
      simp only [Matrix.mulVec_smul] at h2
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at h2
      have h3 := congrArg (fun w => μ⁻¹ • w) h2
      simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at h3
      exact h3.symm
    have h4 := S.hMarg μ⁻¹ (mem_spectrum_of_mulVec_eq_smul hvne h1)
    rw [norm_inv, inv_eq_one] at h4
    rw [h4]

/-! ### Extinction (`eq:marg-extinct`) -/

variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-- The marginal-corner fixed identity `P = Aₘ·U(Σ∞)|ₘₘ·Aₘᵀ`. -/
lemma strong_margCorner_fixed (hS : S.IsStrongSolution Sinf) :
    (embM n₁ na nm)ᵀ * Sinf * embM n₁ na nm
      = S.Am * ((embM n₁ na nm)ᵀ
          * updM S.fullC S.R Sinf * embM n₁ na nm) * S.Amᵀ := by
  conv_lhs => rw [← hS.fixed]
  exact dareStep_corner_eq S.fullA_transpose_mul_embM S.embM_Qw_corner

/-- **`eq:marg-extinct`, first half**: the marginal correction of the
strong solution vanishes, `D := (Σ∞ − U(Σ∞))|ₘₘ = 0` — by the Stein
telescope and the orbit-kill lemma. -/
theorem strong_marg_correction_eq_zero (hS : S.IsStrongSolution Sinf) :
    (embM n₁ na nm)ᵀ * (Sinf - updM S.fullC S.R Sinf)
      * embM n₁ na nm = 0 := by
  set P := (embM n₁ na nm)ᵀ * Sinf * embM n₁ na nm with hP
  set U2 := (embM n₁ na nm)ᵀ * updM S.fullC S.R Sinf * embM n₁ na nm
    with hU2
  set D := (embM n₁ na nm)ᵀ * (Sinf - updM S.fullC S.R Sinf)
    * embM n₁ na nm with hD
  have hDsplit : D = P - U2 := by
    rw [hD, hP, hU2, Matrix.mul_sub, Matrix.sub_mul]
  -- U2 = Am⁻¹ P (Am⁻¹)ᵀ from the corner fixed identity
  have hAmInv : S.Am⁻¹ * S.Am = 1 :=
    Matrix.nonsing_inv_mul _ S.isUnit_Am_det
  have hAmInv' : S.Amᵀ * (S.Amᵀ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by
      rw [Matrix.det_transpose]; exact S.isUnit_Am_det)
  have hU2eq : U2 = S.Am⁻¹ * P * (S.Am⁻¹)ᵀ := by
    have h1 := S.strong_margCorner_fixed hS
    rw [← hP, ← hU2] at h1
    calc U2 = (S.Am⁻¹ * S.Am) * U2 * (S.Amᵀ * (S.Amᵀ)⁻¹) := by
          rw [hAmInv, hAmInv', Matrix.one_mul, Matrix.mul_one]
    _ = S.Am⁻¹ * (S.Am * U2 * S.Amᵀ) * (S.Amᵀ)⁻¹ := by
          simp only [Matrix.mul_assoc]
    _ = S.Am⁻¹ * P * (S.Am⁻¹)ᵀ := by
          rw [← h1, Matrix.transpose_nonsing_inv]
  -- per-step telescope in quadratic form, with B := (Amᵀ)⁻¹
  set B := (S.Amᵀ)⁻¹ with hB
  have hBt : Bᵀ = S.Am⁻¹ := by
    rw [hB, Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
  have hstep : ∀ w : Fin nm → ℝ,
      quadForm D w = quadForm P w - quadForm P (B *ᵥ w) := by
    intro w
    have h1 : quadForm P (B *ᵥ w) = quadForm (Bᵀ * P * B) w :=
      quadForm_mulVec P B w
    have h2 : Bᵀ * P * B = S.Am⁻¹ * P * (S.Am⁻¹)ᵀ := by
      rw [hBt, hB, Matrix.transpose_nonsing_inv]
    rw [hDsplit, quadForm_sub_matrix, hU2eq, h1, h2]
  -- telescoped partial sums are dominated by quadForm P
  have hPpsd : P.PosSemidef := by
    rw [hP]
    have h := hS.posSemidef.conjTranspose_mul_mul_same (embM n₁ na nm)
    rwa [show (embM n₁ na nm)ᴴ = (embM n₁ na nm)ᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h
  have htele : ∀ (u : Fin nm → ℝ) (N : ℕ),
      ∑ k ∈ Finset.range N, quadForm D (B ^ k *ᵥ u)
        = quadForm P u - quadForm P (B ^ N *ᵥ u) := by
    intro u N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, ih, hstep (B ^ N *ᵥ u)]
      have h1 : B *ᵥ (B ^ N *ᵥ u) = B ^ (N + 1) *ᵥ u := by
        rw [Matrix.mulVec_mulVec, ← pow_succ']
      rw [h1]
      ring
  have hsum : ∀ (u : Fin nm → ℝ) (N : ℕ),
      ∑ k ∈ Finset.range N, quadForm D (B ^ k *ᵥ u) ≤ quadForm P u := by
    intro u N
    rw [htele u N]
    have := hPpsd.quadForm_nonneg (B ^ N *ᵥ u)
    linarith
  -- D is PSD (corner of the contraction), and the kill lemma fires
  have hDpsd : D.PosSemidef := by
    rw [hD]
    have h := (sub_updM_posSemidef (C := S.fullC) S.hR
      hS.posSemidef).conjTranspose_mul_mul_same (embM n₁ na nm)
    rwa [show (embM n₁ na nm)ᴴ = (embM n₁ na nm)ᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h
  have hBspec : ∀ μ ∈ spectrum ℂ (complexify Bᵀ), 1 ≤ ‖μ‖ := by
    rw [hBt]
    exact S.Am_inv_spectrum
  exact posSemidef_eq_zero_of_orbit_summable hDpsd hBspec hsum

/-- The marginal columns are invisible to the output:
`C·Σ∞·E = 0`. -/
theorem strong_marg_output_eq_zero (hS : S.IsStrongSolution Sinf) :
    S.fullC * Sinf * embM n₁ na nm = 0 := by
  have hD := S.strong_marg_correction_eq_zero hS
  have hcorr : Sinf - updM S.fullC S.R Sinf
      = Sinf * S.fullCᵀ * (innov S.fullC S.R Sinf)⁻¹
        * (S.fullC * Sinf) := sub_updM_eq
  have hform : (embM n₁ na nm)ᵀ * (Sinf - updM S.fullC S.R Sinf)
        * embM n₁ na nm
      = (S.fullC * Sinf * embM n₁ na nm)ᵀ
        * (innov S.fullC S.R Sinf)⁻¹
        * (S.fullC * Sinf * embM n₁ na nm) := by
    rw [hcorr]
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      hS.posSemidef.1.transpose_eq_self]
    simp only [Matrix.mul_assoc]
  rw [hform] at hD
  exact eq_zero_of_transpose_mul_mul_eq_zero
    (innov_posDef S.hR hS.posSemidef).inv hD

/-- **`eq:marg-extinct` (extinction)**: the strong solution vanishes
on the marginal columns, `Σ∞·E = 0` — by the output-injection
intertwining `(A−LC)ᵏZ = Z(Aₘᵀ)⁻ᵏ` (Schur decay left, unit-circle
`fact:no-decay` right). -/
theorem strong_marg_extinct (hC1 : S.C1) (hS : S.IsStrongSolution Sinf) :
    Sinf * embM n₁ na nm = 0 := by
  set Z := Sinf * embM n₁ na nm with hZ
  clear_value Z
  have hBm := S.strong_marg_output_eq_zero hS
  have hCZ : S.fullC * Z = 0 := by
    rw [hZ, ← Matrix.mul_assoc]
    exact hBm
  -- the marginal-column fixed point Z = A·Z·Amᵀ
  have hcorrE : (Sinf - updM S.fullC S.R Sinf) * embM n₁ na nm = 0 := by
    rw [sub_updM_eq]
    calc Sinf * S.fullCᵀ * (innov S.fullC S.R Sinf)⁻¹
          * (S.fullC * Sinf) * embM n₁ na nm
        = Sinf * S.fullCᵀ * (innov S.fullC S.R Sinf)⁻¹
          * (S.fullC * Sinf * embM n₁ na nm) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hBm, Matrix.mul_zero]
  have hUE : updM S.fullC S.R Sinf * embM n₁ na nm = Z := by
    have h1 : Sinf * embM n₁ na nm
        - updM S.fullC S.R Sinf * embM n₁ na nm = 0 := by
      rw [← Matrix.sub_mul]
      exact hcorrE
    rw [hZ]
    linear_combination (norm := abel) -h1
  have hQwE : S.Qw * embM n₁ na nm = 0 := by
    unfold Qw
    calc S.fullG * S.Q * S.fullGᵀ * embM n₁ na nm
        = S.fullG * S.Q * (S.fullGᵀ * embM n₁ na nm) := by
          simp only [Matrix.mul_assoc]
    _ = 0 := by
        have h : S.fullGᵀ * embM n₁ na nm
            = ((embM n₁ na nm)ᵀ * S.fullG)ᵀ := by
          rw [Matrix.transpose_mul, Matrix.transpose_transpose]
        rw [h, S.embM_transpose_mul_fullG]
        simp
  have hZfix : Z = S.fullA * Z * S.Amᵀ := by
    conv_lhs => rw [hZ, ← hS.fixed]
    show dareStep S.fullC S.R S.fullA S.Qw Sinf * embM n₁ na nm = _
    unfold dareStep
    rw [Matrix.add_mul, hQwE, add_zero]
    calc S.fullA * updM S.fullC S.R Sinf * S.fullAᵀ * embM n₁ na nm
        = S.fullA * updM S.fullC S.R Sinf
            * (S.fullAᵀ * embM n₁ na nm) := by
          simp only [Matrix.mul_assoc]
    _ = S.fullA * updM S.fullC S.R Sinf
          * (embM n₁ na nm * S.Amᵀ) := by
          rw [S.fullA_transpose_mul_embM]
    _ = S.fullA * (updM S.fullC S.R Sinf * embM n₁ na nm) * S.Amᵀ := by
          simp only [Matrix.mul_assoc]
    _ = S.fullA * Z * S.Amᵀ := by rw [hUE]
  -- rearranged: A·Z = Z·(Amᵀ)⁻¹
  have hAmT : IsUnit S.Amᵀ.det := by
    rw [Matrix.det_transpose]; exact S.isUnit_Am_det
  have hAZ : S.fullA * Z = Z * (S.Amᵀ)⁻¹ := by
    have h1 := congrArg (fun M => M * (S.Amᵀ)⁻¹) hZfix
    simp only at h1
    rw [Matrix.mul_assoc (S.fullA * Z) S.Amᵀ (S.Amᵀ)⁻¹,
      Matrix.mul_nonsing_inv _ hAmT, Matrix.mul_one] at h1
    exact h1.symm
  -- the detectability injection
  obtain ⟨L, hL⟩ := detect_inj S.fullA S.fullC hC1
  have hFZ : (S.fullA - L * S.fullC) * Z = Z * (S.Amᵀ)⁻¹ := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hCZ, Matrix.mul_zero,
      sub_zero, hAZ]
  have hFkZ : ∀ k : ℕ,
      (S.fullA - L * S.fullC) ^ k * Z = Z * ((S.Amᵀ)⁻¹) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc (S.fullA - L * S.fullC) ^ (k + 1) * Z
          = (S.fullA - L * S.fullC)
              * ((S.fullA - L * S.fullC) ^ k * Z) := by
            rw [pow_succ', Matrix.mul_assoc]
      _ = (S.fullA - L * S.fullC) * (Z * ((S.Amᵀ)⁻¹) ^ k) := by
            rw [ih]
      _ = ((S.fullA - L * S.fullC) * Z) * ((S.Amᵀ)⁻¹) ^ k := by
            rw [← Matrix.mul_assoc (S.fullA - L * S.fullC) Z
              (((S.Amᵀ)⁻¹) ^ k)]
      _ = Z * ((S.Amᵀ)⁻¹) ^ (k + 1) := by
            rw [hFZ,
              Matrix.mul_assoc Z ((S.Amᵀ)⁻¹) (((S.Amᵀ)⁻¹) ^ k),
              ← pow_succ']
  -- Schur decay on the left kills the products
  obtain ⟨c, ρ, hc, hρ0, hρ1, hpow⟩ := hL.exists_pow_norm_le
  -- rows of Z die under no_decay
  have hrow : ∀ j : ix n₁ na nm, Zᵀ *ᵥ Pi.single j (1 : ℝ) = 0 := by
    intro j
    refine no_decay S.Am⁻¹ S.Am_inv_spectrum ?_
    have hnorm : ∀ k : ℕ,
        ‖(S.Am⁻¹) ^ k *ᵥ (Zᵀ *ᵥ Pi.single j (1 : ℝ))‖
          ≤ ((Fintype.card (ix n₁ na nm) : ℝ) * (c * ρ ^ k * ‖Z‖))
            * ‖(Pi.single j 1 : ix n₁ na nm → ℝ)‖ := by
      intro k
      have hmat : (S.Am⁻¹) ^ k * Zᵀ
          = ((S.fullA - L * S.fullC) ^ k * Z)ᵀ := by
        rw [hFkZ k, Matrix.transpose_mul, Matrix.transpose_pow,
          Matrix.transpose_nonsing_inv, Matrix.transpose_transpose]
      have h1 : (S.Am⁻¹) ^ k *ᵥ (Zᵀ *ᵥ Pi.single j (1 : ℝ))
          = ((S.fullA - L * S.fullC) ^ k * Z)ᵀ
              *ᵥ Pi.single j (1 : ℝ) := by
        rw [Matrix.mulVec_mulVec, hmat]
      rw [h1]
      calc ‖((S.fullA - L * S.fullC) ^ k * Z)ᵀ *ᵥ Pi.single j 1‖
          ≤ ‖((S.fullA - L * S.fullC) ^ k * Z)ᵀ‖
              * ‖(Pi.single j 1 : ix n₁ na nm → ℝ)‖ :=
            Matrix.linfty_opNorm_mulVec _ _
      _ ≤ ((Fintype.card (ix n₁ na nm) : ℝ)
              * ‖(S.fullA - L * S.fullC) ^ k * Z‖)
            * ‖(Pi.single j 1 : ix n₁ na nm → ℝ)‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            exact linfty_opNorm_transpose_le' _
      _ ≤ ((Fintype.card (ix n₁ na nm) : ℝ) * (c * ρ ^ k * ‖Z‖))
            * ‖(Pi.single j 1 : ix n₁ na nm → ℝ)‖ := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
              (norm_nonneg _)
            calc ‖(S.fullA - L * S.fullC) ^ k * Z‖
                ≤ ‖(S.fullA - L * S.fullC) ^ k‖ * ‖Z‖ :=
                  Matrix.linfty_opNorm_mul _ _
            _ ≤ c * ρ ^ k * ‖Z‖ :=
                  mul_le_mul_of_nonneg_right (hpow k) (norm_nonneg _)
    refine squeeze_zero_norm hnorm ?_
    have h2 : Tendsto (fun k : ℕ => ρ ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1
    have h3 : Tendsto (fun k : ℕ =>
        ((Fintype.card (ix n₁ na nm) : ℝ) * (c * ρ ^ k * ‖Z‖))
          * ‖(Pi.single j 1 : ix n₁ na nm → ℝ)‖) atTop (nhds 0) := by
      have h4 := ((h2.const_mul c).mul_const ‖Z‖).const_mul
        (Fintype.card (ix n₁ na nm) : ℝ)
      have h5 := h4.mul_const ‖(Pi.single j 1 : ix n₁ na nm → ℝ)‖
      simpa using h5
    exact h3
  have hZt : Zᵀ = 0 := by
    ext i j
    have h1 := congrFun (hrow j) i
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
      Finset.sum_ite_eq'] using h1
  have h2 := congrArg Matrix.transpose hZt
  rwa [Matrix.transpose_transpose, Matrix.transpose_zero] at h2

end DareSystem

end Dare
end Estimation