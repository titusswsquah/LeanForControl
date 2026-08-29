import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Real.StarOrdered
import Architect

/-!
# Real quadratic forms of matrices

The `costogo` value functions are quadratic forms `x ⬝ᵥ (M *ᵥ x)` of real
matrices over general finite index types (the estimation layer works over
`Fin n₁ ⊕ Fin n₂`). This file fixes the conventions and provides the
`fact:psd-bounds` glue:

* `LinearSystems.quadForm M x = x ⬝ᵥ (M *ᵥ x)`;
* expansion, nonnegativity/positivity from `PosSemidef`/`PosDef`;
* two-sided norm equivalence in the sup norm:
  `PosDef.exists_le_quadForm` (`c‖x‖² ≤ x'Mx`) and
  `exists_quadForm_le` (`x'Mx ≤ c‖x‖²`), via the spectral theorem;
* comparison along the Loewner order
  (`quadForm_le_quadForm_of_posSemidef_sub`), and its converse
  (`posSemidef_sub_of_quadForm_le` — pointwise domination of quadratic
  forms between symmetric matrices is the Loewner order).

Matrix norms, where they appear, are the `L∞` operator norm.
-/

namespace LinearSystems

open Matrix

variable {ι : Type*} [Fintype ι] {κ : Type*} [Fintype κ]

/-- The quadratic form of a real matrix: `quadForm M x = x ⬝ᵥ (M *ᵥ x)`. -/
def quadForm (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  x ⬝ᵥ (M *ᵥ x)

@[simp]
lemma quadForm_zero_matrix (x : ι → ℝ) : quadForm (0 : Matrix ι ι ℝ) x = 0 := by
  simp [quadForm]

@[simp]
lemma quadForm_zero (M : Matrix ι ι ℝ) : quadForm M 0 = 0 := by
  simp [quadForm]

lemma quadForm_add_matrix (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadForm (M + N) x = quadForm M x + quadForm N x := by
  simp [quadForm, Matrix.add_mulVec, dotProduct_add]

lemma quadForm_sub_matrix (M N : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadForm (M - N) x = quadForm M x - quadForm N x := by
  simp [quadForm, Matrix.sub_mulVec, dotProduct_sub]

lemma quadForm_smul (M : Matrix ι ι ℝ) (c : ℝ) (x : ι → ℝ) :
    quadForm M (c • x) = c ^ 2 * quadForm M x := by
  simp only [quadForm, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  ring

lemma quadForm_neg (M : Matrix ι ι ℝ) (x : ι → ℝ) :
    quadForm M (-x) = quadForm M x := by
  have h := quadForm_smul M (-1) x
  simpa using h

/-- Expansion of the quadratic form of a sum (no symmetry required). -/
lemma quadForm_add (M : Matrix ι ι ℝ) (x y : ι → ℝ) :
    quadForm M (x + y)
      = quadForm M x + x ⬝ᵥ (M *ᵥ y) + y ⬝ᵥ (M *ᵥ x) + quadForm M y := by
  simp only [quadForm, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
  ring

/-- Move a matrix across the dot product. -/
lemma mulVec_dotProduct_eq (A : Matrix ι κ ℝ) (x : κ → ℝ) (y : ι → ℝ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]

/-- Move a matrix across the dot product, transposed version. -/
lemma dotProduct_mulVec_eq (A : Matrix ι κ ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    x ⬝ᵥ (A *ᵥ y) = (Aᵀ *ᵥ x) ⬝ᵥ y := by
  rw [mulVec_dotProduct_eq, transpose_transpose]

/-- Quadratic form of an image vector: `(Ny)'M(Ny) = y'(NᵀMN)y`. -/
lemma quadForm_mulVec (M : Matrix ι ι ℝ) (N : Matrix ι κ ℝ) (y : κ → ℝ) :
    quadForm M (N *ᵥ y) = quadForm (Nᵀ * M * N) y := by
  rw [quadForm, quadForm, mulVec_dotProduct_eq, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

/-- Bilinear form of two image vectors:
`(Ny)'M(N'z) = y'(NᵀMN')z`. -/
lemma mulVec_dotProduct_mulVec_mulVec {κ' : Type*} [Fintype κ']
    (M : Matrix ι ι ℝ) (N : Matrix ι κ ℝ) (N' : Matrix ι κ' ℝ)
    (y : κ → ℝ) (z : κ' → ℝ) :
    (N *ᵥ y) ⬝ᵥ (M *ᵥ (N' *ᵥ z)) = y ⬝ᵥ ((Nᵀ * M * N') *ᵥ z) := by
  rw [mulVec_dotProduct_eq, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- Bilinear symmetry for a symmetric matrix. -/
lemma dotProduct_mulVec_comm {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (x y : ι → ℝ) : x ⬝ᵥ (M *ᵥ y) = y ⬝ᵥ (M *ᵥ x) := by
  rw [dotProduct_mulVec_eq]
  have h2 : Mᵀ = M := by
    rw [← conjTranspose_eq_transpose_of_trivial]
    exact hM
  rw [h2, dotProduct_comm]

/-- Expansion of the quadratic form of a sum, symmetric version. -/
lemma quadForm_add_of_isHermitian {M : Matrix ι ι ℝ} (hM : M.IsHermitian)
    (x y : ι → ℝ) :
    quadForm M (x + y) = quadForm M x + 2 * (x ⬝ᵥ (M *ᵥ y)) + quadForm M y := by
  rw [quadForm_add, dotProduct_mulVec_comm hM y x]
  ring

lemma _root_.Matrix.PosSemidef.quadForm_nonneg {M : Matrix ι ι ℝ}
    (hM : M.PosSemidef) (x : ι → ℝ) : 0 ≤ quadForm M x := by
  have h := hM.re_dotProduct_nonneg x
  simpa [quadForm] using h

lemma _root_.Matrix.PosDef.quadForm_pos {M : Matrix ι ι ℝ} (hM : M.PosDef)
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < quadForm M x := by
  have h := hM.re_dotProduct_pos hx
  simpa [quadForm] using h

/-- Loewner comparison of quadratic forms. -/
lemma quadForm_le_quadForm_of_posSemidef_sub {M N : Matrix ι ι ℝ}
    (h : (N - M).PosSemidef) (x : ι → ℝ) : quadForm M x ≤ quadForm N x := by
  have h1 := h.quadForm_nonneg x
  rw [quadForm_sub_matrix] at h1
  linarith

/-- Pointwise domination of quadratic forms between symmetric matrices is
the Loewner order. -/
lemma posSemidef_sub_of_quadForm_le {M N : Matrix ι ι ℝ}
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (h : ∀ x, quadForm M x ≤ quadForm N x) : (N - M).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hN.sub hM) fun x => ?_
  have h1 := h x
  rw [← sub_nonneg, ← quadForm_sub_matrix] at h1
  simpa [quadForm] using h1

section NormBounds

open scoped Matrix.Norms.Operator

/-- `‖x‖² ≤ x ⬝ᵥ x` in the sup norm. -/
lemma sq_norm_le_dotProduct (x : ι → ℝ) : ‖x‖ ^ 2 ≤ x ⬝ᵥ x := by
  have hxx : (0 : ℝ) ≤ x ⬝ᵥ x := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hnorm : ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
    have h1 : x i ^ 2 ≤ x ⬝ᵥ x := by
      have := Finset.single_le_sum (f := fun j => x j * x j)
        (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
      simpa [dotProduct, sq] using this
    calc ‖x i‖ = Real.sqrt (x i ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
    _ ≤ Real.sqrt (x ⬝ᵥ x) := Real.sqrt_le_sqrt h1
  calc ‖x‖ ^ 2 ≤ Real.sqrt (x ⬝ᵥ x) ^ 2 := by
        have h0 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
        gcongr
  _ = x ⬝ᵥ x := Real.sq_sqrt hxx

/-- `x ⬝ᵥ x ≤ card ι * ‖x‖²` in the sup norm. -/
lemma dotProduct_le_card_mul_sq_norm (x : ι → ℝ) :
    x ⬝ᵥ x ≤ (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
  calc x ⬝ᵥ x = ∑ i, x i * x i := rfl
  _ ≤ ∑ _i : ι, ‖x‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : ‖x i‖ ≤ ‖x‖ := norm_le_pi_norm x i
      calc x i * x i = ‖x i‖ ^ 2 := by
            rw [Real.norm_eq_abs, sq_abs, sq]
      _ ≤ ‖x‖ ^ 2 := by
            have h0 : (0 : ℝ) ≤ ‖x i‖ := norm_nonneg _
            gcongr
  _ = (Fintype.card ι : ℝ) * ‖x‖ ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Any quadratic form is bounded above by a multiple of `‖x‖²`. -/
lemma exists_quadForm_le (M : Matrix ι ι ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ι → ℝ, quadForm M x ≤ c * ‖x‖ ^ 2 := by
  refine ⟨(Fintype.card ι : ℝ) * ‖M‖ + 1, by positivity, fun x => ?_⟩
  have h1 : quadForm M x ≤ ‖x‖ * ((Fintype.card ι : ℝ) * (‖M‖ * ‖x‖)) := by
    calc quadForm M x ≤ |x ⬝ᵥ (M *ᵥ x)| := le_abs_self _
    _ ≤ ∑ i, |x i| * |(M *ᵥ x) i| := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun i _ => le_of_eq ?_
        rw [abs_mul]
    _ ≤ ∑ _i : ι, ‖x‖ * ‖M *ᵥ x‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h2 : |x i| ≤ ‖x‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm x i
        have h3 : |(M *ᵥ x) i| ≤ ‖M *ᵥ x‖ := by
          rw [← Real.norm_eq_abs]
          exact norm_le_pi_norm _ i
        exact mul_le_mul h2 h3 (abs_nonneg _) (norm_nonneg _)
    _ = (Fintype.card ι : ℝ) * (‖x‖ * ‖M *ᵥ x‖) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card ι : ℝ) * (‖x‖ * (‖M‖ * ‖x‖)) := by
        have h4 := Matrix.linfty_opNorm_mulVec M x
        have h5 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
        have h6 : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 h5) h6
    _ = ‖x‖ * ((Fintype.card ι : ℝ) * (‖M‖ * ‖x‖)) := by ring
  have h7 : ‖x‖ * ((Fintype.card ι : ℝ) * (‖M‖ * ‖x‖))
      ≤ ((Fintype.card ι : ℝ) * ‖M‖ + 1) * ‖x‖ ^ 2 := by
    have h8 : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
    nlinarith [norm_nonneg x, norm_nonneg M, Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  linarith

/-- A positive definite quadratic form dominates a multiple of `‖x‖²`
(the `λ_min` bound of `fact:psd-bounds`, in the sup norm). -/
lemma _root_.Matrix.PosDef.exists_le_quadForm {M : Matrix ι ι ℝ}
    (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ι → ℝ, c * ‖x‖ ^ 2 ≤ quadForm M x := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun x => by
      simp [quadForm, Subsingleton.elim x 0]⟩
  · -- `x'Mx = ∑ λᵢ cᵢ²` with `c = Uᵀx`; bound below by `λ_min · x⬝ᵥx`.
    set lmin : ℝ := Finset.univ.inf' Finset.univ_nonempty hM.1.eigenvalues
      with hlmin
    have hlmin_pos : 0 < lmin := by
      rw [hlmin, Finset.lt_inf'_iff]
      exact fun i _ => hM.eigenvalues_pos i
    refine ⟨lmin, hlmin_pos, fun x => ?_⟩
    have hspec := hM.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hspec
    set U : Matrix ι ι ℝ := (hM.1.eigenvectorUnitary : Matrix ι ι ℝ) with hU
    set c : ι → ℝ := star U *ᵥ x with hc
    have hstar : star U = Uᵀ := by
      rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    have hUU : U * star U = 1 := by
      rw [hU]
      exact Unitary.coe_mul_star_self _
    have hUdecomp : M = U * diagonal hM.1.eigenvalues * star U := by
      simpa [hU] using hspec
    have key : lmin * (x ⬝ᵥ x) ≤ quadForm M x := by
      have hMx : quadForm M x = ∑ i, hM.1.eigenvalues i * c i ^ 2 := by
        have h0 : quadForm M x
            = quadForm (U * diagonal hM.1.eigenvalues * star U) x := by
          conv_lhs => rw [hUdecomp]
        rw [h0, quadForm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          dotProduct_mulVec_eq, ← hstar, ← hc]
        simp only [dotProduct, mulVec_diagonal, sq]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hcc : x ⬝ᵥ x = ∑ i, c i ^ 2 := by
        have h1 : ∑ i, c i ^ 2 = c ⬝ᵥ c := by
          simp only [dotProduct, sq]
        rw [h1, hc, mulVec_dotProduct_eq, hstar, transpose_transpose,
          Matrix.mulVec_mulVec, ← hstar, hUU, Matrix.one_mulVec]
      rw [hMx, hcc, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have h1 : lmin ≤ hM.1.eigenvalues i :=
        Finset.inf'_le _ (Finset.mem_univ i)
      have h2 : (0 : ℝ) ≤ c i ^ 2 := sq_nonneg _
      exact mul_le_mul_of_nonneg_right h1 h2
    calc lmin * ‖x‖ ^ 2 ≤ lmin * (x ⬝ᵥ x) :=
          mul_le_mul_of_nonneg_left (sq_norm_le_dotProduct x) hlmin_pos.le
    _ ≤ quadForm M x := key

end NormBounds

section QuadSolve

set_option linter.unusedDecidableInType false

variable [DecidableEq ι]

/-- **Solvability from bounded-below quadratics**: if `L ⪰ 0` and the
quadratic `v ↦ v'Lv - 2 r⬝v` is bounded below, then `r ∈ range L`. This is
the existence half of every KKT system in the estimation layer: costs are
nonnegative, so their stationarity equations are solvable. -/
lemma _root_.Matrix.PosSemidef.exists_mulVec_eq {L : Matrix ι ι ℝ}
    (hL : L.PosSemidef) {r : ι → ℝ} {c : ℝ}
    (hbdd : ∀ v : ι → ℝ, 2 * (r ⬝ᵥ v) ≤ quadForm L v + c) :
    ∃ v : ι → ℝ, L *ᵥ v = r := by
  classical
  -- Spectral decomposition of `L`.
  have hspec := hL.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set U : Matrix ι ι ℝ := (hL.1.eigenvectorUnitary : Matrix ι ι ℝ) with hU
  set lam : ι → ℝ := hL.1.eigenvalues with hlam
  have hstar : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hUU : U * star U = 1 := by
    rw [hU]
    exact Unitary.coe_mul_star_self _
  have hUU' : star U * U = 1 := by
    rw [hU]
    exact Unitary.coe_star_mul_self _
  have hLdecomp : L = U * diagonal lam * star U := by
    simpa [hU, hlam] using hspec
  set rt : ι → ℝ := star U *ᵥ r with hrt
  -- Zero eigenvalues force the corresponding transformed coordinates of `r`
  -- to vanish.
  have hzero : ∀ i, lam i = 0 → rt i = 0 := by
    intro i hi
    by_contra hne
    -- test with `v = t • (U eᵢ)`
    have htest : ∀ t : ℝ, 2 * (t * rt i) ≤ c := by
      intro t
      have h := hbdd (t • (U *ᵥ Pi.single i 1))
      have h1 : quadForm L (t • (U *ᵥ Pi.single i 1)) = 0 := by
        rw [quadForm_smul]
        have h3 : quadForm L (U *ᵥ Pi.single i 1)
            = quadForm (Uᵀ * L * U) (Pi.single i 1) := quadForm_mulVec _ _ _
        have h4 : Uᵀ * L * U = diagonal lam := by
          rw [hLdecomp, ← hstar]
          calc star U * (U * diagonal lam * star U) * U
              = (star U * U) * diagonal lam * (star U * U) := by
                simp only [Matrix.mul_assoc]
          _ = diagonal lam := by rw [hUU']; simp
        rw [h3, h4, quadForm]
        have h6 : (diagonal lam *ᵥ Pi.single i 1) ⬝ᵥ Pi.single i 1 = lam i := by
          simp [mulVec_diagonal, dotProduct, Pi.single_apply]
        rw [dotProduct_comm, h6, hi, mul_zero]
      have h5 : r ⬝ᵥ (t • (U *ᵥ Pi.single i 1)) = t * rt i := by
        rw [dotProduct_smul, smul_eq_mul, dotProduct_mulVec_eq]
        congr 1
        rw [hrt, hstar]
        simp [dotProduct, Pi.single_apply]
      rw [h1, h5] at h
      linarith
    have hcontr := htest ((c + 1) / (2 * rt i))
    have heq : 2 * ((c + 1) / (2 * rt i) * rt i) = c + 1 := by
      field_simp
    rw [heq] at hcontr
    linarith
  -- Solve in the eigenbasis, killing the zero directions.
  refine ⟨U *ᵥ (fun i => rt i * (lam i)⁻¹), ?_⟩
  have hDv : diagonal lam *ᵥ (fun i => rt i * (lam i)⁻¹) = rt := by
    funext i
    rw [mulVec_diagonal]
    rcases eq_or_ne (lam i) 0 with h | h
    · rw [hzero i h, h]
      ring
    · field_simp
  rw [hLdecomp]
  calc (U * diagonal lam * star U) *ᵥ (U *ᵥ fun i => rt i * (lam i)⁻¹)
      = (U * diagonal lam * (star U * U)) *ᵥ (fun i => rt i * (lam i)⁻¹) := by
        rw [Matrix.mulVec_mulVec]
        simp only [Matrix.mul_assoc]
  _ = (U * diagonal lam) *ᵥ (fun i => rt i * (lam i)⁻¹) := by
        rw [hUU', Matrix.mul_one]
  _ = U *ᵥ rt := by rw [← Matrix.mulVec_mulVec, hDv]
  _ = r := by rw [hrt, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]

/-- A positive semidefinite quadratic form vanishes only along the kernel:
`x'Mx = 0` forces `Mx = 0`. -/
lemma _root_.Matrix.PosSemidef.mulVec_eq_zero_of_quadForm_eq_zero
    {M : Matrix ι ι ℝ} (hM : M.PosSemidef) {x : ι → ℝ}
    (hx : quadForm M x = 0) : M *ᵥ x = 0 := by
  funext j
  -- For every `y`, expanding `0 ≤ quadForm M (x + t • y)` in `t` forces the
  -- cross term to vanish; take `y = eⱼ`.
  have key : ∀ y : ι → ℝ, y ⬝ᵥ (M *ᵥ x) = 0 := by
    intro y
    by_contra hne
    set b : ℝ := y ⬝ᵥ (M *ᵥ x) with hb
    set q : ℝ := quadForm M y with hq
    have hexp : ∀ t : ℝ, 0 ≤ t ^ 2 * q + 2 * t * b := by
      intro t
      have h := hM.quadForm_nonneg (x + t • y)
      rw [quadForm_add, hx] at h
      have h1 : x ⬝ᵥ (M *ᵥ (t • y)) = t * (x ⬝ᵥ (M *ᵥ y)) := by
        rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
      have h2 : (t • y) ⬝ᵥ (M *ᵥ x) = t * b := by
        rw [smul_dotProduct, smul_eq_mul, hb]
      have h3 : quadForm M (t • y) = t ^ 2 * q := by
        rw [quadForm_smul, hq]
      rw [h1, h2, h3] at h
      -- symmetric cross term: x'My = y'Mx = b
      have h4 : x ⬝ᵥ (M *ᵥ y) = b := by
        rw [dotProduct_mulVec_comm hM.1, hb]
      rw [h4] at h
      linarith
    -- a quadratic `q t² + 2bt` with `b ≠ 0` takes negative values
    have hqnn : 0 ≤ q := hM.quadForm_nonneg y
    have hb2 : 0 < b ^ 2 :=
      lt_of_le_of_ne (sq_nonneg b) (Ne.symm (pow_ne_zero 2 hne))
    rcases eq_or_ne q 0 with hq0 | hq0
    · have h5 := hexp (-b)
      rw [hq0] at h5
      nlinarith
    · have hqpos : 0 < q := lt_of_le_of_ne hqnn (Ne.symm hq0)
      have h5 := hexp (-(b / q))
      have h6 : (-(b / q)) ^ 2 * q + 2 * (-(b / q)) * b = -(b ^ 2 / q) := by
        field_simp
        ring
      rw [h6] at h5
      have h7 : 0 < b ^ 2 / q := div_pos hb2 hqpos
      linarith
  have h := key (Pi.single j 1)
  rw [dotProduct_comm] at h
  simpa [dotProduct, Pi.single_apply] using h

end QuadSolve

end LinearSystems
