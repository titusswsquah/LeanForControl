import LeanForControl.Estimation.Dare.CondChart
import Architect

/-!
# The lower anchor converges (`lem:condfilter`-3, `lem:jtransform`,
`lem:lowsqueeze`)

The analysis layer over the verified chart algebra. The strong
solution itself carries a chart (marginal loading `0`, by extinction);
its data are fixed points of the chart map (chart extraction). The
trajectory data converge to them: `P_T → P∞` is the deck's
`fact:dare-strong` import on the reduced `e₁` system (hypothesized as
`ReducedImport`, with the closed-loop product bound); `Λₘₐ → 0` is
`lem:loading`; `Λ₁ₐ → Λ∞` rides the perturbed Stein recursion against
the Schur `Aₐ⁻¹`; the information `J₁ = Σₐₐ⁻¹` homes on the fixed
`Aₐ⁻¹`-gramian. Assembling through the decomposition gives
`eq:lowsqueeze`.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

/-- The generalized Schur complement of a PSD form through two test
maps is PSD. -/
lemma schur_compl_posSemidef {ι k₁ k₂ : Type} [Fintype ι]
    [Fintype k₁] [Fintype k₂] [DecidableEq k₂]
    {Sg : Matrix ι ι ℝ} (hSg : Sg.PosSemidef)
    (W₁ : Matrix ι k₁ ℝ) (W₂ : Matrix ι k₂ ℝ)
    (hcorner : (W₂ᵀ * Sg * W₂).PosDef) :
    (W₁ᵀ * Sg * W₁ - W₁ᵀ * Sg * W₂ * (W₂ᵀ * Sg * W₂)⁻¹
      * (W₂ᵀ * Sg * W₁)).PosSemidef := by
  have hBu : IsUnit (W₂ᵀ * Sg * W₂).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hcorner.isUnit
  have hBsym : (W₂ᵀ * Sg * W₂)ᵀ = W₂ᵀ * Sg * W₂ :=
    hcorner.posSemidef.1.transpose_eq_self
  have hSgSym : Sgᵀ = Sg := hSg.1.transpose_eq_self
  have hherm : (W₁ᵀ * Sg * W₁ - W₁ᵀ * Sg * W₂ * (W₂ᵀ * Sg * W₂)⁻¹
      * (W₂ᵀ * Sg * W₁)).IsHermitian := by
    rw [Matrix.IsHermitian,
      Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_sub]
    congr 1
    · simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
        hSgSym]
      simp only [Matrix.mul_assoc]
    · simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_nonsing_inv, hSgSym, hBsym]
      simp only [Matrix.mul_assoc]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm fun u => ?_
  rw [star_trivial]
  have hq := hSg.quadForm_nonneg (W₁ *ᵥ u
    - W₂ *ᵥ ((W₂ᵀ * Sg * W₂)⁻¹ *ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u)))
  have hexp : quadForm Sg (W₁ *ᵥ u
      - W₂ *ᵥ ((W₂ᵀ * Sg * W₂)⁻¹ *ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u)))
      = u ⬝ᵥ ((W₁ᵀ * Sg * W₁ - W₁ᵀ * Sg * W₂ * (W₂ᵀ * Sg * W₂)⁻¹
          * (W₂ᵀ * Sg * W₁)) *ᵥ u) := by
    have hcollapse : ∀ {k : Type} [Fintype k] (W : Matrix ι k ℝ)
        (z : ι → ℝ), Wᵀ *ᵥ (Sg *ᵥ z) = (Wᵀ * Sg) *ᵥ z := by
      intro k _ W z
      rw [Matrix.mulVec_mulVec]
    unfold quadForm
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct,
      sub_dotProduct]
    have e11 : (W₁ *ᵥ u) ⬝ᵥ (Sg *ᵥ (W₁ *ᵥ u))
        = u ⬝ᵥ ((W₁ᵀ * Sg * W₁) *ᵥ u) := by
      rw [mulVec_dotProduct_eq, hcollapse, Matrix.mulVec_mulVec]
    have e12 : (W₁ *ᵥ u) ⬝ᵥ (Sg *ᵥ (W₂ *ᵥ ((W₂ᵀ * Sg * W₂)⁻¹
          *ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u))))
        = u ⬝ᵥ ((W₁ᵀ * Sg * W₂ * (W₂ᵀ * Sg * W₂)⁻¹
            * (W₂ᵀ * Sg * W₁)) *ᵥ u) := by
      rw [mulVec_dotProduct_eq, hcollapse]
      simp only [Matrix.mulVec_mulVec]
      simp only [← Matrix.mul_assoc]
    have e21 : (W₂ *ᵥ ((W₂ᵀ * Sg * W₂)⁻¹
          *ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u)))
          ⬝ᵥ (Sg *ᵥ (W₁ *ᵥ u))
        = ((W₂ᵀ * Sg * W₂)⁻¹ *ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u))
          ⬝ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u) := by
      rw [mulVec_dotProduct_eq]
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    have e22 : (W₂ *ᵥ ((W₂ᵀ * Sg * W₂)⁻¹
          *ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u)))
          ⬝ᵥ (Sg *ᵥ (W₂ *ᵥ ((W₂ᵀ * Sg * W₂)⁻¹
            *ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u))))
        = ((W₂ᵀ * Sg * W₂)⁻¹ *ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u))
          ⬝ᵥ ((W₂ᵀ * Sg * W₁) *ᵥ u) := by
      rw [mulVec_dotProduct_eq]
      simp only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
      rw [show W₂ᵀ * Sg * W₂ * (W₂ᵀ * Sg * W₂)⁻¹ * W₂ᵀ * Sg * W₁
        = W₂ᵀ * Sg * W₁ by
          rw [Matrix.mul_nonsing_inv _ hBu, Matrix.one_mul]]
    rw [e11, e12, e21, e22, Matrix.sub_mulVec, dotProduct_sub]
    ring
  rw [← hexp]
  exact hq

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-! ### Chart extraction and uniqueness -/

variable {Sg : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

lemma condVt_mul_embA (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    (condV Λ1a Λma)ᵀ * embA n₁ na nm = 1 := by
  have h := congrArg Matrix.transpose (embAt_mul_condV Λ1a Λma)
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_one] at h

lemma condVt_mul_emb1 (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    (condV Λ1a Λma)ᵀ * emb1 n₁ na nm = Λ1aᵀ := by
  have h := congrArg Matrix.transpose (emb1t_mul_condV Λ1a Λma)
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at h

/-- Chart extraction: the antistable corner. -/
lemma CondChart.extract_Saa (c : CondChart Sg) :
    (embA n₁ na nm)ᵀ * Sg * embA n₁ na nm = c.Saa := by
  obtain ⟨P, Λ1a, Λma, Saa, hP, hSaa, hdec⟩ := c
  dsimp only
  rw [hdec, Matrix.mul_add, Matrix.add_mul]
  have h1 : (embA n₁ na nm)ᵀ * (emb1 n₁ na nm * P
        * (emb1 n₁ na nm)ᵀ) * embA n₁ na nm = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, embAt_mul_emb1,
      Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
  have h2 : (embA n₁ na nm)ᵀ * (condV Λ1a Λma * Saa
        * (condV Λ1a Λma)ᵀ) * embA n₁ na nm = Saa := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, embAt_mul_condV,
      Matrix.one_mul, Matrix.mul_assoc, condVt_mul_embA,
      Matrix.mul_one]
  rw [h1, h2, zero_add]

/-- Chart extraction: the stabilizable–antistable cross block. -/
lemma CondChart.extract_1a (c : CondChart Sg) :
    (emb1 n₁ na nm)ᵀ * Sg * embA n₁ na nm = c.Λ1a * c.Saa := by
  obtain ⟨P, Λ1a, Λma, Saa, hP, hSaa, hdec⟩ := c
  dsimp only
  rw [hdec, Matrix.mul_add, Matrix.add_mul]
  have h1 : (emb1 n₁ na nm)ᵀ * (emb1 n₁ na nm * P
        * (emb1 n₁ na nm)ᵀ) * embA n₁ na nm = 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, emb1t_mul_emb1,
      Matrix.one_mul, Matrix.mul_assoc, emb1t_mul_embA,
      Matrix.mul_zero]
  have h2 : (emb1 n₁ na nm)ᵀ * (condV Λ1a Λma * Saa
        * (condV Λ1a Λma)ᵀ) * embA n₁ na nm
      = Λ1a * Saa := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, emb1t_mul_condV,
      Matrix.mul_assoc, condVt_mul_embA, Matrix.mul_one]
  rw [h1, h2, zero_add]

/-- Chart extraction: the stabilizable block. -/
lemma CondChart.extract_11 (c : CondChart Sg) :
    (emb1 n₁ na nm)ᵀ * Sg * emb1 n₁ na nm
      = c.P + c.Λ1a * c.Saa * c.Λ1aᵀ := by
  obtain ⟨P, Λ1a, Λma, Saa, hP, hSaa, hdec⟩ := c
  dsimp only
  rw [hdec, Matrix.mul_add, Matrix.add_mul]
  have h1 : (emb1 n₁ na nm)ᵀ * (emb1 n₁ na nm * P
        * (emb1 n₁ na nm)ᵀ) * emb1 n₁ na nm = P := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, emb1t_mul_emb1,
      Matrix.one_mul, Matrix.mul_assoc, emb1t_mul_emb1,
      Matrix.mul_one]
  have h2 : (emb1 n₁ na nm)ᵀ * (condV Λ1a Λma * Saa
        * (condV Λ1a Λma)ᵀ) * emb1 n₁ na nm
      = Λ1a * Saa * Λ1aᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, emb1t_mul_condV,
      Matrix.mul_assoc, condVt_mul_emb1]
  rw [h1, h2]

/-- The three-way block reconstruction. -/
lemma partition3_decomp (M : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) :
    M = emb1 n₁ na nm * ((emb1 n₁ na nm)ᵀ * M * emb1 n₁ na nm)
          * (emb1 n₁ na nm)ᵀ
      + emb1 n₁ na nm * ((emb1 n₁ na nm)ᵀ * M * embA n₁ na nm)
          * (embA n₁ na nm)ᵀ
      + emb1 n₁ na nm * ((emb1 n₁ na nm)ᵀ * M * embM n₁ na nm)
          * (embM n₁ na nm)ᵀ
      + embA n₁ na nm * ((embA n₁ na nm)ᵀ * M * emb1 n₁ na nm)
          * (emb1 n₁ na nm)ᵀ
      + embA n₁ na nm * ((embA n₁ na nm)ᵀ * M * embA n₁ na nm)
          * (embA n₁ na nm)ᵀ
      + embA n₁ na nm * ((embA n₁ na nm)ᵀ * M * embM n₁ na nm)
          * (embM n₁ na nm)ᵀ
      + embM n₁ na nm * ((embM n₁ na nm)ᵀ * M * emb1 n₁ na nm)
          * (emb1 n₁ na nm)ᵀ
      + embM n₁ na nm * ((embM n₁ na nm)ᵀ * M * embA n₁ na nm)
          * (embA n₁ na nm)ᵀ
      + embM n₁ na nm * ((embM n₁ na nm)ᵀ * M * embM n₁ na nm)
          * (embM n₁ na nm)ᵀ := by
  have h1 : (emb1 n₁ na nm * (emb1 n₁ na nm)ᵀ
        + embA n₁ na nm * (embA n₁ na nm)ᵀ
        + embM n₁ na nm * (embM n₁ na nm)ᵀ) * M
      * (emb1 n₁ na nm * (emb1 n₁ na nm)ᵀ
        + embA n₁ na nm * (embA n₁ na nm)ᵀ
        + embM n₁ na nm * (embM n₁ na nm)ᵀ)
      = emb1 n₁ na nm * ((emb1 n₁ na nm)ᵀ * M * emb1 n₁ na nm)
          * (emb1 n₁ na nm)ᵀ
      + emb1 n₁ na nm * ((emb1 n₁ na nm)ᵀ * M * embA n₁ na nm)
          * (embA n₁ na nm)ᵀ
      + emb1 n₁ na nm * ((emb1 n₁ na nm)ᵀ * M * embM n₁ na nm)
          * (embM n₁ na nm)ᵀ
      + embA n₁ na nm * ((embA n₁ na nm)ᵀ * M * emb1 n₁ na nm)
          * (emb1 n₁ na nm)ᵀ
      + embA n₁ na nm * ((embA n₁ na nm)ᵀ * M * embA n₁ na nm)
          * (embA n₁ na nm)ᵀ
      + embA n₁ na nm * ((embA n₁ na nm)ᵀ * M * embM n₁ na nm)
          * (embM n₁ na nm)ᵀ
      + embM n₁ na nm * ((embM n₁ na nm)ᵀ * M * emb1 n₁ na nm)
          * (emb1 n₁ na nm)ᵀ
      + embM n₁ na nm * ((embM n₁ na nm)ᵀ * M * embA n₁ na nm)
          * (embA n₁ na nm)ᵀ
      + embM n₁ na nm * ((embM n₁ na nm)ᵀ * M * embM n₁ na nm)
          * (embM n₁ na nm)ᵀ := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
    abel
  rw [← h1, partition3, Matrix.one_mul, Matrix.mul_one]

/-! ### The strong solution's chart -/

variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-- The strong solution's conditional block `P∞ = Σ∞|₁|ₐ`
(`eq:condcov` at the fixed point). -/
noncomputable def infP (Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) :
    Matrix (Fin n₁) (Fin n₁) ℝ :=
  (emb1 n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm
    - (emb1 n₁ na nm)ᵀ * Sinf * embA n₁ na nm
      * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
      * ((embA n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm)

/-- The strong solution's loading `Λ∞ = Σ∞|₁ₐ·(Σ∞|ₐₐ)⁻¹`. -/
noncomputable def infLam
    (Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) :
    Matrix (Fin n₁) (Fin na) ℝ :=
  (emb1 n₁ na nm)ᵀ * Sinf * embA n₁ na nm
    * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹

/-- **The strong solution's conditional decomposition**: `Σ∞` is
charted with zero marginal loading (`eq:marg-extinct`). -/
theorem strong_decomp (hC1 : S.C1) (hS : S.IsStrongSolution Sinf) :
    Sinf = emb1 n₁ na nm * infP Sinf * (emb1 n₁ na nm)ᵀ
      + condV (infLam Sinf) 0
        * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
        * (condV (infLam Sinf) 0)ᵀ := by
  have hSaa := S.strong_corner_posDef hS
  have hSaaU : IsUnit ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSaa.isUnit
  have hSaaSym : ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)ᵀ
      = (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm :=
    hSaa.posSemidef.1.transpose_eq_self
  have hSym : Sinfᵀ = Sinf := hS.posSemidef.1.transpose_eq_self
  have hcolM : Sinf * embM n₁ na nm = 0 := S.strong_marg_extinct hC1 hS
  have hrowM : (embM n₁ na nm)ᵀ * Sinf = 0 := by
    have h := congrArg Matrix.transpose hcolM
    rwa [Matrix.transpose_mul, hSym, Matrix.transpose_zero] at h
  -- the transposed cross block
  have hS1at : ((emb1 n₁ na nm)ᵀ * Sinf * embA n₁ na nm)ᵀ
      = (embA n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hSym]
    simp only [Matrix.mul_assoc]
  -- kill the marginal blocks in the reconstruction
  have hz1 : (emb1 n₁ na nm)ᵀ * Sinf * embM n₁ na nm = 0 := by
    rw [Matrix.mul_assoc, hcolM, Matrix.mul_zero]
  have hz2 : (embA n₁ na nm)ᵀ * Sinf * embM n₁ na nm = 0 := by
    rw [Matrix.mul_assoc, hcolM, Matrix.mul_zero]
  have hz3 : (embM n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm = 0 := by
    rw [hrowM, Matrix.zero_mul]
  have hz4 : (embM n₁ na nm)ᵀ * Sinf * embA n₁ na nm = 0 := by
    rw [hrowM, Matrix.zero_mul]
  have hz5 : (embM n₁ na nm)ᵀ * Sinf * embM n₁ na nm = 0 := by
    rw [hrowM, Matrix.zero_mul]
  -- the cancel identities
  have hc1 : infLam Sinf * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
      = (emb1 n₁ na nm)ᵀ * Sinf * embA n₁ na nm := by
    unfold infLam
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSaaU,
      Matrix.mul_one]
  have hc2 : (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm
        * (infLam Sinf)ᵀ
      = (embA n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm := by
    unfold infLam
    rw [Matrix.transpose_mul, Matrix.transpose_nonsing_inv, hSaaSym,
      hS1at, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hSaaU, Matrix.one_mul]
  have hc3 : infLam Sinf
        * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
        * (infLam Sinf)ᵀ
      = (emb1 n₁ na nm)ᵀ * Sinf * embA n₁ na nm
        * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹
        * ((embA n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm) := by
    rw [Matrix.mul_assoc (infLam Sinf), hc2]
    unfold infLam
    rw [Matrix.mul_assoc]
  -- assemble
  have hV0 : condV (infLam Sinf) (0 : Matrix (Fin nm) (Fin na) ℝ)
      = emb1 n₁ na nm * infLam Sinf + embA n₁ na nm := by
    unfold condV
    rw [Matrix.mul_zero, add_zero]
  rw [hV0]
  calc Sinf
      = emb1 n₁ na nm * ((emb1 n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm)
          * (emb1 n₁ na nm)ᵀ
        + emb1 n₁ na nm * ((emb1 n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
          * (embA n₁ na nm)ᵀ
        + embA n₁ na nm * ((embA n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm)
          * (emb1 n₁ na nm)ᵀ
        + embA n₁ na nm * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
          * (embA n₁ na nm)ᵀ := by
        have h := partition3_decomp Sinf
        rw [hz1, hz2, hz3, hz4, hz5] at h
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero] at h
        conv_lhs => rw [h]
  _ = emb1 n₁ na nm * infP Sinf * (emb1 n₁ na nm)ᵀ
      + (emb1 n₁ na nm * infLam Sinf + embA n₁ na nm)
        * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
        * (emb1 n₁ na nm * infLam Sinf + embA n₁ na nm)ᵀ := by
      rw [Matrix.transpose_add, Matrix.transpose_mul]
      simp only [Matrix.add_mul, Matrix.mul_add]
      rw [show emb1 n₁ na nm * infLam Sinf
            * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
            * ((infLam Sinf)ᵀ * (emb1 n₁ na nm)ᵀ)
          = emb1 n₁ na nm * (infLam Sinf
              * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
              * (infLam Sinf)ᵀ) * (emb1 n₁ na nm)ᵀ by
        simp only [Matrix.mul_assoc], hc3]
      rw [show emb1 n₁ na nm * infLam Sinf
            * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
            * (embA n₁ na nm)ᵀ
          = emb1 n₁ na nm * (infLam Sinf
              * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm))
            * (embA n₁ na nm)ᵀ by
        simp only [Matrix.mul_assoc], hc1]
      rw [show embA n₁ na nm
            * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
            * ((infLam Sinf)ᵀ * (emb1 n₁ na nm)ᵀ)
          = embA n₁ na nm
            * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm
              * (infLam Sinf)ᵀ) * (emb1 n₁ na nm)ᵀ by
        simp only [Matrix.mul_assoc], hc2]
      unfold infP
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      abel

lemma infP_posSemidef (hS : S.IsStrongSolution Sinf) :
    (infP Sinf).PosSemidef := by
  unfold infP
  exact schur_compl_posSemidef hS.posSemidef _ _
    (S.strong_corner_posDef hS)

/-- The strong solution's chart. -/
noncomputable def infChart (hC1 : S.C1) (hS : S.IsStrongSolution Sinf) :
    CondChart Sinf where
  P := infP Sinf
  Λ1a := infLam Sinf
  Λma := 0
  Saa := (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm
  hP := S.infP_posSemidef hS
  hSaa := S.strong_corner_posDef hS
  decomp := S.strong_decomp hC1 hS

/-- **The chart fixed-point identities at the strong solution**
(limit identification for `lem:condfilter`-3, `lem:jtransform`,
`eq:J1-home`): the strong data are fixed by the chart map. -/
theorem strong_chart_fixed (hC1 : S.C1)
    (hS : S.IsStrongSolution Sinf) :
    S.Aa * S.uhatOf (infP Sinf) (infLam Sinf) 0
        ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm) * S.Aaᵀ
      = (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm
    ∧ S.lamNext (infP Sinf) (infLam Sinf) 0 = infLam Sinf
    ∧ dareStep S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ) (infP Sinf)
      = infP Sinf := by
  have hcornerPD := S.strong_corner_posDef hS
  have hcornerU : IsUnit ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hcornerPD.isUnit
  have hstep := S.chart_dareStep (S.infChart hC1 hS)
  dsimp only [infChart] at hstep
  rw [hS.fixed] at hstep
  rw [show S.Am * (0 : Matrix (Fin nm) (Fin na) ℝ) * S.Aa⁻¹ = 0 by
    rw [Matrix.mul_zero, Matrix.zero_mul]] at hstep
  have hUPD : (S.Aa * S.uhatOf (infP Sinf) (infLam Sinf) 0
      ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm) * S.Aaᵀ).PosDef := by
    have hU := S.uhatOf_posDef (S.infP_posSemidef hS) (infLam Sinf) 0
      hcornerPD
    have h := hU.mul_mul_conjTranspose_same (B := S.Aa)
      S.Aa_vecMul_injective
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hP2 : (dareStep S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ)
      (infP Sinf)).PosSemidef :=
    dareStep_posSemidef S.hR S.redQ_posSemidef (S.infP_posSemidef hS)
  have hSaa2 := CondChart.extract_Saa
    (⟨_, _, _, _, hP2, hUPD, hstep⟩ : CondChart Sinf)
  have h1a2 := CondChart.extract_1a
    (⟨_, _, _, _, hP2, hUPD, hstep⟩ : CondChart Sinf)
  have h11_2 := CondChart.extract_11
    (⟨_, _, _, _, hP2, hUPD, hstep⟩ : CondChart Sinf)
  have hSaa1 := CondChart.extract_Saa (S.infChart hC1 hS)
  have h1a1 := CondChart.extract_1a (S.infChart hC1 hS)
  have h11_1 := CondChart.extract_11 (S.infChart hC1 hS)
  dsimp only [infChart] at hSaa1 h1a1 h11_1
  dsimp only at hSaa2 h1a2 h11_2
  -- (i) the antistable corner is fixed
  have hi : S.Aa * S.uhatOf (infP Sinf) (infLam Sinf) 0
      ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm) * S.Aaᵀ
      = (embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm := hSaa2.symm
  -- (ii) the loading is fixed: cancel the invertible corner
  have hii : S.lamNext (infP Sinf) (infLam Sinf) 0 = infLam Sinf := by
    have h := h1a2
    rw [hi] at h
    rw [h1a1] at h
    -- h : infLam * corner = lamNext * corner
    have h2 := congrArg
      (fun X => X * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)⁻¹) h
    dsimp only at h2
    rw [Matrix.mul_assoc (infLam Sinf)
        ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm) _,
      Matrix.mul_assoc (S.lamNext (infP Sinf) (infLam Sinf) 0)
        ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm) _,
      Matrix.mul_nonsing_inv _ hcornerU, Matrix.mul_one,
      Matrix.mul_one] at h2
    exact h2.symm
  -- (iii) the conditional block is fixed
  have hiii : dareStep S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ)
      (infP Sinf) = infP Sinf := by
    have h := h11_2
    rw [hi, hii, h11_1] at h
    -- h : infP + infLam*corner*infLamᵀ = dareStep-red + infLam*corner*infLamᵀ
    have h2 := congrArg
      (fun X => X - infLam Sinf
        * ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
        * (infLam Sinf)ᵀ) h
    dsimp only at h2
    rw [add_sub_cancel_right, add_sub_cancel_right] at h2
    exact h2.symm
  exact ⟨hi, hii, hiii⟩

end DareSystem

end Dare
end Estimation
