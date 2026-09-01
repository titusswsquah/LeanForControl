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

/-! ### Analysis helpers -/

/-- A null real sequence is bounded above. -/
lemma exists_bound_of_tendsto_zero {f : ℕ → ℝ}
    (hf : Tendsto f atTop (nhds 0)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n, f n ≤ B := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hf.eventually_lt_const one_pos)
  refine ⟨max 1 (∑ i ∈ Finset.range (N + 1), |f i|),
    le_trans zero_le_one (le_max_left _ _), fun n => ?_⟩
  rcases Nat.le_total n N with h | h
  · calc f n ≤ |f n| := le_abs_self _
    _ ≤ ∑ i ∈ Finset.range (N + 1), |f i| :=
        Finset.single_le_sum (f := fun i => |f i|)
          (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))
    _ ≤ max 1 (∑ i ∈ Finset.range (N + 1), |f i|) := le_max_right _ _
  · exact le_trans (hN n h).le (le_max_left _ _)

/-- Norm-convergent matrix sequences multiply. -/
lemma tendsto_matmul {ι κ σ : Type*} [Fintype ι] [Fintype κ] [Fintype σ]
    {X : ℕ → Matrix ι κ ℝ} {Y : ℕ → Matrix κ σ ℝ}
    {Xl : Matrix ι κ ℝ} {Yl : Matrix κ σ ℝ}
    (hX : Tendsto (fun T => ‖X T - Xl‖) atTop (nhds 0))
    (hY : Tendsto (fun T => ‖Y T - Yl‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖X T * Y T - Xl * Yl‖) atTop (nhds 0) := by
  obtain ⟨B, hB0, hB⟩ := exists_bound_of_tendsto_zero hY
  have hb : ∀ T, ‖X T * Y T - Xl * Yl‖
      ≤ ‖X T - Xl‖ * (B + ‖Yl‖) + ‖Xl‖ * ‖Y T - Yl‖ := by
    intro T
    have hid : X T * Y T - Xl * Yl
        = (X T - Xl) * Y T + Xl * (Y T - Yl) := by
      rw [Matrix.sub_mul, Matrix.mul_sub]
      abel
    have hYb : ‖Y T‖ ≤ B + ‖Yl‖ := by
      calc ‖Y T‖ = ‖Y T - Yl + Yl‖ := by rw [sub_add_cancel]
      _ ≤ ‖Y T - Yl‖ + ‖Yl‖ := norm_add_le _ _
      _ ≤ B + ‖Yl‖ := by linarith [hB T]
    calc ‖X T * Y T - Xl * Yl‖
        = ‖(X T - Xl) * Y T + Xl * (Y T - Yl)‖ := by rw [hid]
    _ ≤ ‖(X T - Xl) * Y T‖ + ‖Xl * (Y T - Yl)‖ := norm_add_le _ _
    _ ≤ ‖X T - Xl‖ * ‖Y T‖ + ‖Xl‖ * ‖Y T - Yl‖ := by
        refine add_le_add (Matrix.linfty_opNorm_mul _ _)
          (Matrix.linfty_opNorm_mul _ _)
    _ ≤ ‖X T - Xl‖ * (B + ‖Yl‖) + ‖Xl‖ * ‖Y T - Yl‖ := by
        refine add_le_add ?_ le_rfl
        exact mul_le_mul_of_nonneg_left hYb (norm_nonneg _)
  refine squeeze_zero (fun T => norm_nonneg _) hb ?_
  have h1 := hX.mul_const (B + ‖Yl‖)
  have h2 := hY.const_mul ‖Xl‖
  have h3 := h1.add h2
  simpa using h3

/-- Norm-convergent matrix sequences add. -/
lemma tendsto_matadd {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X Y : ℕ → Matrix ι κ ℝ} {Xl Yl : Matrix ι κ ℝ}
    (hX : Tendsto (fun T => ‖X T - Xl‖) atTop (nhds 0))
    (hY : Tendsto (fun T => ‖Y T - Yl‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖X T + Y T - (Xl + Yl)‖) atTop (nhds 0) := by
  have hb : ∀ T, ‖X T + Y T - (Xl + Yl)‖
      ≤ ‖X T - Xl‖ + ‖Y T - Yl‖ := by
    intro T
    calc ‖X T + Y T - (Xl + Yl)‖
        = ‖(X T - Xl) + (Y T - Yl)‖ := by
          congr 1
          abel
    _ ≤ ‖X T - Xl‖ + ‖Y T - Yl‖ := norm_add_le _ _
  refine squeeze_zero (fun T => norm_nonneg _) hb ?_
  simpa using hX.add hY

/-- Norm-convergent matrix sequences subtract. -/
lemma tendsto_matsub {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X Y : ℕ → Matrix ι κ ℝ} {Xl Yl : Matrix ι κ ℝ}
    (hX : Tendsto (fun T => ‖X T - Xl‖) atTop (nhds 0))
    (hY : Tendsto (fun T => ‖Y T - Yl‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖X T - Y T - (Xl - Yl)‖) atTop (nhds 0) := by
  have hb : ∀ T, ‖X T - Y T - (Xl - Yl)‖
      ≤ ‖X T - Xl‖ + ‖Y T - Yl‖ := by
    intro T
    calc ‖X T - Y T - (Xl - Yl)‖
        = ‖(X T - Xl) - (Y T - Yl)‖ := by
          congr 1
          abel
    _ ≤ ‖X T - Xl‖ + ‖Y T - Yl‖ := norm_sub_le _ _
  refine squeeze_zero (fun T => norm_nonneg _) hb ?_
  simpa using hX.add hY

/-- A constant sequence norm-converges to itself. -/
lemma tendsto_matconst {ι κ : Type*} [Fintype ι] [Fintype κ]
    (C : Matrix ι κ ℝ) :
    Tendsto (fun _ : ℕ => ‖C - C‖) atTop (nhds 0) := by
  simp only [sub_self, norm_zero]
  exact tendsto_const_nhds

/-- Transposes of a norm-convergent sequence converge. -/
lemma tendsto_mattrans {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] {X : ℕ → Matrix ι κ ℝ} {Xl : Matrix ι κ ℝ}
    (hX : Tendsto (fun T => ‖X T - Xl‖) atTop (nhds 0)) :
    Tendsto (fun T => ‖(X T)ᵀ - Xlᵀ‖) atTop (nhds 0) := by
  have hb : ∀ T, ‖(X T)ᵀ - Xlᵀ‖
      ≤ (Fintype.card ι : ℝ) * ‖X T - Xl‖ := by
    intro T
    rw [← Matrix.transpose_sub]
    exact linfty_opNorm_transpose_le' _
  refine squeeze_zero (fun T => norm_nonneg _) hb ?_
  simpa using hX.const_mul (Fintype.card ι : ℝ)

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-! ### The reduced closed loop and its products -/

/-- The conditional-filter closed loop `L_T = A₁(I − K_T C₁)`
(`eq:condgain`). -/
noncomputable def redL (T : ℕ) : Matrix (Fin n₁) (Fin n₁) ℝ :=
  errMap S.C₁ S.R S.A₁ (S.redP T)

/-- The transition products `Φ(j, k) = L_{j+k-1}⋯L_j` (newest factor
first). -/
noncomputable def redProdF (j : ℕ) : ℕ → Matrix (Fin n₁) (Fin n₁) ℝ
  | 0 => 1
  | k + 1 => S.redL (j + k) * redProdF j k

/-- **The deck's `fact:dare-strong` import on the reduced `e₁`
system** (`lem:condfilter`-1's analytic content): the zero-seed
conditional Riccati converges to the strong solution's conditional
block, and the closed-loop transition products are uniformly
bounded (`fact:schur-decay` on the asymptotically Schur loop). -/
structure ReducedImport (S : DareSystem n₁ na nm m p)
    (Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) : Prop where
  Ptendsto : Tendsto (fun T => ‖S.redP T - infP Sinf‖) atTop (nhds 0)
  prodBound : ∃ cL : ℝ, 0 ≤ cL ∧ ∀ j k : ℕ, ‖S.redProdF j k‖ ≤ cL

/-- The loading drive (`eq:cf-rec`'s `d_T`). -/
noncomputable def dOf (P : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Λm : Matrix (Fin nm) (Fin na) ℝ) : Matrix (Fin n₁) (Fin na) ℝ :=
  (S.A₁₂ * ea2 na nm + S.A₁₂ * em2 na nm * Λm
    - S.A₁ * kGain S.C₁ S.R P
      * (S.fullC * embA n₁ na nm + S.fullC * embM n₁ na nm * Λm))
    * S.Aa⁻¹

/-- `eq:cf-rec` in closed-loop-plus-drive form. -/
lemma lamNext_eq (P : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Λ : Matrix (Fin n₁) (Fin na) ℝ)
    (Λm : Matrix (Fin nm) (Fin na) ℝ) :
    S.lamNext P Λ Λm
      = errMap S.C₁ S.R S.A₁ P * Λ * S.Aa⁻¹ + S.dOf P Λm := by
  unfold lamNext lamHat dOf ceff errMap kGain
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul,
    Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  abel

/-- The loading recursion along the run (`eq:cf-rec`). -/
lemma lowLam1a_rec (T : ℕ) :
    S.lowLam1a (T + 1)
      = S.redL T * S.lowLam1a T * S.Aa⁻¹
        + S.dOf (S.redP T) (S.lowLamma T) := by
  show S.lamNext (S.redP T) (S.lowLam1a T) (S.lowLamma T) = _
  rw [S.lamNext_eq]
  rfl

/-- Unrolling a time-varying loading recursion against the products. -/
lemma lam_unroll {x d : ℕ → Matrix (Fin n₁) (Fin na) ℝ}
    (hrec : ∀ T, x (T + 1) = S.redL T * x T * S.Aa⁻¹ + d T) :
    ∀ T, x T = S.redProdF 0 T * x 0 * (S.Aa⁻¹) ^ T
      + ∑ j ∈ Finset.range T,
          S.redProdF (j + 1) (T - 1 - j) * d j
            * (S.Aa⁻¹) ^ (T - 1 - j) := by
  intro T
  induction T with
  | zero => simp [redProdF]
  | succ T ih =>
    rw [hrec T, ih]
    have h1 : S.redL T * (S.redProdF 0 T * x 0 * (S.Aa⁻¹) ^ T)
          * S.Aa⁻¹
        = S.redProdF 0 (T + 1) * x 0 * (S.Aa⁻¹) ^ (T + 1) := by
      rw [show S.redProdF 0 (T + 1)
          = S.redL (0 + T) * S.redProdF 0 T from rfl,
        Nat.zero_add, pow_succ]
      simp only [Matrix.mul_assoc]
    have h2 : S.redL T * (∑ j ∈ Finset.range T,
          S.redProdF (j + 1) (T - 1 - j) * d j
            * (S.Aa⁻¹) ^ (T - 1 - j)) * S.Aa⁻¹
        = ∑ j ∈ Finset.range T,
            S.redProdF (j + 1) (T - j) * d j * (S.Aa⁻¹) ^ (T - j) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjT := Finset.mem_range.mp hj
      have hprod : S.redL T * S.redProdF (j + 1) (T - 1 - j)
          = S.redProdF (j + 1) (T - j) := by
        rw [show T - j = (T - 1 - j) + 1 by omega,
          show S.redProdF (j + 1) ((T - 1 - j) + 1)
            = S.redL (j + 1 + (T - 1 - j))
              * S.redProdF (j + 1) (T - 1 - j) from rfl,
          show j + 1 + (T - 1 - j) = T by omega]
      have hpow : (S.Aa⁻¹) ^ (T - 1 - j) * S.Aa⁻¹
          = (S.Aa⁻¹) ^ (T - j) := by
        rw [← pow_succ, show T - 1 - j + 1 = T - j by omega]
      rw [← hprod, ← hpow]
      simp only [Matrix.mul_assoc]
    have h3 : ∑ j ∈ Finset.range (T + 1),
          S.redProdF (j + 1) (T + 1 - 1 - j) * d j
            * (S.Aa⁻¹) ^ (T + 1 - 1 - j)
        = (∑ j ∈ Finset.range T,
            S.redProdF (j + 1) (T - j) * d j * (S.Aa⁻¹) ^ (T - j))
          + d T := by
      have hsimp : ∀ j, T + 1 - 1 - j = T - j := fun j => by omega
      simp only [hsimp]
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, pow_zero,
        show S.redProdF (T + 1) 0 = 1 from rfl, Matrix.one_mul,
        Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2, h3]
    abel

end DareSystem

/-- Unrolling a constant-coefficient conjugation recursion. -/
lemma conj_unroll {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    {L : Matrix ι ι ℝ} {B : Matrix κ κ ℝ} {e η : ℕ → Matrix ι κ ℝ}
    (hrec : ∀ T, e (T + 1) = L * e T * B + η T) :
    ∀ T, e T = L ^ T * e 0 * B ^ T
      + ∑ j ∈ Finset.range T,
          L ^ (T - 1 - j) * η j * B ^ (T - 1 - j) := by
  intro T
  induction T with
  | zero => simp
  | succ T ih =>
    rw [hrec T, ih]
    have h1 : L * (L ^ T * e 0 * B ^ T) * B
        = L ^ (T + 1) * e 0 * B ^ (T + 1) := by
      rw [pow_succ' L T, pow_succ B T]
      simp only [Matrix.mul_assoc]
    have h2 : L * (∑ j ∈ Finset.range T,
          L ^ (T - 1 - j) * η j * B ^ (T - 1 - j)) * B
        = ∑ j ∈ Finset.range T,
            L ^ (T - j) * η j * B ^ (T - j) := by
      simp only [Matrix.mul_sum, Matrix.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjT := Finset.mem_range.mp hj
      have hL : L * L ^ (T - 1 - j) = L ^ (T - j) := by
        rw [← pow_succ' L (T - 1 - j), show T - 1 - j + 1 = T - j
          by omega]
      have hB : B ^ (T - 1 - j) * B = B ^ (T - j) := by
        rw [← pow_succ, show T - 1 - j + 1 = T - j by omega]
      rw [← hL, ← hB]
      simp only [Matrix.mul_assoc]
    have h3 : ∑ j ∈ Finset.range (T + 1),
          L ^ (T + 1 - 1 - j) * η j * B ^ (T + 1 - 1 - j)
        = (∑ j ∈ Finset.range T, L ^ (T - j) * η j * B ^ (T - j))
          + η T := by
      have hsimp : ∀ j, T + 1 - 1 - j = T - j := fun j => by omega
      simp only [hsimp]
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, pow_zero, Matrix.one_mul,
        Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, h1, h2, h3]
    abel

namespace DareSystem

variable {n₁' na' nm' m' p' : ℕ}

end DareSystem

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)
variable {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-- Uniform norm bound on the reduced innovation inverse
(`S̃ ⪰ R`, Löwner inversion). -/
lemma redInnov_inv_norm_bound : ∃ bR : ℝ, 0 ≤ bR ∧
    ∀ (P : Matrix (Fin n₁) (Fin n₁) ℝ), P.PosSemidef →
      ‖(innov S.C₁ S.R P)⁻¹‖ ≤ bR := by
  obtain ⟨cRi, hcRi, hcRile⟩ := exists_quadForm_le S.R⁻¹
  refine ⟨(Fintype.card (Fin p) : ℝ) ^ 2 * cRi, by positivity,
    fun P hP => ?_⟩
  have hSt : (innov S.C₁ S.R P).PosDef := innov_posDef S.hR hP
  have hdiff : (innov S.C₁ S.R P - S.R).PosSemidef := by
    have h1 : innov S.C₁ S.R P - S.R = S.C₁ * P * S.C₁ᵀ := by
      unfold innov
      abel
    rw [h1]
    have h := hP.mul_mul_conjTranspose_same S.C₁
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hinv := posSemidef_inv_sub_inv S.hR hSt hdiff
  have hq : ∀ x, quadForm (innov S.C₁ S.R P)⁻¹ x ≤ cRi * ‖x‖ ^ 2 := by
    intro x
    have h1 := quadForm_le_quadForm_of_posSemidef_sub hinv x
    linarith [hcRile x]
  exact posSemidef_norm_le_of_quadForm_le hSt.inv.posSemidef hcRi.le hq

set_option maxHeartbeats 1000000 in
/-- **`lem:condfilter`-3, verified** (modulo the `fact:dare-strong`
import): the conditional-filter loading converges to the strong
solution's loading, through the perturbed Stein recursion against the
Schur `Aₐ⁻¹` with uniformly bounded closed-loop products. -/
theorem lowLam1a_tendsto (hC1 : S.C1) (hS : S.IsStrongSolution Sinf)
    (himp : S.ReducedImport Sinf)
    {cm : ℝ} (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    Tendsto (fun T => ‖S.lowLam1a T - infLam Sinf‖) atTop (nhds 0) := by
  obtain ⟨cL, hcL, hcLb⟩ := himp.prodBound
  obtain ⟨ca, γ, hca, hγ0, hγ1, hApow⟩ :=
    S.Aa_inv_isSchurStable.exists_pow_norm_le
  have hP := himp.Ptendsto
  obtain ⟨bR, hbR, hbRb⟩ := S.redInnov_inv_norm_bound
  -- the reduced innovation converges
  have hStil : Tendsto (fun T => ‖innov S.C₁ S.R (S.redP T)
      - innov S.C₁ S.R (infP Sinf)‖) atTop (nhds 0) := by
    have hb : ∀ T, ‖innov S.C₁ S.R (S.redP T)
        - innov S.C₁ S.R (infP Sinf)‖
        ≤ ‖S.C₁‖ * ‖S.redP T - infP Sinf‖ * ‖S.C₁ᵀ‖ := by
      intro T
      have hid : innov S.C₁ S.R (S.redP T)
          - innov S.C₁ S.R (infP Sinf)
          = S.C₁ * (S.redP T - infP Sinf) * S.C₁ᵀ := by
        unfold innov
        rw [Matrix.mul_sub, Matrix.sub_mul]
        abel
      rw [hid]
      exact norm_triple_le _ _ _
    refine squeeze_zero (fun T => norm_nonneg _) hb ?_
    have h := (hP.const_mul ‖S.C₁‖).mul_const ‖S.C₁ᵀ‖
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  -- and so does its inverse
  have hinfPD : (innov S.C₁ S.R (infP Sinf)).PosDef :=
    innov_posDef S.hR (S.infP_posSemidef hS)
  have hStilInv : Tendsto (fun T => ‖(innov S.C₁ S.R (S.redP T))⁻¹
      - (innov S.C₁ S.R (infP Sinf))⁻¹‖) atTop (nhds 0) := by
    have hb : ∀ T, ‖(innov S.C₁ S.R (S.redP T))⁻¹
        - (innov S.C₁ S.R (infP Sinf))⁻¹‖
        ≤ bR * ‖innov S.C₁ S.R (S.redP T)
            - innov S.C₁ S.R (infP Sinf)‖
          * ‖(innov S.C₁ S.R (infP Sinf))⁻¹‖ := by
      intro T
      have hTPD : (innov S.C₁ S.R (S.redP T)).PosDef :=
        innov_posDef S.hR (S.redP_posSemidef T)
      have hid : (innov S.C₁ S.R (S.redP T))⁻¹
          - (innov S.C₁ S.R (infP Sinf))⁻¹
          = (innov S.C₁ S.R (S.redP T))⁻¹
            * (innov S.C₁ S.R (infP Sinf)
              - innov S.C₁ S.R (S.redP T))
            * (innov S.C₁ S.R (infP Sinf))⁻¹ := by
        have h1 : (innov S.C₁ S.R (S.redP T))⁻¹
            * (innov S.C₁ S.R (infP Sinf)
              - innov S.C₁ S.R (S.redP T))
            * (innov S.C₁ S.R (infP Sinf))⁻¹
            = (innov S.C₁ S.R (S.redP T))⁻¹
                * (innov S.C₁ S.R (infP Sinf)
                  * (innov S.C₁ S.R (infP Sinf))⁻¹)
              - (innov S.C₁ S.R (S.redP T))⁻¹
                  * innov S.C₁ S.R (S.redP T)
                  * (innov S.C₁ S.R (infP Sinf))⁻¹ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          simp only [Matrix.mul_assoc]
        rw [h1, Matrix.mul_nonsing_inv _
            ((Matrix.isUnit_iff_isUnit_det _).mp hinfPD.isUnit),
          Matrix.nonsing_inv_mul _
            ((Matrix.isUnit_iff_isUnit_det _).mp hTPD.isUnit),
          Matrix.mul_one, Matrix.one_mul]
      rw [hid]
      calc ‖(innov S.C₁ S.R (S.redP T))⁻¹
            * (innov S.C₁ S.R (infP Sinf)
              - innov S.C₁ S.R (S.redP T))
            * (innov S.C₁ S.R (infP Sinf))⁻¹‖
          ≤ ‖(innov S.C₁ S.R (S.redP T))⁻¹‖
            * ‖innov S.C₁ S.R (infP Sinf)
                - innov S.C₁ S.R (S.redP T)‖
            * ‖(innov S.C₁ S.R (infP Sinf))⁻¹‖ := norm_triple_le _ _ _
      _ ≤ bR * ‖innov S.C₁ S.R (S.redP T)
              - innov S.C₁ S.R (infP Sinf)‖
            * ‖(innov S.C₁ S.R (infP Sinf))⁻¹‖ := by
          rw [norm_sub_rev]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (hbRb _ (S.redP_posSemidef T)) (norm_nonneg _)
    refine squeeze_zero (fun T => norm_nonneg _) hb ?_
    have h := (hStil.const_mul bR).mul_const
      ‖(innov S.C₁ S.R (infP Sinf))⁻¹‖
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  -- gain continuity
  have hK : Tendsto (fun T => ‖kGain S.C₁ S.R (S.redP T)
      - kGain S.C₁ S.R (infP Sinf)‖) atTop (nhds 0) := by
    have h1 := tendsto_matmul (tendsto_matmul hP
      (tendsto_matconst S.C₁ᵀ)) hStilInv
    exact h1
  -- closed-loop continuity
  have hL : Tendsto (fun T => ‖S.redL T
      - errMap S.C₁ S.R S.A₁ (infP Sinf)‖) atTop (nhds 0) := by
    have hb : ∀ T, ‖S.redL T - errMap S.C₁ S.R S.A₁ (infP Sinf)‖
        ≤ ‖S.A₁‖ * ‖kGain S.C₁ S.R (S.redP T)
            - kGain S.C₁ S.R (infP Sinf)‖ * ‖S.C₁‖ := by
      intro T
      have hid : S.redL T - errMap S.C₁ S.R S.A₁ (infP Sinf)
          = S.A₁ * (kGain S.C₁ S.R (infP Sinf)
              - kGain S.C₁ S.R (S.redP T)) * S.C₁ := by
        unfold redL errMap
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
          Matrix.mul_assoc]
        abel
      rw [hid]
      calc ‖S.A₁ * (kGain S.C₁ S.R (infP Sinf)
            - kGain S.C₁ S.R (S.redP T)) * S.C₁‖
          ≤ ‖S.A₁‖ * ‖kGain S.C₁ S.R (infP Sinf)
              - kGain S.C₁ S.R (S.redP T)‖ * ‖S.C₁‖ :=
            norm_triple_le _ _ _
      _ = ‖S.A₁‖ * ‖kGain S.C₁ S.R (S.redP T)
              - kGain S.C₁ S.R (infP Sinf)‖ * ‖S.C₁‖ := by
          rw [norm_sub_rev]
    refine squeeze_zero (fun T => norm_nonneg _) hb ?_
    have h := (hK.const_mul ‖S.A₁‖).mul_const ‖S.C₁‖
    simpa [mul_comm, mul_assoc, mul_left_comm] using h
  -- the marginal loading dies
  have hLm : Tendsto (fun T => ‖S.lowLamma T
      - (0 : Matrix (Fin nm) (Fin na) ℝ)‖) atTop (nhds 0) := by
    simp only [sub_zero]
    exact S.loading_tendsto S.lam0 hPB
  -- the drive converges
  have hd : Tendsto (fun T => ‖S.dOf (S.redP T) (S.lowLamma T)
      - S.dOf (infP Sinf) 0‖) atTop (nhds 0) := by
    unfold dOf
    have h1 : Tendsto (fun T => ‖S.A₁₂ * em2 na nm * S.lowLamma T
        - S.A₁₂ * em2 na nm * (0 : Matrix (Fin nm) (Fin na) ℝ)‖)
        atTop (nhds 0) :=
      tendsto_matmul (tendsto_matconst (S.A₁₂ * em2 na nm)) hLm
    have h2 : Tendsto (fun T =>
        ‖S.A₁₂ * ea2 na nm + S.A₁₂ * em2 na nm * S.lowLamma T
          - (S.A₁₂ * ea2 na nm + S.A₁₂ * em2 na nm
            * (0 : Matrix (Fin nm) (Fin na) ℝ))‖)
        atTop (nhds 0) :=
      tendsto_matadd (tendsto_matconst (S.A₁₂ * ea2 na nm)) h1
    have h3 : Tendsto (fun T =>
        ‖S.fullC * embM n₁ na nm * S.lowLamma T
          - S.fullC * embM n₁ na nm
              * (0 : Matrix (Fin nm) (Fin na) ℝ)‖) atTop (nhds 0) :=
      tendsto_matmul (tendsto_matconst (S.fullC * embM n₁ na nm)) hLm
    have h4 : Tendsto (fun T =>
        ‖S.fullC * embA n₁ na nm
            + S.fullC * embM n₁ na nm * S.lowLamma T
          - (S.fullC * embA n₁ na nm
            + S.fullC * embM n₁ na nm
              * (0 : Matrix (Fin nm) (Fin na) ℝ))‖) atTop (nhds 0) :=
      tendsto_matadd (tendsto_matconst (S.fullC * embA n₁ na nm)) h3
    have h5 : Tendsto (fun T =>
        ‖S.A₁ * kGain S.C₁ S.R (S.redP T)
          - S.A₁ * kGain S.C₁ S.R (infP Sinf)‖) atTop (nhds 0) :=
      tendsto_matmul (tendsto_matconst S.A₁) hK
    have h6 : Tendsto (fun T =>
        ‖S.A₁ * kGain S.C₁ S.R (S.redP T)
            * (S.fullC * embA n₁ na nm
              + S.fullC * embM n₁ na nm * S.lowLamma T)
          - S.A₁ * kGain S.C₁ S.R (infP Sinf)
            * (S.fullC * embA n₁ na nm
              + S.fullC * embM n₁ na nm
                * (0 : Matrix (Fin nm) (Fin na) ℝ))‖) atTop (nhds 0) :=
      tendsto_matmul h5 h4
    have h7 : Tendsto (fun T =>
        ‖S.A₁₂ * ea2 na nm + S.A₁₂ * em2 na nm * S.lowLamma T
            - S.A₁ * kGain S.C₁ S.R (S.redP T)
              * (S.fullC * embA n₁ na nm
                + S.fullC * embM n₁ na nm * S.lowLamma T)
          - (S.A₁₂ * ea2 na nm + S.A₁₂ * em2 na nm
              * (0 : Matrix (Fin nm) (Fin na) ℝ)
            - S.A₁ * kGain S.C₁ S.R (infP Sinf)
              * (S.fullC * embA n₁ na nm
                + S.fullC * embM n₁ na nm
                  * (0 : Matrix (Fin nm) (Fin na) ℝ)))‖)
        atTop (nhds 0) :=
      tendsto_matsub h2 h6
    exact tendsto_matmul h7 (tendsto_matconst S.Aa⁻¹)
  -- the fixed point of the loading recursion
  have hfix' : errMap S.C₁ S.R S.A₁ (infP Sinf) * infLam Sinf * S.Aa⁻¹
      + S.dOf (infP Sinf) 0 = infLam Sinf := by
    rw [← S.lamNext_eq]
    exact (S.strong_chart_fixed hC1 hS).2.1
  -- the error recursion
  have herec : ∀ T, (fun T => S.lowLam1a T - infLam Sinf) (T + 1)
      = S.redL T * (fun T => S.lowLam1a T - infLam Sinf) T * S.Aa⁻¹
        + (fun T => S.redL T * infLam Sinf * S.Aa⁻¹
            + S.dOf (S.redP T) (S.lowLamma T) - infLam Sinf) T := by
    intro T
    dsimp only
    rw [S.lowLam1a_rec T]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  -- the perturbation dies
  have hεt : Tendsto (fun T => ‖S.redL T * infLam Sinf * S.Aa⁻¹
      + S.dOf (S.redP T) (S.lowLamma T) - infLam Sinf‖) atTop
      (nhds 0) := by
    have hb : ∀ T, S.redL T * infLam Sinf * S.Aa⁻¹
        + S.dOf (S.redP T) (S.lowLamma T) - infLam Sinf
        = S.redL T * infLam Sinf * S.Aa⁻¹
            + S.dOf (S.redP T) (S.lowLamma T)
          - (errMap S.C₁ S.R S.A₁ (infP Sinf) * infLam Sinf * S.Aa⁻¹
            + S.dOf (infP Sinf) 0) := by
      intro T
      rw [hfix']
    simp only [hb]
    exact tendsto_matadd (tendsto_matmul (tendsto_matmul hL
      (tendsto_matconst (infLam Sinf))) (tendsto_matconst S.Aa⁻¹)) hd
  -- unroll and convolve
  have hunroll := S.lam_unroll
    (x := fun T => S.lowLam1a T - infLam Sinf)
    (d := fun T => S.redL T * infLam Sinf * S.Aa⁻¹
      + S.dOf (S.redP T) (S.lowLamma T) - infLam Sinf) herec
  have hbnd : ∀ T, ‖S.lowLam1a T - infLam Sinf‖
      ≤ (cL * ‖S.lowLam1a 0 - infLam Sinf‖ * ca) * γ ^ T
        + ∑ j ∈ Finset.range T, γ ^ (T - 1 - j)
            * (cL * ca * ‖S.redL j * infLam Sinf * S.Aa⁻¹
                + S.dOf (S.redP j) (S.lowLamma j) - infLam Sinf‖) := by
    intro T
    have hu := hunroll T
    dsimp only at hu
    rw [hu]
    refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
    · calc ‖S.redProdF 0 T * (S.lowLam1a 0 - infLam Sinf)
            * (S.Aa⁻¹) ^ T‖
          ≤ ‖S.redProdF 0 T‖ * ‖S.lowLam1a 0 - infLam Sinf‖
            * ‖(S.Aa⁻¹) ^ T‖ := norm_triple_le _ _ _
      _ ≤ cL * ‖S.lowLam1a 0 - infLam Sinf‖ * (ca * γ ^ T) := by
          refine mul_le_mul ?_ (hApow T) (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right (hcLb 0 T) (norm_nonneg _)
      _ = (cL * ‖S.lowLam1a 0 - infLam Sinf‖ * ca) * γ ^ T := by ring
    · refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum
        fun j hj => ?_)
      calc ‖S.redProdF (j + 1) (T - 1 - j)
            * (S.redL j * infLam Sinf * S.Aa⁻¹
              + S.dOf (S.redP j) (S.lowLamma j) - infLam Sinf)
            * (S.Aa⁻¹) ^ (T - 1 - j)‖
          ≤ ‖S.redProdF (j + 1) (T - 1 - j)‖
            * ‖S.redL j * infLam Sinf * S.Aa⁻¹
                + S.dOf (S.redP j) (S.lowLamma j) - infLam Sinf‖
            * ‖(S.Aa⁻¹) ^ (T - 1 - j)‖ := norm_triple_le _ _ _
      _ ≤ cL * ‖S.redL j * infLam Sinf * S.Aa⁻¹
              + S.dOf (S.redP j) (S.lowLamma j) - infLam Sinf‖
            * (ca * γ ^ (T - 1 - j)) := by
          refine mul_le_mul ?_ (hApow _) (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right (hcLb _ _) (norm_nonneg _)
      _ = γ ^ (T - 1 - j)
            * (cL * ca * ‖S.redL j * infLam Sinf * S.Aa⁻¹
                + S.dOf (S.redP j) (S.lowLamma j) - infLam Sinf‖) := by
          ring
  refine tendsto_zero_of_geometric_conv (by positivity) hγ0 hγ1
    (fun T => norm_nonneg _) (fun j => by positivity) ?_ hbnd
  simpa [mul_assoc] using hεt.const_mul (cL * ca)

end DareSystem

end Dare
end Estimation
