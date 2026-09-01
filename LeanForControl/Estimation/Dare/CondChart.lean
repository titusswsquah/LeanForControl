import LeanForControl.Estimation.Dare.Loading
import Architect

/-!
# The conditional chart (`eq:jchart`, `eq:condcov`, machinery for
`lem:condfilter` / `lem:jtransform`)

The slaved lower trajectory is carried by the chart
`(P, Λ₁ₐ, Λₘₐ, Σₐₐ)` through the **conditional decomposition**

`Σ = e₁·P·e₁ᵀ + V·Σₐₐ·Vᵀ`, `V := e₁·Λ₁ₐ + eₐ + eₘ·Λₘₐ`

(the deck's regression `M = [I Λ₁ₐ; 0 I; 0 Λₘₐ]` with uncorrelated
`(e, xₐ)` of covariance `blkdiag(P, Σₐₐ)`). This file provides the
embeddings and their multiplication table, the three-way partition of
the identity, the chart structure, and chart extraction.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The inclusion of the stabilizable coordinates `e₁`. -/
def emb1 (n₁ na nm : ℕ) : Matrix (ix n₁ na nm) (Fin n₁) ℝ :=
  Matrix.fromRows 1 0

/-! ### The embedding multiplication table -/

lemma emb1_transpose_mul {κ : Type*} (M : Matrix (ix n₁ na nm) κ ℝ) :
    (emb1 n₁ na nm)ᵀ * M = Matrix.of fun i k => M (Sum.inl i) k := by
  ext i k
  unfold emb1
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.transpose_apply, Matrix.one_apply, Finset.sum_ite_eq']

lemma mul_emb1 {κ : Type*} [Fintype κ] (M : Matrix κ (ix n₁ na nm) ℝ) :
    M * emb1 n₁ na nm = Matrix.of fun k j => M k (Sum.inl j) := by
  ext k j
  unfold emb1
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.one_apply]

lemma mul_embA {κ : Type*} [Fintype κ] (M : Matrix κ (ix n₁ na nm) ℝ) :
    M * embA n₁ na nm
      = Matrix.of fun k j => M k (Sum.inr (Sum.inl j)) := by
  ext k j
  unfold embA
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.one_apply]

lemma mul_embM {κ : Type*} [Fintype κ] (M : Matrix κ (ix n₁ na nm) ℝ) :
    M * embM n₁ na nm
      = Matrix.of fun k j => M k (Sum.inr (Sum.inr j)) := by
  ext k j
  unfold embM
  simp [Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
    Matrix.one_apply]

lemma emb1t_mul_emb1 :
    (emb1 n₁ na nm)ᵀ * emb1 n₁ na nm = 1 := by
  rw [emb1_transpose_mul]
  ext i j
  unfold emb1
  simp [Matrix.fromRows_apply_inl]

lemma emb1t_mul_embA :
    (emb1 n₁ na nm)ᵀ * embA n₁ na nm = 0 := by
  rw [emb1_transpose_mul]
  ext i j
  unfold embA
  simp [Matrix.fromRows_apply_inl]

lemma emb1t_mul_embM :
    (emb1 n₁ na nm)ᵀ * embM n₁ na nm = 0 := by
  rw [emb1_transpose_mul]
  ext i j
  unfold embM
  simp [Matrix.fromRows_apply_inl]

lemma embAt_mul_emb1 :
    (embA n₁ na nm)ᵀ * emb1 n₁ na nm = 0 := by
  rw [embA_transpose_mul]
  ext i j
  unfold emb1
  simp [Matrix.fromRows_apply_inr]

lemma embAt_mul_embA :
    (embA n₁ na nm)ᵀ * embA n₁ na nm = 1 := by
  rw [embA_transpose_mul]
  ext i j
  unfold embA
  simp [Matrix.fromRows_apply_inr, Matrix.fromRows_apply_inl]

lemma embAt_mul_embM :
    (embA n₁ na nm)ᵀ * embM n₁ na nm = 0 := by
  rw [embA_transpose_mul]
  ext i j
  unfold embM
  simp [Matrix.fromRows_apply_inr, Matrix.fromRows_apply_inl]

lemma embMt_mul_emb1 :
    (embM n₁ na nm)ᵀ * emb1 n₁ na nm = 0 := by
  rw [embM_transpose_mul]
  ext i j
  unfold emb1
  simp [Matrix.fromRows_apply_inr]

lemma embMt_mul_embA :
    (embM n₁ na nm)ᵀ * embA n₁ na nm = 0 := by
  rw [embM_transpose_mul]
  ext i j
  unfold embA
  simp [Matrix.fromRows_apply_inr]

lemma embMt_mul_embM :
    (embM n₁ na nm)ᵀ * embM n₁ na nm = 1 := by
  rw [embM_transpose_mul]
  ext i j
  unfold embM
  simp [Matrix.fromRows_apply_inr]

/-- The three-way partition of the identity. -/
lemma partition3 :
    emb1 n₁ na nm * (emb1 n₁ na nm)ᵀ
      + embA n₁ na nm * (embA n₁ na nm)ᵀ
      + embM n₁ na nm * (embM n₁ na nm)ᵀ = 1 := by
  ext i j
  rcases i with i₁ | ia | im <;> rcases j with j₁ | ja | jm <;>
    simp [emb1, embA, embM, Matrix.add_apply,
      Matrix.one_apply, Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.transpose_apply, eq_comm]

/-! ### System products with the embeddings -/

lemma fullC_mul_emb1 : S.fullC * emb1 n₁ na nm = S.C₁ := by
  rw [mul_emb1]
  ext k j
  unfold fullC
  simp [Matrix.fromCols_apply_inl]

lemma fullA_mul_emb1 :
    S.fullA * emb1 n₁ na nm = emb1 n₁ na nm * S.A₁ := by
  rw [mul_emb1]
  ext k j
  rcases k with k₁ | k₂ <;>
    simp [fullA, emb1, Matrix.fromBlocks, Matrix.mul_apply,
      Matrix.fromRows_apply_inl,
      Matrix.fromRows_apply_inr, Matrix.one_apply, ite_mul,
      Finset.sum_ite_eq]

lemma fullG_eq : S.fullG = emb1 n₁ na nm * S.G₁ := by
  ext k j
  rcases k with k₁ | k₂ <;>
    simp [fullG, emb1, Matrix.mul_apply,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.one_apply, Finset.sum_ite_eq]

lemma fullA_mul_embA :
    S.fullA * embA n₁ na nm
      = emb1 n₁ na nm * (S.A₁₂ * ea2 na nm)
        + embA n₁ na nm * S.Aa := by
  ext k j
  rcases k with k₁ | ka | km <;>
    simp [fullA, A₂, emb1, embA, ea2, Matrix.fromBlocks,
      Matrix.mul_apply, Matrix.add_apply, Fintype.sum_sum_type,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.one_apply, Finset.sum_ite_eq']

lemma fullA_mul_embM :
    S.fullA * embM n₁ na nm
      = emb1 n₁ na nm * (S.A₁₂ * em2 na nm)
        + embM n₁ na nm * S.Am := by
  ext k j
  rcases k with k₁ | ka | km <;>
    simp [fullA, A₂, emb1, embM, em2, Matrix.fromBlocks,
      Matrix.mul_apply, Matrix.add_apply, Fintype.sum_sum_type,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.one_apply, Finset.sum_ite_eq']

/-! ### The chart -/

/-- The regression factor `V = e₁·Λ₁ₐ + eₐ + eₘ·Λₘₐ`. -/
noncomputable def condV (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    Matrix (ix n₁ na nm) (Fin na) ℝ :=
  emb1 n₁ na nm * Λ1a + embA n₁ na nm + embM n₁ na nm * Λma

/-- The effective antistable observation (`eq:Ceff`). -/
noncomputable def ceff (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) : Matrix (Fin p) (Fin na) ℝ :=
  S.C₁ * Λ1a + S.fullC * embA n₁ na nm
    + S.fullC * embM n₁ na nm * Λma

lemma fullC_mul_condV (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    S.fullC * condV Λ1a Λma = S.ceff Λ1a Λma := by
  unfold condV ceff
  rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc,
    S.fullC_mul_emb1, ← Matrix.mul_assoc]

lemma emb1t_mul_condV (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    (emb1 n₁ na nm)ᵀ * condV Λ1a Λma = Λ1a := by
  unfold condV
  rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc,
    emb1t_mul_emb1, Matrix.one_mul, emb1t_mul_embA,
    ← Matrix.mul_assoc, emb1t_mul_embM, Matrix.zero_mul,
    add_zero, add_zero]

lemma embAt_mul_condV (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    (embA n₁ na nm)ᵀ * condV Λ1a Λma = 1 := by
  unfold condV
  rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc,
    embAt_mul_emb1, Matrix.zero_mul, embAt_mul_embA,
    ← Matrix.mul_assoc, embAt_mul_embM, Matrix.zero_mul,
    zero_add, add_zero]

lemma embMt_mul_condV (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    (embM n₁ na nm)ᵀ * condV Λ1a Λma = Λma := by
  unfold condV
  rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc,
    embMt_mul_emb1, Matrix.zero_mul, embMt_mul_embA,
    ← Matrix.mul_assoc, embMt_mul_embM, Matrix.one_mul,
    zero_add, zero_add]

/-- The dynamics send the regression factor forward
(`Λ̂ ↦ A₁Λ̂ + A₁ₐ + A₁ₘΛₘₐ` on `e₁`, `Aₐ` on `eₐ`, `AₘΛₘₐ` on `eₘ`). -/
lemma fullA_mul_condV (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    S.fullA * condV Λ1a Λma
      = emb1 n₁ na nm
          * (S.A₁ * Λ1a + S.A₁₂ * ea2 na nm + S.A₁₂ * em2 na nm * Λma)
        + embA n₁ na nm * S.Aa
        + embM n₁ na nm * (S.Am * Λma) := by
  unfold condV
  rw [Matrix.mul_add, Matrix.mul_add,
    ← Matrix.mul_assoc S.fullA (emb1 n₁ na nm) Λ1a,
    S.fullA_mul_emb1, S.fullA_mul_embA,
    ← Matrix.mul_assoc S.fullA (embM n₁ na nm) Λma,
    S.fullA_mul_embM]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- **The conditional chart** of a covariance: the data
`(P, Λ₁ₐ, Λₘₐ, Σₐₐ)` of `eq:jchart`/`eq:condcov` together with the
decomposition. -/
structure CondChart (Sg : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) where
  P : Matrix (Fin n₁) (Fin n₁) ℝ
  Λ1a : Matrix (Fin n₁) (Fin na) ℝ
  Λma : Matrix (Fin nm) (Fin na) ℝ
  Saa : Matrix (Fin na) (Fin na) ℝ
  hP : P.PosSemidef
  hSaa : Saa.PosDef
  decomp : Sg = emb1 n₁ na nm * P * (emb1 n₁ na nm)ᵀ
    + condV Λ1a Λma * Saa * (condV Λ1a Λma)ᵀ

lemma CondChart.posSemidef {Sg : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (c : CondChart Sg) : Sg.PosSemidef := by
  rw [c.decomp]
  have h1 := c.hP.mul_mul_conjTranspose_same (emb1 n₁ na nm)
  have h2 := c.hSaa.posSemidef.mul_mul_conjTranspose_same
    (condV c.Λ1a c.Λma)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2
  exact h1.add h2

end DareSystem

/-! ### The push-through identities

All the Woodbury content of `lem:condfilter`-2 / `lem:jtransform`,
distilled: consequences of `S = S̃ + C·Σₐₐ·Cᵀ` alone. -/

section PushThrough

variable {a q : Type*} [Fintype a] [DecidableEq a] [Fintype q]
  [DecidableEq q]

variable {Saa : Matrix a a ℝ} {Ceff : Matrix q a ℝ}
  {Sfull Stil : Matrix q q ℝ}

omit [DecidableEq a] in
/-- The inverse-difference bracket:
`S̃⁻¹ = S⁻¹ + S⁻¹·(C·Σₐₐ·Cᵀ)·S̃⁻¹`. -/
lemma inv_bracket (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det) :
    Stil⁻¹ = Sfull⁻¹ + Sfull⁻¹ * (Ceff * Saa * Ceffᵀ) * Stil⁻¹ := by
  calc Stil⁻¹ = Sfull⁻¹ * Sfull * Stil⁻¹ := by
        rw [Matrix.nonsing_inv_mul _ hSf, Matrix.one_mul]
  _ = Sfull⁻¹ * (Stil + Ceff * Saa * Ceffᵀ) * Stil⁻¹ := by rw [← hS]
  _ = Sfull⁻¹ * Stil * Stil⁻¹
      + Sfull⁻¹ * (Ceff * Saa * Ceffᵀ) * Stil⁻¹ := by
      rw [Matrix.mul_add, Matrix.add_mul]
  _ = Sfull⁻¹ + Sfull⁻¹ * (Ceff * Saa * Ceffᵀ) * Stil⁻¹ := by
      rw [Matrix.mul_assoc Sfull⁻¹ Stil Stil⁻¹,
        Matrix.mul_nonsing_inv _ hSt, Matrix.mul_one]

omit [DecidableEq a] in
/-- **The push-through**:
`S̃⁻¹·C·Û = S⁻¹·C·Σₐₐ` where `Û = Σₐₐ − Σₐₐ·Cᵀ·S⁻¹·C·Σₐₐ`. -/
lemma pushthrough (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det) :
    Stil⁻¹ * Ceff
        * (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa))
      = Sfull⁻¹ * Ceff * Saa := by
  have h1 : Stil⁻¹ * Ceff
        * (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa))
      = Stil⁻¹ * ((Sfull - Ceff * Saa * Ceffᵀ) * (Sfull⁻¹
          * (Ceff * Saa))) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    congr 1
    · rw [show Sfull * (Sfull⁻¹ * (Ceff * Saa))
          = Ceff * Saa by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hSf,
          Matrix.one_mul]]
      rw [Matrix.mul_assoc]
    · simp only [Matrix.mul_assoc]
  rw [h1, show Sfull - Ceff * Saa * Ceffᵀ = Stil by
      rw [hS]; abel,
    ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSt, Matrix.one_mul,
    ← Matrix.mul_assoc]

omit [DecidableEq a] in
/-- The mirrored push-through:
`Û·Cᵀ·S̃⁻¹ = Σₐₐ·Cᵀ·S⁻¹` (for symmetric `Σₐₐ`, `S`, `S̃`). -/
lemma pushthrough' (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det)
    (hSaaSym : Saaᵀ = Saa) (hSfSym : Sfullᵀ = Sfull)
    (hStSym : Stilᵀ = Stil) :
    (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa)) * Ceffᵀ * Stil⁻¹
      = Saa * Ceffᵀ * Sfull⁻¹ := by
  have h := congrArg Matrix.transpose (pushthrough hS hSf hSt)
  simp only [Matrix.transpose_mul, Matrix.transpose_sub,
    Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
    hSaaSym, hSfSym, hStSym] at h
  simp only [← Matrix.mul_assoc] at h ⊢
  exact h

/-- **The information form** (`lem:jtransform`'s Woodbury dual):
`Û·(Σₐₐ⁻¹ + Cᵀ·S̃⁻¹·C) = 1`. -/
lemma uhat_mul_inv_form (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det)
    (hSa : IsUnit Saa.det) :
    (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa))
      * (Saa⁻¹ + Ceffᵀ * Stil⁻¹ * Ceff) = 1 := by
  have hb := inv_bracket hS hSf hSt
  have h2 : Saa * (Ceffᵀ * Stil⁻¹ * Ceff)
      = Saa * Ceffᵀ * Sfull⁻¹ * Ceff
        + Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa)
          * (Ceffᵀ * Stil⁻¹ * Ceff) := by
    calc Saa * (Ceffᵀ * Stil⁻¹ * Ceff)
        = Saa * (Ceffᵀ * (Sfull⁻¹
            + Sfull⁻¹ * (Ceff * Saa * Ceffᵀ) * Stil⁻¹) * Ceff) := by
          conv_lhs => rw [hb]
    _ = Saa * Ceffᵀ * Sfull⁻¹ * Ceff
        + Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa)
          * (Ceffᵀ * Stil⁻¹ * Ceff) := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.mul_nonsing_inv _ hSa]
  have h1 : Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa) * Saa⁻¹
      = Saa * Ceffᵀ * Sfull⁻¹ * Ceff := by
    rw [Matrix.mul_assoc (Saa * Ceffᵀ * Sfull⁻¹) (Ceff * Saa) Saa⁻¹,
      Matrix.mul_assoc Ceff Saa Saa⁻¹, Matrix.mul_nonsing_inv _ hSa,
      Matrix.mul_one]
  rw [h1, h2]
  abel

lemma isUnit_uhat_det (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det)
    (hSa : IsUnit Saa.det) :
    IsUnit (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa)).det :=
  Matrix.isUnit_det_of_right_inverse (uhat_mul_inv_form hS hSf hSt hSa)

/-- `Û⁻¹ = Σₐₐ⁻¹ + Cᵀ·S̃⁻¹·C` (`eq:J1-rec`'s increment). -/
lemma uhat_inv_eq (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det)
    (hSa : IsUnit Saa.det) :
    (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa))⁻¹
      = Saa⁻¹ + Ceffᵀ * Stil⁻¹ * Ceff :=
  Matrix.inv_eq_right_inv (uhat_mul_inv_form hS hSf hSt hSa)

omit [DecidableEq a] in
/-- The push-through with a left factor. -/
lemma pushthrough_left (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det)
    {k : Type*} [Fintype k] (Y : Matrix k q ℝ) :
    Y * Stil⁻¹ * Ceff * (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa))
      = Y * Sfull⁻¹ * (Ceff * Saa) := by
  calc Y * Stil⁻¹ * Ceff
        * (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa))
      = Y * (Stil⁻¹ * Ceff
          * (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa))) := by
        simp only [Matrix.mul_assoc]
  _ = Y * (Sfull⁻¹ * Ceff * Saa) := by rw [pushthrough hS hSf hSt]
  _ = Y * Sfull⁻¹ * (Ceff * Saa) := by simp only [Matrix.mul_assoc]

omit [DecidableEq a] in
/-- The mirrored push-through with a right factor. -/
lemma pushthrough_right (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det)
    (hSaaSym : Saaᵀ = Saa) (hSfSym : Sfullᵀ = Sfull)
    (hStSym : Stilᵀ = Stil)
    {k : Type*} [Fintype k] (Y : Matrix q k ℝ) :
    (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa)) * (Ceffᵀ
        * (Stil⁻¹ * Y))
      = Saa * Ceffᵀ * Sfull⁻¹ * Y := by
  calc (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa))
        * (Ceffᵀ * (Stil⁻¹ * Y))
      = (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa)) * Ceffᵀ
          * Stil⁻¹ * Y := by
        simp only [Matrix.mul_assoc]
  _ = Saa * Ceffᵀ * Sfull⁻¹ * Y := by
      rw [pushthrough' hS hSf hSt hSaaSym hSfSym hStSym]

omit [DecidableEq a] in
/-- The bracket, sandwiched. -/
lemma bracket_sandwich (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det)
    {k k' : Type*} [Fintype k] [Fintype k']
    (Y : Matrix k q ℝ) (Z : Matrix q k' ℝ) :
    Y * Stil⁻¹ * Z
      = Y * Sfull⁻¹ * Z
        + Y * Sfull⁻¹ * (Ceff * Saa * Ceffᵀ) * (Stil⁻¹ * Z) := by
  have hb := inv_bracket hS hSf hSt
  calc Y * Stil⁻¹ * Z
      = Y * (Sfull⁻¹ + Sfull⁻¹ * (Ceff * Saa * Ceffᵀ) * Stil⁻¹)
          * Z := by rw [← hb]
  _ = Y * Sfull⁻¹ * Z
      + Y * Sfull⁻¹ * (Ceff * Saa * Ceffᵀ) * (Stil⁻¹ * Z) := by
      rw [Matrix.mul_add, Matrix.add_mul]
      congr 1
      simp only [Matrix.mul_assoc]

omit [DecidableEq a] in
/-- **The two-block conditional update** (the algebraic heart of
`lem:condfilter`-1,2): the measurement update of a conditionally
decomposed covariance is again conditionally decomposed, with the
conditional block updated by its own reduced filter, the loading sent
through `Λ̂ = Λ − K·C_eff`, and the antistable block contracted. -/
lemma twoblock_update {ι n' : Type*} [Fintype ι] [Fintype n']
    (W₁ : Matrix ι n' ℝ) (W₂ : Matrix ι a ℝ)
    {P : Matrix n' n' ℝ} {C1 : Matrix q n' ℝ}
    (hS : Sfull = Stil + Ceff * Saa * Ceffᵀ)
    (hSf : IsUnit Sfull.det) (hSt : IsUnit Stil.det)
    (hPsym : Pᵀ = P) (hSaaSym : Saaᵀ = Saa)
    (hSfSym : Sfullᵀ = Sfull) (hStSym : Stilᵀ = Stil) :
    W₁ * P * W₁ᵀ + W₂ * Saa * W₂ᵀ
      - (W₁ * (P * C1ᵀ) + W₂ * (Saa * Ceffᵀ)) * Sfull⁻¹
          * (C1 * P * W₁ᵀ + Ceff * Saa * W₂ᵀ)
      = W₁ * (P - P * C1ᵀ * Stil⁻¹ * (C1 * P)) * W₁ᵀ
        + (W₂ - W₁ * (P * C1ᵀ * Stil⁻¹ * Ceff))
          * (Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa))
          * (W₂ - W₁ * (P * C1ᵀ * Stil⁻¹ * Ceff))ᵀ := by
  set U : Matrix a a ℝ :=
    Saa - Saa * Ceffᵀ * Sfull⁻¹ * (Ceff * Saa) with hU
  -- the three coefficient identities
  have h12 : P * C1ᵀ * Stil⁻¹ * Ceff * U
      = P * C1ᵀ * Sfull⁻¹ * (Ceff * Saa) := by
    rw [hU]
    exact pushthrough_left hS hSf hSt (P * C1ᵀ)
  have h21 : U * (Ceffᵀ * (Stil⁻¹ * (C1 * P)))
      = Saa * Ceffᵀ * Sfull⁻¹ * (C1 * P) := by
    rw [hU]
    exact pushthrough_right hS hSf hSt hSaaSym hSfSym hStSym _
  have h11 : P * C1ᵀ * Stil⁻¹ * (C1 * P)
      = P * C1ᵀ * Sfull⁻¹ * (C1 * P)
        + P * C1ᵀ * Sfull⁻¹ * (Ceff * Saa * Ceffᵀ)
          * (Stil⁻¹ * (C1 * P)) :=
    bracket_sandwich hS hSf hSt (P * C1ᵀ) (C1 * P)
  -- expand the right-hand side and substitute
  have hVt : (W₂ - W₁ * (P * C1ᵀ * Stil⁻¹ * Ceff))ᵀ
      = W₂ᵀ - Ceffᵀ * (Stil⁻¹ * (C1 * P)) * W₁ᵀ := by
    simp only [Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
      hPsym, hStSym]
    try simp only [Matrix.mul_assoc]
  rw [hVt]
  -- distribute everything and close with the identities
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
    Matrix.add_mul]
  rw [show W₁ * (P * C1ᵀ * Stil⁻¹ * Ceff) * U
      = W₁ * (P * C1ᵀ * Stil⁻¹ * Ceff * U) by
    simp only [Matrix.mul_assoc], h12]
  rw [show W₂ * U * (Ceffᵀ * (Stil⁻¹ * (C1 * P)) * W₁ᵀ)
      = W₂ * (U * (Ceffᵀ * (Stil⁻¹ * (C1 * P)))) * W₁ᵀ by
    simp only [Matrix.mul_assoc], h21]
  rw [show W₁ * (P * C1ᵀ * Sfull⁻¹ * (Ceff * Saa))
        * (Ceffᵀ * (Stil⁻¹ * (C1 * P)) * W₁ᵀ)
      = W₁ * (P * C1ᵀ * Sfull⁻¹ * (Ceff * Saa * Ceffᵀ)
          * (Stil⁻¹ * (C1 * P))) * W₁ᵀ by
    simp only [Matrix.mul_assoc]]
  rw [show W₁ * (P * C1ᵀ * Stil⁻¹ * (C1 * P)) * W₁ᵀ
      = W₁ * (P * C1ᵀ * Sfull⁻¹ * (C1 * P)) * W₁ᵀ
        + W₁ * (P * C1ᵀ * Sfull⁻¹ * (Ceff * Saa * Ceffᵀ)
            * (Stil⁻¹ * (C1 * P))) * W₁ᵀ by
    rw [h11, Matrix.mul_add, Matrix.add_mul]]
  rw [hU]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

end PushThrough

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

variable {Sg : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}

/-! ### The chart step -/

/-- The innovation of a charted covariance decomposes:
`S = S̃ + C_eff·Σₐₐ·C_effᵀ` (`lem:condfilter`-1's split). -/
lemma chart_innov_eq (c : CondChart Sg) :
    innov S.fullC S.R Sg
      = innov S.C₁ S.R c.P
        + S.ceff c.Λ1a c.Λma * c.Saa * (S.ceff c.Λ1a c.Λma)ᵀ := by
  obtain ⟨P, Λ1a, Λma, Saa, hP, hSaa, hdec⟩ := c
  dsimp only
  have hCe1 : (emb1 n₁ na nm)ᵀ * S.fullCᵀ = S.C₁ᵀ := by
    rw [← Matrix.transpose_mul, S.fullC_mul_emb1]
  have hCV : (condV Λ1a Λma)ᵀ * S.fullCᵀ
      = (S.ceff Λ1a Λma)ᵀ := by
    rw [← Matrix.transpose_mul, S.fullC_mul_condV]
  unfold innov
  rw [hdec, Matrix.mul_add S.fullC, Matrix.add_mul]
  have h1 : S.fullC * (emb1 n₁ na nm * P * (emb1 n₁ na nm)ᵀ)
        * S.fullCᵀ
      = S.C₁ * P * S.C₁ᵀ := by
    calc S.fullC * (emb1 n₁ na nm * P * (emb1 n₁ na nm)ᵀ)
          * S.fullCᵀ
        = S.fullC * emb1 n₁ na nm * P
            * ((emb1 n₁ na nm)ᵀ * S.fullCᵀ) := by
          simp only [Matrix.mul_assoc]
    _ = S.C₁ * P * S.C₁ᵀ := by rw [S.fullC_mul_emb1, hCe1]
  have h2 : S.fullC * (condV Λ1a Λma * Saa
        * (condV Λ1a Λma)ᵀ) * S.fullCᵀ
      = S.ceff Λ1a Λma * Saa * (S.ceff Λ1a Λma)ᵀ := by
    calc S.fullC * (condV Λ1a Λma * Saa
          * (condV Λ1a Λma)ᵀ) * S.fullCᵀ
        = S.fullC * condV Λ1a Λma * Saa
            * ((condV Λ1a Λma)ᵀ * S.fullCᵀ) := by
          simp only [Matrix.mul_assoc]
    _ = S.ceff Λ1a Λma * Saa * (S.ceff Λ1a Λma)ᵀ := by
        rw [S.fullC_mul_condV, hCV]
  rw [h1, h2]
  abel

/-- The post-update loading (`lem:condfilter`-2,
`Λ̂₁ₐ = Λ₁ₐ − K·C_eff`). -/
noncomputable def lamHat (P : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    Matrix (Fin n₁) (Fin na) ℝ :=
  Λ1a - P * S.C₁ᵀ * (innov S.C₁ S.R P)⁻¹ * S.ceff Λ1a Λma

/-- The full innovation, data-intrinsically. -/
noncomputable def sfullOf (P : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ)
    (Saa : Matrix (Fin na) (Fin na) ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  innov S.C₁ S.R P + S.ceff Λ1a Λma * Saa * (S.ceff Λ1a Λma)ᵀ

/-- The contracted antistable block. -/
noncomputable def uhatOf (P : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ)
    (Saa : Matrix (Fin na) (Fin na) ℝ) : Matrix (Fin na) (Fin na) ℝ :=
  Saa - Saa * (S.ceff Λ1a Λma)ᵀ * (S.sfullOf P Λ1a Λma Saa)⁻¹
    * (S.ceff Λ1a Λma * Saa)

/-- The predicted loading (`eq:cf-rec` in one piece:
`Λ₁ₐ⁺ = (A₁·Λ̂₁ₐ + A₁ₐ + A₁ₘ·Λₘₐ)·Aₐ⁻¹`). -/
noncomputable def lamNext (P : Matrix (Fin n₁) (Fin n₁) ℝ)
    (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ) :
    Matrix (Fin n₁) (Fin na) ℝ :=
  (S.A₁ * S.lamHat P Λ1a Λma + S.A₁₂ * ea2 na nm
    + S.A₁₂ * em2 na nm * Λma) * S.Aa⁻¹

lemma sfullOf_posDef {P : Matrix (Fin n₁) (Fin n₁) ℝ}
    (hP : P.PosSemidef) (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ)
    {Saa : Matrix (Fin na) (Fin na) ℝ} (hSaa : Saa.PosSemidef) :
    (S.sfullOf P Λ1a Λma Saa).PosDef := by
  unfold sfullOf
  refine Matrix.PosDef.add_posSemidef (innov_posDef S.hR hP) ?_
  have h := hSaa.mul_mul_conjTranspose_same (S.ceff Λ1a Λma)
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The contracted antistable block stays positive definite
(`lem:structure`-3 on the chart, information form). -/
lemma uhatOf_posDef {P : Matrix (Fin n₁) (Fin n₁) ℝ}
    (hP : P.PosSemidef) (Λ1a : Matrix (Fin n₁) (Fin na) ℝ)
    (Λma : Matrix (Fin nm) (Fin na) ℝ)
    {Saa : Matrix (Fin na) (Fin na) ℝ} (hSaa : Saa.PosDef) :
    (S.uhatOf P Λ1a Λma Saa).PosDef := by
  have hSf := S.sfullOf_posDef hP Λ1a Λma hSaa.posSemidef
  have hSfu : IsUnit (S.sfullOf P Λ1a Λma Saa).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSf.isUnit
  have hStu : IsUnit (innov S.C₁ S.R P).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (innov_posDef (C := S.C₁) S.hR hP).isUnit
  have hSau : IsUnit Saa.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSaa.isUnit
  have hform := uhat_mul_inv_form (Ceff := S.ceff Λ1a Λma)
    (Saa := Saa) (Sfull := S.sfullOf P Λ1a Λma Saa)
    (Stil := innov S.C₁ S.R P) rfl hSfu hStu hSau
  have hsum : (Saa⁻¹ + (S.ceff Λ1a Λma)ᵀ
      * (innov S.C₁ S.R P)⁻¹ * S.ceff Λ1a Λma).PosDef := by
    refine Matrix.PosDef.add_posSemidef hSaa.inv ?_
    have h := (innov_posDef (C := S.C₁)
      S.hR hP).inv.posSemidef.mul_mul_conjTranspose_same
      (S.ceff Λ1a Λma)ᵀ
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose] at h
  have hinv : S.uhatOf P Λ1a Λma Saa
      = (Saa⁻¹ + (S.ceff Λ1a Λma)ᵀ
          * (innov S.C₁ S.R P)⁻¹ * S.ceff Λ1a Λma)⁻¹ := by
    have h4 := Matrix.inv_eq_right_inv hform
    have h5 : IsUnit (Saa - Saa * (S.ceff Λ1a Λma)ᵀ
        * (S.sfullOf P Λ1a Λma Saa)⁻¹ * (S.ceff Λ1a Λma * Saa)).det :=
      Matrix.isUnit_det_of_right_inverse hform
    rw [← h4, Matrix.nonsing_inv_nonsing_inv _ h5]
    rfl
  rw [hinv]
  exact hsum.inv

/-- **The chart update** (`lem:condfilter`-1,2, update half): the
measurement update maps the chart
`(P, Λ₁ₐ, Λₘₐ, Σₐₐ) ↦ (U₁(P), Λ̂₁ₐ, Λₘₐ, Û)`. -/
theorem chart_updM (c : CondChart Sg) :
    updM S.fullC S.R Sg
      = emb1 n₁ na nm * updM S.C₁ S.R c.P * (emb1 n₁ na nm)ᵀ
        + condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma
          * S.uhatOf c.P c.Λ1a c.Λma c.Saa
          * (condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma)ᵀ := by
  have hpsdSg := c.posSemidef
  have hSfeq : innov S.fullC S.R Sg
      = innov S.C₁ S.R c.P
        + S.ceff c.Λ1a c.Λma * c.Saa * (S.ceff c.Λ1a c.Λma)ᵀ :=
    S.chart_innov_eq c
  obtain ⟨P, Λ1a, Λma, Saa, hP, hSaa, hdec⟩ := c
  dsimp only at hSfeq ⊢
  have hSf : IsUnit (innov S.fullC S.R Sg).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (innov_posDef S.hR hpsdSg).isUnit
  have hSt : IsUnit (innov S.C₁ S.R P).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp
      (innov_posDef (C := S.C₁) S.hR hP).isUnit
  have hPsym : Pᵀ = P := hP.1.transpose_eq_self
  have hSaaSym : Saaᵀ = Saa := hSaa.posSemidef.1.transpose_eq_self
  have hSfSym : (innov S.fullC S.R Sg)ᵀ = innov S.fullC S.R Sg :=
    innov_transpose S.hR hpsdSg
  have hStSym : (innov S.C₁ S.R P)ᵀ = innov S.C₁ S.R P :=
    innov_transpose (C := S.C₁) S.hR hP
  -- rows and columns of the charted covariance against C
  have hCe1 : (emb1 n₁ na nm)ᵀ * S.fullCᵀ = S.C₁ᵀ := by
    rw [← Matrix.transpose_mul, S.fullC_mul_emb1]
  have hCV : (condV Λ1a Λma)ᵀ * S.fullCᵀ
      = (S.ceff Λ1a Λma)ᵀ := by
    rw [← Matrix.transpose_mul, S.fullC_mul_condV]
  have hSgC : Sg * S.fullCᵀ
      = emb1 n₁ na nm * (P * S.C₁ᵀ)
        + condV Λ1a Λma * (Saa * (S.ceff Λ1a Λma)ᵀ) := by
    rw [hdec, Matrix.add_mul]
    congr 1
    · calc emb1 n₁ na nm * P * (emb1 n₁ na nm)ᵀ * S.fullCᵀ
          = emb1 n₁ na nm * (P * ((emb1 n₁ na nm)ᵀ * S.fullCᵀ)) := by
            simp only [Matrix.mul_assoc]
      _ = emb1 n₁ na nm * (P * S.C₁ᵀ) := by rw [hCe1]
    · calc condV Λ1a Λma * Saa * (condV Λ1a Λma)ᵀ * S.fullCᵀ
          = condV Λ1a Λma * (Saa
              * ((condV Λ1a Λma)ᵀ * S.fullCᵀ)) := by
            simp only [Matrix.mul_assoc]
      _ = condV Λ1a Λma * (Saa * (S.ceff Λ1a Λma)ᵀ) := by rw [hCV]
  have hCSg : S.fullC * Sg
      = S.C₁ * P * (emb1 n₁ na nm)ᵀ
        + S.ceff Λ1a Λma * Saa * (condV Λ1a Λma)ᵀ := by
    rw [hdec, Matrix.mul_add]
    congr 1
    · calc S.fullC * (emb1 n₁ na nm * P * (emb1 n₁ na nm)ᵀ)
          = S.fullC * emb1 n₁ na nm * P * (emb1 n₁ na nm)ᵀ := by
            simp only [Matrix.mul_assoc]
      _ = S.C₁ * P * (emb1 n₁ na nm)ᵀ := by rw [S.fullC_mul_emb1]
    · calc S.fullC * (condV Λ1a Λma * Saa * (condV Λ1a Λma)ᵀ)
          = S.fullC * condV Λ1a Λma * Saa * (condV Λ1a Λma)ᵀ := by
            simp only [Matrix.mul_assoc]
      _ = S.ceff Λ1a Λma * Saa * (condV Λ1a Λma)ᵀ := by
          rw [S.fullC_mul_condV]
  -- assemble via the generic two-block update
  have htb := twoblock_update (Sfull := innov S.fullC S.R Sg)
    (Stil := innov S.C₁ S.R P) (Ceff := S.ceff Λ1a Λma)
    (Saa := Saa) (emb1 n₁ na nm) (condV Λ1a Λma)
    (P := P) (C1 := S.C₁) hSfeq hSf hSt hPsym hSaaSym hSfSym hStSym
  show Sg - Sg * S.fullCᵀ * (innov S.fullC S.R Sg)⁻¹ * (S.fullC * Sg)
      = _
  rw [hSgC, hCSg]
  unfold lamHat uhatOf
  rw [show (S.sfullOf P Λ1a Λma Saa)⁻¹
      = (innov S.fullC S.R Sg)⁻¹ by unfold sfullOf; rw [hSfeq]]
  have hVhat : condV (Λ1a - P * S.C₁ᵀ * (innov S.C₁ S.R P)⁻¹
        * S.ceff Λ1a Λma) Λma
      = condV Λ1a Λma - emb1 n₁ na nm
          * (P * S.C₁ᵀ * (innov S.C₁ S.R P)⁻¹ * S.ceff Λ1a Λma) := by
    unfold condV
    rw [Matrix.mul_sub]
    abel
  have hupdred : updM S.C₁ S.R P
      = P - P * S.C₁ᵀ * (innov S.C₁ S.R P)⁻¹ * (S.C₁ * P) :=
    rfl
  rw [hVhat, hupdred]
  rw [← hdec] at htb
  exact htb

/-- **The chart prediction** (`lem:condfilter` prediction half +
`eq:cf-rec` + `eq:loading-rec` + the `(a,a)`-identity): one full DARE
step maps the chart
`(P, Λ₁ₐ, Λₘₐ, Σₐₐ) ↦ (R₁(P), Λ₁ₐ⁺, AₘΛₘₐAₐ⁻¹, Aₐ·Û·Aₐᵀ)`. -/
theorem chart_dareStep (c : CondChart Sg) :
    dareStep S.fullC S.R S.fullA S.Qw Sg
      = emb1 n₁ na nm
          * dareStep S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ) c.P
          * (emb1 n₁ na nm)ᵀ
        + condV (S.lamNext c.P c.Λ1a c.Λma) (S.Am * c.Λma * S.Aa⁻¹)
          * (S.Aa * S.uhatOf c.P c.Λ1a c.Λma c.Saa * S.Aaᵀ)
          * (condV (S.lamNext c.P c.Λ1a c.Λma)
              (S.Am * c.Λma * S.Aa⁻¹))ᵀ := by
  have hupd := S.chart_updM c
  have hcancel : ∀ {k : Type} (X : Matrix k (Fin na) ℝ),
      X * S.Aa⁻¹ * S.Aa = X := by
    intro k X
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ S.isUnit_Aa_det,
      Matrix.mul_one]
  -- A·V̂ = V⁺·Aₐ
  have hAV : S.fullA * condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma
      = condV (S.lamNext c.P c.Λ1a c.Λma) (S.Am * c.Λma * S.Aa⁻¹)
          * S.Aa := by
    rw [S.fullA_mul_condV]
    conv_rhs => rw [show condV (S.lamNext c.P c.Λ1a c.Λma)
        (S.Am * c.Λma * S.Aa⁻¹)
      = emb1 n₁ na nm * S.lamNext c.P c.Λ1a c.Λma + embA n₁ na nm
        + embM n₁ na nm * (S.Am * c.Λma * S.Aa⁻¹) from rfl]
    rw [Matrix.add_mul, Matrix.add_mul]
    have h1 : emb1 n₁ na nm * S.lamNext c.P c.Λ1a c.Λma * S.Aa
        = emb1 n₁ na nm * (S.A₁ * S.lamHat c.P c.Λ1a c.Λma
            + S.A₁₂ * ea2 na nm + S.A₁₂ * em2 na nm * c.Λma) := by
      rw [Matrix.mul_assoc]
      congr 1
      unfold lamNext
      exact hcancel _
    have h2 : embM n₁ na nm * (S.Am * c.Λma * S.Aa⁻¹) * S.Aa
        = embM n₁ na nm * (S.Am * c.Λma) := by
      rw [Matrix.mul_assoc]
      congr 1
      exact hcancel _
    rw [h1, h2]
  have hAVt : (condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma)ᵀ * S.fullAᵀ
      = S.Aaᵀ * (condV (S.lamNext c.P c.Λ1a c.Λma)
          (S.Am * c.Λma * S.Aa⁻¹))ᵀ := by
    rw [← Matrix.transpose_mul, hAV, Matrix.transpose_mul]
  have hAe1t : (emb1 n₁ na nm)ᵀ * S.fullAᵀ
      = S.A₁ᵀ * (emb1 n₁ na nm)ᵀ := by
    rw [← Matrix.transpose_mul, S.fullA_mul_emb1, Matrix.transpose_mul]
  show S.fullA * updM S.fullC S.R Sg * S.fullAᵀ + S.Qw = _
  rw [hupd, Matrix.mul_add S.fullA, Matrix.add_mul]
  have h1 : S.fullA * (emb1 n₁ na nm * updM S.C₁ S.R c.P
        * (emb1 n₁ na nm)ᵀ) * S.fullAᵀ
      = emb1 n₁ na nm * (S.A₁ * updM S.C₁ S.R c.P * S.A₁ᵀ)
          * (emb1 n₁ na nm)ᵀ := by
    calc S.fullA * (emb1 n₁ na nm * updM S.C₁ S.R c.P
          * (emb1 n₁ na nm)ᵀ) * S.fullAᵀ
        = S.fullA * emb1 n₁ na nm * updM S.C₁ S.R c.P
            * ((emb1 n₁ na nm)ᵀ * S.fullAᵀ) := by
          simp only [Matrix.mul_assoc]
    _ = emb1 n₁ na nm * S.A₁ * updM S.C₁ S.R c.P
          * (S.A₁ᵀ * (emb1 n₁ na nm)ᵀ) := by
        rw [S.fullA_mul_emb1, hAe1t]
    _ = emb1 n₁ na nm * (S.A₁ * updM S.C₁ S.R c.P * S.A₁ᵀ)
          * (emb1 n₁ na nm)ᵀ := by
        simp only [Matrix.mul_assoc]
  have h2 : S.fullA * (condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma
        * S.uhatOf c.P c.Λ1a c.Λma c.Saa
        * (condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma)ᵀ) * S.fullAᵀ
      = condV (S.lamNext c.P c.Λ1a c.Λma) (S.Am * c.Λma * S.Aa⁻¹)
          * (S.Aa * S.uhatOf c.P c.Λ1a c.Λma c.Saa * S.Aaᵀ)
          * (condV (S.lamNext c.P c.Λ1a c.Λma)
              (S.Am * c.Λma * S.Aa⁻¹))ᵀ := by
    calc S.fullA * (condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma
          * S.uhatOf c.P c.Λ1a c.Λma c.Saa
          * (condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma)ᵀ) * S.fullAᵀ
        = S.fullA * condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma
            * S.uhatOf c.P c.Λ1a c.Λma c.Saa
            * ((condV (S.lamHat c.P c.Λ1a c.Λma) c.Λma)ᵀ
                * S.fullAᵀ) := by
          simp only [Matrix.mul_assoc]
    _ = condV (S.lamNext c.P c.Λ1a c.Λma) (S.Am * c.Λma * S.Aa⁻¹)
          * S.Aa * S.uhatOf c.P c.Λ1a c.Λma c.Saa
          * (S.Aaᵀ * (condV (S.lamNext c.P c.Λ1a c.Λma)
              (S.Am * c.Λma * S.Aa⁻¹))ᵀ) := by
        rw [hAV, hAVt]
    _ = condV (S.lamNext c.P c.Λ1a c.Λma) (S.Am * c.Λma * S.Aa⁻¹)
          * (S.Aa * S.uhatOf c.P c.Λ1a c.Λma c.Saa * S.Aaᵀ)
          * (condV (S.lamNext c.P c.Λ1a c.Λma)
              (S.Am * c.Λma * S.Aa⁻¹))ᵀ := by
        simp only [Matrix.mul_assoc]
  have hQw : S.Qw
      = emb1 n₁ na nm * (S.G₁ * S.Q * S.G₁ᵀ) * (emb1 n₁ na nm)ᵀ := by
    unfold Qw
    rw [S.fullG_eq, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  rw [h1, h2, hQw]
  have h3 : dareStep S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ) c.P
      = S.A₁ * updM S.C₁ S.R c.P * S.A₁ᵀ + S.G₁ * S.Q * S.G₁ᵀ := rfl
  rw [h3, Matrix.mul_add (emb1 n₁ na nm), Matrix.add_mul]
  abel

/-! ### The chart along the lower trajectory
(`lem:condfilter`, `lem:jtransform` recursions, explicit data) -/

/-- The reduced (conditional) Riccati trajectory from the zero seed
(`eq:condric`): the `e₁` filter, in which `Σₐₐ` never appears. -/
noncomputable def redP : ℕ → Matrix (Fin n₁) (Fin n₁) ℝ :=
  dareIter S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ) 0

lemma redQ_posSemidef : (S.G₁ * S.Q * S.G₁ᵀ).PosSemidef := by
  have h := S.hQ.posSemidef.mul_mul_conjTranspose_same S.G₁
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

lemma redP_posSemidef (T : ℕ) : (S.redP T).PosSemidef :=
  dareIter_posSemidef S.hR S.redQ_posSemidef Matrix.PosSemidef.zero T

/-- The marginal loading along the run (`eq:loading-rec` closed
form). -/
noncomputable def lowLamma (T : ℕ) : Matrix (Fin nm) (Fin na) ℝ :=
  S.Am ^ T * S.lam0 * (S.Aa⁻¹) ^ T

/-- The conditional-filter loading along the run (`eq:cf-rec`). -/
noncomputable def lowLam1a : ℕ → Matrix (Fin n₁) (Fin na) ℝ
  | 0 => 0
  | T + 1 => S.lamNext (S.redP T) (lowLam1a T) (S.lowLamma T)

/-- The antistable block along the run (`lem:jtransform`'s
`(a,a)`-identity). -/
noncomputable def lowSaa (δ : ℝ) : ℕ → Matrix (Fin na) (Fin na) ℝ
  | 0 => δ • S.Siga
  | T + 1 => S.Aa * S.uhatOf (S.redP T) (S.lowLam1a T) (S.lowLamma T)
      (lowSaa δ T) * S.Aaᵀ

lemma Aa_vecMul_injective : Function.Injective S.Aa.vecMul := by
  intro x y hxy
  have h := congrArg (fun v => v ᵥ* S.Aa⁻¹) hxy
  simpa [Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv _ S.isUnit_Aa_det] using h

lemma lowSaa_posDef (hSa : S.Siga.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    ∀ T, (S.lowSaa δ T).PosDef
  | 0 => hSa.smul hδ
  | T + 1 => by
    have hU := S.uhatOf_posDef (S.redP_posSemidef T) (S.lowLam1a T)
      (S.lowLamma T) (lowSaa_posDef hSa hδ T)
    have h := hU.mul_mul_conjTranspose_same (B := S.Aa)
      S.Aa_vecMul_injective
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

set_option linter.unusedSimpArgs false in
/-- The blocks of the seed decomposition. -/
lemma emb_blocks_eq (X : Matrix (Fin na) (Fin na) ℝ)
    (Y : Matrix (Fin na) (Fin nm) ℝ) (Z : Matrix (Fin nm) (Fin na) ℝ)
    (W : Matrix (Fin nm) (Fin nm) ℝ) :
    embA n₁ na nm * X * (embA n₁ na nm)ᵀ
      + embA n₁ na nm * Y * (embM n₁ na nm)ᵀ
      + embM n₁ na nm * Z * (embA n₁ na nm)ᵀ
      + embM n₁ na nm * W * (embM n₁ na nm)ᵀ
      = Matrix.fromBlocks 0 0 0 (Matrix.fromBlocks X Y Z W) := by
  ext i j
  rcases i with i₁ | ia | im <;> rcases j with j₁ | ja | jm <;>
    simp [embA, embM, Matrix.fromBlocks, Matrix.mul_apply,
      Matrix.add_apply, Fintype.sum_sum_type,
      Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr,
      Matrix.transpose_apply, Matrix.one_apply, mul_ite, ite_mul,
      Finset.sum_ite_eq, Finset.sum_ite_eq']

/-- The slaved seed in chart form:
`Σ̲₀ = e₁·0·e₁ᵀ + [0-loading chart]·(δΣₐ)·[…]ᵀ`. -/
lemma slavedSeed_decomp (hSa : S.Siga.PosDef) (δ : ℝ) :
    S.slavedSeed δ
      = emb1 n₁ na nm * (0 : Matrix (Fin n₁) (Fin n₁) ℝ)
          * (emb1 n₁ na nm)ᵀ
        + condV 0 S.lam0 * (δ • S.Siga) * (condV 0 S.lam0)ᵀ := by
  have hV0 : condV (0 : Matrix (Fin n₁) (Fin na) ℝ) S.lam0
      = embA n₁ na nm + embM n₁ na nm * S.lam0 := by
    unfold condV
    rw [Matrix.mul_zero, zero_add]
  rw [hV0, Matrix.mul_zero, Matrix.zero_mul, zero_add]
  have hsmul : (embA n₁ na nm + embM n₁ na nm * S.lam0) * (δ • S.Siga)
        * (embA n₁ na nm + embM n₁ na nm * S.lam0)ᵀ
      = δ • ((embA n₁ na nm + embM n₁ na nm * S.lam0) * S.Siga
        * (embA n₁ na nm + embM n₁ na nm * S.lam0)ᵀ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hsmul]
  have htb21lam : S.Sig₂.toBlocks₂₁ * S.lam0ᵀ
      = S.lam0 * S.Sig₂.toBlocks₁₂ := by
    rw [← S.lam0_mul_Siga hSa, Matrix.mul_assoc, S.Siga_mul_lam0t hSa]
  have hcore : (embA n₁ na nm + embM n₁ na nm * S.lam0) * S.Siga
        * (embA n₁ na nm + embM n₁ na nm * S.lam0)ᵀ
      = Matrix.fromBlocks 0 0 0 S.sig2a := by
    simp only [Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.add_mul, Matrix.mul_add]
    have t1 : embA n₁ na nm * S.Siga * (S.lam0ᵀ * (embM n₁ na nm)ᵀ)
        = embA n₁ na nm * S.Sig₂.toBlocks₁₂ * (embM n₁ na nm)ᵀ := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (embA n₁ na nm) S.Siga
        S.lam0ᵀ, S.Siga_mul_lam0t hSa]
    have t2 : embM n₁ na nm * S.lam0 * S.Siga
        = embM n₁ na nm * S.Sig₂.toBlocks₂₁ := by
      rw [Matrix.mul_assoc, S.lam0_mul_Siga hSa]
    have t3 : embM n₁ na nm * S.Sig₂.toBlocks₂₁
          * (S.lam0ᵀ * (embM n₁ na nm)ᵀ)
        = embM n₁ na nm * (S.lam0 * S.Sig₂.toBlocks₁₂)
          * (embM n₁ na nm)ᵀ := by
      rw [← Matrix.mul_assoc, Matrix.mul_assoc (embM n₁ na nm)
        S.Sig₂.toBlocks₂₁ S.lam0ᵀ, htb21lam]
    rw [t2, t1, t3]
    have h5 : Matrix.fromBlocks (0 : Matrix (Fin n₁) (Fin n₁) ℝ) 0 0
        S.sig2a
      = embA n₁ na nm * S.Siga * (embA n₁ na nm)ᵀ
        + embA n₁ na nm * S.Sig₂.toBlocks₁₂ * (embM n₁ na nm)ᵀ
        + embM n₁ na nm * S.Sig₂.toBlocks₂₁ * (embA n₁ na nm)ᵀ
        + embM n₁ na nm * (S.lam0 * S.Sig₂.toBlocks₁₂)
          * (embM n₁ na nm)ᵀ :=
      (emb_blocks_eq (n₁ := n₁) S.Siga S.Sig₂.toBlocks₁₂
        S.Sig₂.toBlocks₂₁ (S.lam0 * S.Sig₂.toBlocks₁₂)).symm
    rw [h5]
    abel
  rw [hcore]
  unfold slavedSeed
  ext i j
  rcases i with i₁ | i₂ <;> rcases j with j₁ | j₂ <;>
    simp [Matrix.fromBlocks, Matrix.smul_apply]

/-- **The lower trajectory rides the chart**: explicit chart data at
every horizon (`lem:condfilter`-1,2 and `lem:loading` along the run,
assembled). -/
theorem lowTraj_decomp (hSa : S.Siga.PosDef) {δ : ℝ} (hδ : 0 < δ) :
    ∀ T, S.dareFrom (S.slavedSeed δ) T
      = emb1 n₁ na nm * S.redP T * (emb1 n₁ na nm)ᵀ
        + condV (S.lowLam1a T) (S.lowLamma T) * S.lowSaa δ T
          * (condV (S.lowLam1a T) (S.lowLamma T))ᵀ := by
  intro T
  induction T with
  | zero =>
    show S.slavedSeed δ = _
    have h0 : S.lowLamma 0 = S.lam0 := by
      unfold lowLamma
      rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
    rw [h0]
    exact S.slavedSeed_decomp hSa δ
  | succ T ih =>
    have hstep := S.chart_dareStep
      (Sg := S.dareFrom (S.slavedSeed δ) T)
      ⟨S.redP T, S.lowLam1a T, S.lowLamma T, S.lowSaa δ T,
        S.redP_posSemidef T, S.lowSaa_posDef hSa hδ T, ih⟩
    dsimp only at hstep
    have hLm : S.Am * S.lowLamma T * S.Aa⁻¹ = S.lowLamma (T + 1) := by
      unfold lowLamma
      rw [pow_succ' S.Am T, pow_succ (S.Aa⁻¹) T]
      simp only [Matrix.mul_assoc]
    have hP1 : S.redP (T + 1)
        = dareStep S.C₁ S.R S.A₁ (S.G₁ * S.Q * S.G₁ᵀ) (S.redP T) :=
      rfl
    have hL1 : S.lowLam1a (T + 1)
        = S.lamNext (S.redP T) (S.lowLam1a T) (S.lowLamma T) := rfl
    have hS1 : S.lowSaa δ (T + 1)
        = S.Aa * S.uhatOf (S.redP T) (S.lowLam1a T) (S.lowLamma T)
            (S.lowSaa δ T) * S.Aaᵀ := rfl
    show dareStep S.fullC S.R S.fullA S.Qw
        (S.dareFrom (S.slavedSeed δ) T) = _
    rw [hP1, hL1, hS1, ← hLm]
    exact hstep

/-- **`eq:J1-rec`, verified**: the antistable information along the
lower trajectory rides the fixed `Aₐ⁻¹`-Stein recursion with source
`Ξ_T = C_effᵀ·S̃⁻¹·C_eff`. -/
theorem lowJ_rec (hSa : S.Siga.PosDef) {δ : ℝ} (hδ : 0 < δ) (T : ℕ) :
    (S.lowSaa δ (T + 1))⁻¹
      = (S.Aaᵀ)⁻¹ * ((S.lowSaa δ T)⁻¹
          + (S.ceff (S.lowLam1a T) (S.lowLamma T))ᵀ
            * (innov S.C₁ S.R (S.redP T))⁻¹
            * S.ceff (S.lowLam1a T) (S.lowLamma T)) * S.Aa⁻¹ := by
  have hSf := S.sfullOf_posDef (S.redP_posSemidef T) (S.lowLam1a T)
    (S.lowLamma T) (S.lowSaa_posDef hSa hδ T).posSemidef
  have hUinv : (S.uhatOf (S.redP T) (S.lowLam1a T) (S.lowLamma T)
        (S.lowSaa δ T))⁻¹
      = (S.lowSaa δ T)⁻¹
        + (S.ceff (S.lowLam1a T) (S.lowLamma T))ᵀ
          * (innov S.C₁ S.R (S.redP T))⁻¹
          * S.ceff (S.lowLam1a T) (S.lowLamma T) :=
    uhat_inv_eq rfl
      ((Matrix.isUnit_iff_isUnit_det _).mp hSf.isUnit)
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (innov_posDef (C := S.C₁) S.hR (S.redP_posSemidef T)).isUnit)
      ((Matrix.isUnit_iff_isUnit_det _).mp
        (S.lowSaa_posDef hSa hδ T).isUnit)
  have hstep : S.lowSaa δ (T + 1)
      = S.Aa * S.uhatOf (S.redP T) (S.lowLam1a T) (S.lowLamma T)
          (S.lowSaa δ T) * S.Aaᵀ := rfl
  rw [hstep, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUinv,
    ← Matrix.mul_assoc]

end DareSystem

end Dare
end Estimation
