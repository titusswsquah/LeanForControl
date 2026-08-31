import LeanForControl.Estimation.Dare.BlockInfo
import LeanForControl.LinearSystems.Detectability
import Architect

/-!
# The antistable–marginal frame (`eq:three-block`)

The odyssey deck's working frame: the stabilizable part, the strictly
antistable part, and the unit-circle part separated in that order,

`A = [[A₁ A₁ₐ A₁ₘ],[0 Aₐ 0],[0 0 Aₘ]]`, `G = col(G₁,0,0)`,
`C = [C₁ Cₐ Cₘ]`, `Σ₀ = blkdiag(Σ₁, Σ₂)`,

carried on the index `Fin n₁ ⊕ (Fin nₐ ⊕ Fin n_m)` so the inner sum
is the uncontrollable `e₂` block and `A₂ = Aₐ ⊕ Aₘ` block-diagonal.
The C3w / stabilizing regime is `n_m = 0`.

The conditions C2/C2w are **defined in the paper's kernel form**
(`ker Σ₀ ∩ 𝒳 = {0}` on the coordinate subspaces the frame exhibits)
and the prior-positivity forms are theorems — `eq:prior-pos`(a)/(b),
the latter being `lem:criterion-w`.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

/-- The antistable–marginal frame `eq:three-block`. -/
structure DareSystem (n₁ na nm m p : ℕ) where
  /-- Stabilizable-block dynamics. -/
  A₁ : Matrix (Fin n₁) (Fin n₁) ℝ
  /-- Coupling row `[A₁ₐ A₁ₘ]` into the uncontrollable block. -/
  A₁₂ : Matrix (Fin n₁) (Fin na ⊕ Fin nm) ℝ
  /-- Antistable block, `|λ| > 1`. -/
  Aa : Matrix (Fin na) (Fin na) ℝ
  /-- Marginal block, `|λ| = 1`. -/
  Am : Matrix (Fin nm) (Fin nm) ℝ
  /-- Noise input, stabilizable block only. -/
  G₁ : Matrix (Fin n₁) (Fin m) ℝ
  /-- Output map, stabilizable block. -/
  C₁ : Matrix (Fin p) (Fin n₁) ℝ
  /-- Output map, uncontrollable block `[Cₐ Cₘ]`. -/
  C₂ : Matrix (Fin p) (Fin na ⊕ Fin nm) ℝ
  /-- Process-noise covariance. -/
  Q : Matrix (Fin m) (Fin m) ℝ
  /-- Measurement-noise covariance. -/
  R : Matrix (Fin p) (Fin p) ℝ
  /-- Prior, stabilizable block. -/
  Sig₁ : Matrix (Fin n₁) (Fin n₁) ℝ
  /-- Prior, lumped uncontrollable block (aa/am/mm coupled). -/
  Sig₂ : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ
  hQ : Q.PosDef
  hR : R.PosDef
  hSig₁ : Sig₁.PosSemidef
  hSig₂ : Sig₂.PosSemidef
  hStab : IsStabilizable (complexify A₁) (complexify G₁)
  hAnti : ∀ μ ∈ spectrum ℂ (complexify Aa), 1 < ‖μ‖
  hMarg : ∀ μ ∈ spectrum ℂ (complexify Am), ‖μ‖ = 1

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-- The full state index `e₁ ⊕ (eₐ ⊕ eₘ)`. -/
abbrev ix (n₁ na nm : ℕ) := Fin n₁ ⊕ (Fin na ⊕ Fin nm)

/-- The uncontrollable block `A₂ = Aₐ ⊕ Aₘ` (`eq:A2-inv` carrier). -/
def A₂ : Matrix (Fin na ⊕ Fin nm) (Fin na ⊕ Fin nm) ℝ :=
  Matrix.fromBlocks S.Aa 0 0 S.Am

/-- The full state matrix. -/
def fullA : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  Matrix.fromBlocks S.A₁ S.A₁₂ 0 S.A₂

/-- The full noise input `col(G₁, 0)`. -/
def fullG : Matrix (ix n₁ na nm) (Fin m) ℝ :=
  Matrix.fromRows S.G₁ 0

/-- The full output map `[C₁ C₂]`. -/
def fullC : Matrix (Fin p) (ix n₁ na nm) ℝ :=
  Matrix.fromCols S.C₁ S.C₂

/-- The process-noise term `Q_w = GQGᵀ`. -/
noncomputable def Qw : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  S.fullG * S.Q * S.fullGᵀ

/-- The block-diagonal prior. -/
def Sig0 : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  Matrix.fromBlocks S.Sig₁ 0 0 S.Sig₂

/-- The covariance iterates from an arbitrary seed. -/
noncomputable def dareFrom (L : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) :
    ℕ → Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  dareIter S.fullC S.R S.fullA S.Qw L

/-- The covariance iterates from the prior (`eq:cov-rec`). -/
noncomputable def dare : ℕ → Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ :=
  S.dareFrom S.Sig0

/-! ### Basic structure facts -/

lemma Qw_posSemidef : S.Qw.PosSemidef := by
  have h := S.hQ.posSemidef.mul_mul_conjTranspose_same S.fullG
  rwa [show S.fullGᴴ = S.fullGᵀ from
    Matrix.conjTranspose_eq_transpose_of_trivial _] at h

/-- No process noise reaches the uncontrollable block. -/
lemma Qw_toBlocks₂₂ : S.Qw.toBlocks₂₂ = 0 := by
  ext i j
  unfold Qw fullG
  simp [Matrix.toBlocks₂₂, Matrix.mul_apply,
    Matrix.fromRows_apply_inr, Matrix.transpose_apply]

lemma Sig0_posSemidef : S.Sig0.PosSemidef := by
  unfold Sig0
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero, Matrix.conjTranspose_zero,
      S.hSig₁.1, S.hSig₂.1]
  · rw [star_trivial]
    have hd : x ⬝ᵥ (Matrix.fromBlocks S.Sig₁ 0 0 S.Sig₂ *ᵥ x)
        = quadForm S.Sig₁ (x ∘ Sum.inl) + quadForm S.Sig₂ (x ∘ Sum.inr) := by
      simp [quadForm, dotProduct, Matrix.mulVec, Fintype.sum_sum_type,
        Matrix.fromBlocks, Finset.mul_sum]
    rw [hd]
    exact add_nonneg (S.hSig₁.quadForm_nonneg _)
      (S.hSig₂.quadForm_nonneg _)

lemma Sig0_toBlocks₂₂ : S.Sig0.toBlocks₂₂ = S.Sig₂ := rfl

/-- A real matrix whose complexified spectrum misses `0` has nonzero
determinant. -/
lemma _root_.LinearSystems.det_ne_zero_of_zero_notMem_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℝ}
    (h : (0 : ℂ) ∉ spectrum ℂ (complexify M)) : M.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have h1 : complexify M *ᵥ complexifyVec v
      = (0 : ℂ) • complexifyVec v := by
    rw [complexify_mulVec, hv, zero_smul]
    funext i
    simp [complexifyVec]
  have h2 : complexifyVec v ≠ 0 := by
    intro h0
    apply hvne
    funext i
    have h3 := congrFun h0 i
    simpa [complexifyVec] using h3
  exact h (mem_spectrum_of_mulVec_eq_smul h2 h1)

/-- The uncontrollable block is nonsingular (`eq:A2-inv`):
`|λ(A₂)| ≥ 1` throughout, so `det A₂ ≠ 0`. -/
lemma isUnit_A₂_det : IsUnit S.A₂.det := by
  rw [isUnit_iff_ne_zero]
  have hdet : S.A₂.det = S.Aa.det * S.Am.det := by
    unfold A₂
    rw [Matrix.det_fromBlocks_zero₂₁]
  rw [hdet]
  refine mul_ne_zero
    (LinearSystems.det_ne_zero_of_zero_notMem_spectrum fun h0 => ?_)
    (LinearSystems.det_ne_zero_of_zero_notMem_spectrum fun h0 => ?_)
  · have := S.hAnti 0 h0
    rw [norm_zero] at this
    linarith
  · have := S.hMarg 0 h0
    rw [norm_zero] at this
    linarith

/-! ### The conditions -/

/-- **C1**: `(A, C)` detectable (the paper's standing hypothesis). -/
def C1 : Prop :=
  IsDetectable (complexify S.fullA) (complexify S.fullC)

/-- **C2** in kernel form: the prior kernel misses the whole
uncontrollable coordinate subspace `𝒳_{u,uc}` (the `e₂` coordinates
in this frame). -/
def C2 : Prop :=
  ∀ w : Fin na ⊕ Fin nm → ℝ,
    S.Sig0 *ᵥ Sum.elim (0 : Fin n₁ → ℝ) w = 0 → w = 0

/-- **C2w** in kernel form: the prior kernel misses the antistable
coordinate subspace `𝒳_{a,uc}` (the `eₐ` coordinates). -/
def C2w : Prop :=
  ∀ w : Fin na → ℝ,
    S.Sig0 *ᵥ Sum.elim (0 : Fin n₁ → ℝ)
      (Sum.elim w (0 : Fin nm → ℝ)) = 0 → w = 0

/-- **C3w**: no marginal block. -/
def C3w : Prop := nm = 0

/-- The antistable diagonal block of the prior, `Σₐ`. -/
def Siga : Matrix (Fin na) (Fin na) ℝ := S.Sig₂.toBlocks₁₁

/-! ### The prior-positivity criteria (`eq:prior-pos`) -/

lemma Sig0_mulVec_elim (w : Fin na ⊕ Fin nm → ℝ) :
    S.Sig0 *ᵥ Sum.elim (0 : Fin n₁ → ℝ) w
      = Sum.elim (0 : Fin n₁ → ℝ) (S.Sig₂ *ᵥ w) := by
  unfold Sig0
  rw [Matrix.fromBlocks_mulVec]
  simp

/-- **`eq:prior-pos`(a)**: C2 is exactly positive-definiteness of the
lumped uncontrollable prior block. -/
theorem criterion : S.C2 ↔ S.Sig₂.PosDef := by
  constructor
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos S.hSig₂.1 fun w hw => ?_
    rcases lt_or_eq_of_le (S.hSig₂.quadForm_nonneg w) with hq | hq
    · exact hq
    · exfalso
      have hker : S.Sig₂ *ᵥ w = 0 :=
        S.hSig₂.mulVec_eq_zero_of_quadForm_eq_zero hq.symm
      refine hw (h w ?_)
      rw [Sig0_mulVec_elim, hker]
      simp
  · intro h w hw
    have h2 : S.Sig₂ *ᵥ w = 0 := by
      rw [Sig0_mulVec_elim] at hw
      funext j
      simpa using congrFun hw (Sum.inr j)
    by_contra hne
    have hpos := h.quadForm_pos hne
    rw [quadForm, h2, dotProduct_zero] at hpos
    exact lt_irrefl 0 hpos

/-- **`eq:prior-pos`(b) = `lem:criterion-w`**: C2w is exactly
positive-definiteness of the antistable diagonal prior block `Σₐ` —
equivalently, finiteness of the antistable information seed. -/
theorem criterion_w : S.C2w ↔ S.Siga.PosDef := by
  have hSiga : S.Siga.PosSemidef := toBlocks₁₁_posSemidef S.hSig₂
  constructor
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hSiga.1 fun v hv => ?_
    rcases lt_or_eq_of_le (hSiga.quadForm_nonneg v) with hq | hq
    · exact hq
    · exfalso
      have hq2 : quadForm S.Sig₂ (Sum.elim v (0 : Fin nm → ℝ)) = 0 := by
        rw [quadForm_elim_zero']
        exact hq.symm
      have hker : S.Sig₂ *ᵥ Sum.elim v (0 : Fin nm → ℝ) = 0 :=
        S.hSig₂.mulVec_eq_zero_of_quadForm_eq_zero hq2
      refine hv (h v ?_)
      rw [Sig0_mulVec_elim, hker]
      simp
  · intro h w hw
    have h2 : S.Sig₂ *ᵥ Sum.elim w (0 : Fin nm → ℝ) = 0 := by
      rw [Sig0_mulVec_elim] at hw
      funext j
      simpa using congrFun hw (Sum.inr j)
    have hq : quadForm S.Siga w = 0 := by
      unfold Siga
      rw [← quadForm_elim_zero', quadForm, h2, dotProduct_zero]
    by_contra hne
    exact absurd hq (ne_of_gt (h.quadForm_pos hne))

/-- C2 implies C2w (`𝒳_{a,uc} ⊆ 𝒳_{u,uc}`). -/
theorem C2w_of_C2 (h : S.C2) : S.C2w := by
  intro w hw
  have h1 := h (Sum.elim w (0 : Fin nm → ℝ)) hw
  funext i
  simpa using congrFun h1 (Sum.inl i)

end DareSystem

end Dare
end Estimation