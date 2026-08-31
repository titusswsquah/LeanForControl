import LeanForControl.Estimation.Dare.Update
import Architect

/-!
# The gap engine (`a02-machinery`-3)

The difference identity `eq:diff-id`
`R(Σ₁) − R(Σ₂) = F(Σ₁)(Σ₁−Σ₂)F(Σ₂)ᵀ`, its unrolled form
`eq:diff-unroll` along two trajectories, and the from-above
gap-Riccati `eq:gap-ric`
`R(Σ∞+V) − Σ∞ = F∞(V − VCᵀS_V⁻¹CV)F∞ᵀ ⪯ F∞VF∞ᵀ` at a fixed point.

The route to `eq:diff-id` is a four-line calc resting on the gain
identity `U(Σ)Cᵀ = K(Σ)R`:
`M₁(Σ₁−Σ₂)M₂ᵀ = U₁M₂ᵀ − M₁U₂ = (U₁ − K₁RK₂ᵀ) − (U₂ − K₁RK₂ᵀ)`.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ} {Sg : Matrix ι ι ℝ}

variable (C R) in
/-- The error map `F(Σ) = A(I − K(Σ)C)` (`eq:filter`). -/
noncomputable def errMap (A Sg : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  A * (1 - kGain C R Sg * C)

variable (C R) in
/-- The error-map transition products along a trajectory
(`Φ_T = F(Σ_{T−1})⋯F(Σ₀)`, newest factor first). -/
noncomputable def errProd (A Qw L : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => 1
  | T + 1 => errMap C R A (dareIter C R A Qw L T) * errProd A Qw L T

@[simp]
lemma errProd_zero (A Qw L : Matrix ι ι ℝ) :
    errProd C R A Qw L 0 = 1 := rfl

lemma errProd_succ (A Qw L : Matrix ι ι ℝ) (T : ℕ) :
    errProd C R A Qw L (T + 1)
      = errMap C R A (dareIter C R A Qw L T)
        * errProd C R A Qw L T := rfl

/-! ### The gain identity `U(Σ)Cᵀ = K(Σ)R` and its consequences -/

/-- `U(Σ)·Cᵀ = K(Σ)·R`. -/
lemma updM_mul_Ct (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    updM C R Sg * Cᵀ = kGain C R Sg * R := by
  have hCS : C * Sg * Cᵀ = innov C R Sg - R := by
    unfold innov; abel
  unfold updM kGain
  rw [Matrix.sub_mul,
    Matrix.mul_assoc (Sg * Cᵀ * (innov C R Sg)⁻¹) (C * Sg) Cᵀ,
    show C * Sg * Cᵀ = innov C R Sg - R from hCS,
    Matrix.mul_sub,
    Matrix.mul_assoc (Sg * Cᵀ) ((innov C R Sg)⁻¹) (innov C R Sg),
    innov_inv_mul hR hSg, Matrix.mul_one]
  abel

/-- `C·U(Σ) = R·K(Σ)ᵀ`. -/
lemma C_mul_updM (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    C * updM C R Sg = R * (kGain C R Sg)ᵀ := by
  have h := congrArg Matrix.transpose (updM_mul_Ct (C := C) hR hSg)
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose,
    (updM_isHermitian hR hSg).transpose_eq_self,
    hR.1.transpose_eq_self] at h
  exact h

/-- `U(Σ) = (I − K(Σ)C)·Σ`. -/
lemma updM_eq_oneSubKC_mul :
    updM C R Sg = (1 - kGain C R Sg * C) * Sg := by
  rw [updM_eq_mul]; rfl

/-- `U(Σ) = Σ·(I − K(Σ)C)ᵀ`. -/
lemma updM_eq_mul_oneSubKCt (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    updM C R Sg = Sg * (1 - kGain C R Sg * C)ᵀ := by
  have h := congrArg Matrix.transpose
    (updM_eq_oneSubKC_mul (C := C) (R := R) (Sg := Sg))
  rw [(updM_isHermitian hR hSg).transpose_eq_self, Matrix.transpose_mul,
    hSg.1.transpose_eq_self] at h
  exact h

/-! ### The difference identity (`eq:diff-id`) -/

/-- The update-level difference identity:
`U(Σ₁) − U(Σ₂) = (I−K₁C)(Σ₁−Σ₂)(I−K₂C)ᵀ`. -/
lemma updM_diff {Sg₁ Sg₂ : Matrix ι ι ℝ} (hR : R.PosDef)
    (hSg₁ : Sg₁.PosSemidef) (hSg₂ : Sg₂.PosSemidef) :
    updM C R Sg₁ - updM C R Sg₂
      = (1 - kGain C R Sg₁ * C) * (Sg₁ - Sg₂)
          * (1 - kGain C R Sg₂ * C)ᵀ := by
  have hexp : (1 - kGain C R Sg₁ * C) * (Sg₁ - Sg₂)
        * (1 - kGain C R Sg₂ * C)ᵀ
      = updM C R Sg₁ * (1 - kGain C R Sg₂ * C)ᵀ
        - (1 - kGain C R Sg₁ * C) * updM C R Sg₂ := by
    rw [Matrix.mul_sub (1 - kGain C R Sg₁ * C) Sg₁ Sg₂,
      Matrix.sub_mul ((1 - kGain C R Sg₁ * C) * Sg₁)
        ((1 - kGain C R Sg₁ * C) * Sg₂) (1 - kGain C R Sg₂ * C)ᵀ,
      ← updM_eq_oneSubKC_mul,
      Matrix.mul_assoc (1 - kGain C R Sg₁ * C) Sg₂
        (1 - kGain C R Sg₂ * C)ᵀ,
      ← updM_eq_mul_oneSubKCt hR hSg₂]
  have h1 : updM C R Sg₁ * (1 - kGain C R Sg₂ * C)ᵀ
      = updM C R Sg₁
        - kGain C R Sg₁ * R * (kGain C R Sg₂)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
      Matrix.mul_sub, Matrix.mul_one,
      ← Matrix.mul_assoc (updM C R Sg₁) Cᵀ (kGain C R Sg₂)ᵀ,
      updM_mul_Ct hR hSg₁]
  have h2 : (1 - kGain C R Sg₁ * C) * updM C R Sg₂
      = updM C R Sg₂
        - kGain C R Sg₁ * R * (kGain C R Sg₂)ᵀ := by
    rw [Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc (kGain C R Sg₁) C (updM C R Sg₂),
      C_mul_updM hR hSg₂,
      ← Matrix.mul_assoc (kGain C R Sg₁) R (kGain C R Sg₂)ᵀ]
  rw [hexp, h1, h2]
  abel

/-- **The difference identity** (`eq:diff-id`):
`R(Σ₁) − R(Σ₂) = F(Σ₁)(Σ₁−Σ₂)F(Σ₂)ᵀ`. -/
theorem dareStep_diff {A Qw Sg₁ Sg₂ : Matrix ι ι ℝ} (hR : R.PosDef)
    (hSg₁ : Sg₁.PosSemidef) (hSg₂ : Sg₂.PosSemidef) :
    dareStep C R A Qw Sg₁ - dareStep C R A Qw Sg₂
      = errMap C R A Sg₁ * (Sg₁ - Sg₂) * (errMap C R A Sg₂)ᵀ := by
  have h : dareStep C R A Qw Sg₁ - dareStep C R A Qw Sg₂
      = A * (updM C R Sg₁ - updM C R Sg₂) * Aᵀ := by
    unfold dareStep
    rw [Matrix.mul_sub A (updM C R Sg₁) (updM C R Sg₂), Matrix.sub_mul]
    abel
  rw [h, updM_diff hR hSg₁ hSg₂]
  unfold errMap
  rw [Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- **The unrolled difference** (`eq:diff-unroll`):
`Σ_T(L₁) − Σ_T(L₂) = Φ_T(L₁)·(L₁−L₂)·Φ_T(L₂)ᵀ`. -/
theorem dareIter_diff {A Qw L₁ L₂ : Matrix ι ι ℝ} (hR : R.PosDef)
    (hQw : Qw.PosSemidef) (hL₁ : L₁.PosSemidef) (hL₂ : L₂.PosSemidef) :
    ∀ T, dareIter C R A Qw L₁ T - dareIter C R A Qw L₂ T
      = errProd C R A Qw L₁ T * (L₁ - L₂)
          * (errProd C R A Qw L₂ T)ᵀ
  | 0 => by simp
  | T + 1 => by
    rw [dareIter_succ, dareIter_succ,
      dareStep_diff hR (dareIter_posSemidef hR hQw hL₁ T)
        (dareIter_posSemidef hR hQw hL₂ T),
      dareIter_diff hR hQw hL₁ hL₂ T,
      errProd_succ, errProd_succ, Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

/-! ### The from-above gap-Riccati (`eq:gap-ric`) -/

/-- The gain factorization about a base covariance:
`I − K(Σ+V)C = (I − K(Σ)C)(I − VCᵀS(Σ+V)⁻¹C)`. -/
lemma oneSubKC_add (hR : R.PosDef) (hSg : Sg.PosSemidef)
    {V : Matrix ι ι ℝ} (hV : V.PosSemidef) :
    1 - kGain C R (Sg + V) * C
      = (1 - kGain C R Sg * C)
        * (1 - V * Cᵀ * (innov C R (Sg + V))⁻¹ * C) := by
  have hSV : (Sg + V).PosSemidef := hSg.add hV
  have hCVC : C * V * Cᵀ = innov C R (Sg + V) - innov C R Sg := by
    unfold innov
    rw [Matrix.mul_add C Sg V, Matrix.add_mul]
    abel
  have hKCW : kGain C R Sg * C * (V * Cᵀ * (innov C R (Sg + V))⁻¹ * C)
      = kGain C R Sg * C
        - Sg * Cᵀ * (innov C R (Sg + V))⁻¹ * C := by
    have h1 : kGain C R Sg * C * (V * Cᵀ * (innov C R (Sg + V))⁻¹ * C)
        = kGain C R Sg * (C * V * Cᵀ)
            * ((innov C R (Sg + V))⁻¹ * C) := by
      simp only [Matrix.mul_assoc]
    rw [h1, hCVC, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc (kGain C R Sg) (innov C R (Sg + V)) _,
      ← Matrix.mul_assoc (innov C R (Sg + V)) _ C,
      innov_mul_inv hR hSV, Matrix.one_mul,
      kGain_mul_innov hR hSg]
    simp only [Matrix.mul_assoc]
  have hKplus : kGain C R (Sg + V) * C
      = Sg * Cᵀ * (innov C R (Sg + V))⁻¹ * C
        + V * Cᵀ * (innov C R (Sg + V))⁻¹ * C := by
    unfold kGain
    rw [Matrix.add_mul Sg V Cᵀ, Matrix.add_mul, Matrix.add_mul]
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul,
    hKCW, hKplus]
  abel

/-- **The gap-Riccati identity** (`eq:gap-ric`): at a fixed point `Σ∞`,
`R(Σ∞+V) − Σ∞ = F∞·(V − VCᵀS_V⁻¹CV)·F∞ᵀ`. -/
theorem gapRic {A Qw Sinf V : Matrix ι ι ℝ} (hR : R.PosDef)
    (hSinf : Sinf.PosSemidef) (hV : V.PosSemidef)
    (hfix : dareStep C R A Qw Sinf = Sinf) :
    dareStep C R A Qw (Sinf + V) - Sinf
      = errMap C R A Sinf
        * (V - V * Cᵀ * (innov C R (Sinf + V))⁻¹ * (C * V))
        * (errMap C R A Sinf)ᵀ := by
  have hSV : (Sinf + V).PosSemidef := hSinf.add hV
  have h1 : dareStep C R A Qw (Sinf + V) - Sinf
      = errMap C R A (Sinf + V) * V * (errMap C R A Sinf)ᵀ := by
    have h0 := dareStep_diff (C := C) (A := A) (Qw := Qw) hR hSV hSinf
    rw [add_sub_cancel_left, hfix] at h0
    exact h0
  rw [h1]
  unfold errMap
  rw [oneSubKC_add hR hSinf hV]
  have h2 : V - V * Cᵀ * (innov C R (Sinf + V))⁻¹ * (C * V)
      = (1 - V * Cᵀ * (innov C R (Sinf + V))⁻¹ * C) * V := by
    rw [Matrix.sub_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  rw [h2]
  simp only [Matrix.mul_assoc]

/-- **The from-above domination** (`eq:gap-ric`, inequality form):
`R(Σ∞+V) − Σ∞ ⪯ F∞VF∞ᵀ` — above the fixed point, the gap is dominated
by the fixed loop. -/
theorem gapRic_le {A Qw Sinf V : Matrix ι ι ℝ} (hR : R.PosDef)
    (hSinf : Sinf.PosSemidef) (hV : V.PosSemidef)
    (hfix : dareStep C R A Qw Sinf = Sinf) :
    (errMap C R A Sinf * V * (errMap C R A Sinf)ᵀ
      - (dareStep C R A Qw (Sinf + V) - Sinf)).PosSemidef := by
  rw [gapRic hR hSinf hV hfix]
  have heq : errMap C R A Sinf * V * (errMap C R A Sinf)ᵀ
      - errMap C R A Sinf
          * (V - V * Cᵀ * (innov C R (Sinf + V))⁻¹ * (C * V))
          * (errMap C R A Sinf)ᵀ
      = errMap C R A Sinf * V * Cᵀ * (innov C R (Sinf + V))⁻¹
          * (errMap C R A Sinf * V * Cᵀ)ᵀ := by
    rw [Matrix.mul_sub (errMap C R A Sinf) V _, Matrix.sub_mul]
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hV.1.transpose_eq_self]
    simp only [Matrix.mul_assoc]
    abel
  rw [heq]
  have hSV : (Sinf + V).PosSemidef := hSinf.add hV
  have h := ((innov_posDef (C := C) hR hSV).inv.posSemidef).mul_mul_conjTranspose_same
    (errMap C R A Sinf * V * Cᵀ)
  rwa [show (errMap C R A Sinf * V * Cᵀ)ᴴ
      = (errMap C R A Sinf * V * Cᵀ)ᵀ from
    Matrix.conjTranspose_eq_transpose_of_trivial _] at h

end Dare
end Estimation