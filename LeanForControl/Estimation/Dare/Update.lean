import LeanForControl.Estimation.KalmanFilter
import Architect

/-!
# The measurement update and the comparison principle

Index-generic machinery for the covariance recursion of the odyssey
development (`a02-machinery`): the measurement update
`U(Σ) = Σ − ΣCᵀ(CΣCᵀ+R)⁻¹CΣ`, its Joseph-form variational
characterization, the resulting Löwner monotonicity in the initial
condition (`eq:comparison` — the one result the paper imports), the
update contraction `U(Σ) ⪯ Σ`, and kernel preservation
(`fact:update-kernel`), all pseudoinverse-free on the `Σ` side.

Everything is stated over an arbitrary finite index type because the
odyssey frame lives on `Fin n₁ ⊕ (Fin nₐ ⊕ Fin n_m)`; the Fin-bound
`GeneralSystem.measM` layer of `KalmanFilter.lean` is the same
mathematics at `ι = Fin n` (with inverse weights `Ri = R⁻¹` carried as
data there).
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (C : Matrix κ ι ℝ) (R : Matrix κ κ ℝ)

/-- The innovation covariance `S(Σ) = CΣCᵀ + R`. -/
noncomputable def innov (Sg : Matrix ι ι ℝ) : Matrix κ κ ℝ :=
  C * Sg * Cᵀ + R

/-- The measurement update `U(Σ) = Σ − ΣCᵀS(Σ)⁻¹CΣ` (`eq:Rmap`). -/
noncomputable def updM (Sg : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  Sg - Sg * Cᵀ * (innov C R Sg)⁻¹ * (C * Sg)

/-- One covariance step `R(Σ) = A·U(Σ)·Aᵀ + Q_w` (`eq:Rmap`). -/
noncomputable def dareStep (A Qw Sg : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  A * updM C R Sg * Aᵀ + Qw

/-- The covariance iterates from a seed (`eq:cov-rec`, seed-general). -/
noncomputable def dareIter (A Qw L : Matrix ι ι ℝ) :
    ℕ → Matrix ι ι ℝ
  | 0 => L
  | T + 1 => dareStep C R A Qw (dareIter A Qw L T)

@[simp]
lemma dareIter_zero (A Qw L : Matrix ι ι ℝ) :
    dareIter C R A Qw L 0 = L := rfl

lemma dareIter_succ (A Qw L : Matrix ι ι ℝ) (T : ℕ) :
    dareIter C R A Qw L (T + 1)
      = dareStep C R A Qw (dareIter C R A Qw L T) := rfl

variable {C R}
variable {Sg : Matrix ι ι ℝ}

/-! ### The innovation covariance -/

lemma innov_posDef (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    (innov C R Sg).PosDef := by
  unfold innov
  have h1 : (C * Sg * Cᵀ).PosSemidef := by
    have h2 := hSg.mul_mul_conjTranspose_same C
    rwa [show Cᴴ = Cᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h2
  exact Matrix.PosDef.posSemidef_add h1 hR

lemma innov_transpose (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    (innov C R Sg)ᵀ = innov C R Sg :=
  (innov_posDef hR hSg).1.transpose_eq_self

lemma innov_mul_inv (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    innov C R Sg * (innov C R Sg)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (innov_posDef hR hSg).isUnit)

lemma innov_inv_mul (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    (innov C R Sg)⁻¹ * innov C R Sg = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
    (innov_posDef hR hSg).isUnit)

lemma innov_inv_transpose (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    ((innov C R Sg)⁻¹)ᵀ = (innov C R Sg)⁻¹ := by
  rw [Matrix.transpose_nonsing_inv, innov_transpose hR hSg]

/-! ### The Joseph form: the update as a gain minimization

`joseph K Σ = (I−KC)Σ(I−KC)ᵀ + KRKᵀ` is the covariance of the
`K`-gain estimator; the update is its minimum over `K`, attained at
the Kalman gain `K* = ΣCᵀS⁻¹`. This is the variational
characterization that makes the update — hence the whole recursion —
monotone in the Löwner order. -/

variable (C R) in
/-- The Joseph (fixed-gain) form. -/
noncomputable def joseph (K : Matrix ι κ ℝ) (Sg : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  (1 - K * C) * Sg * (1 - K * C)ᵀ + K * R * Kᵀ

variable (C R) in
/-- The Kalman gain `K* = ΣCᵀS⁻¹`. -/
noncomputable def kGain (Sg : Matrix ι ι ℝ) : Matrix ι κ ℝ :=
  Sg * Cᵀ * (innov C R Sg)⁻¹

variable (C R) in
/-- Expansion of the Joseph form (pure distribution, no hypotheses):
`joseph K Σ = Σ − K(CΣ) − ΣCᵀKᵀ + K·S(Σ)·Kᵀ`. -/
lemma joseph_eq (K : Matrix ι κ ℝ) (Sg : Matrix ι ι ℝ) :
    joseph C R K Sg
      = Sg - K * (C * Sg) - Sg * Cᵀ * Kᵀ + K * innov C R Sg * Kᵀ := by
  unfold joseph innov
  simp only [Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_mul, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_assoc]
  abel

/-- `S(Σ)·K*ᵀ = CΣ`. -/
lemma innov_mul_kGainT (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    innov C R Sg * (kGain C R Sg)ᵀ = C * Sg := by
  unfold kGain
  rw [Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose, innov_inv_transpose hR hSg,
    hSg.1.transpose_eq_self, ← Matrix.mul_assoc,
    Matrix.mul_assoc _ ((innov C R Sg)⁻¹) _,
    ← Matrix.mul_assoc (innov C R Sg) _ _,
    innov_mul_inv hR hSg, Matrix.one_mul]

/-- `K*·S(Σ) = ΣCᵀ`. -/
lemma kGain_mul_innov (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    kGain C R Sg * innov C R Sg = Sg * Cᵀ := by
  unfold kGain
  rw [Matrix.mul_assoc, innov_inv_mul hR hSg, Matrix.mul_one]

/-- The update is the Joseph form at the Kalman gain, and every other
gain exceeds it by the innovation-weighted gain error:
`joseph K Σ − U(Σ) = (K−K*)·S(Σ)·(K−K*)ᵀ`. -/
lemma joseph_sub_updM (hR : R.PosDef) (hSg : Sg.PosSemidef)
    (K : Matrix ι κ ℝ) :
    joseph C R K Sg - updM C R Sg
      = (K - kGain C R Sg) * innov C R Sg
          * (K - kGain C R Sg)ᵀ := by
  have hSKt : innov C R Sg * (kGain C R Sg)ᵀ = C * Sg :=
    innov_mul_kGainT hR hSg
  have hKS : kGain C R Sg * innov C R Sg = Sg * Cᵀ :=
    kGain_mul_innov hR hSg
  have hKSKt : kGain C R Sg * innov C R Sg
      * (kGain C R Sg)ᵀ
      = Sg * Cᵀ * (innov C R Sg)⁻¹ * (C * Sg) := by
    rw [hKS]
    unfold kGain
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, innov_inv_transpose hR hSg,
      hSg.1.transpose_eq_self]
    simp only [Matrix.mul_assoc]
  have hRHS : (K - kGain C R Sg) * innov C R Sg * (K - kGain C R Sg)ᵀ
      = K * innov C R Sg * Kᵀ - K * (C * Sg) - Sg * Cᵀ * Kᵀ
        + Sg * Cᵀ * (innov C R Sg)⁻¹ * (C * Sg) := by
    simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
    rw [Matrix.mul_assoc K (innov C R Sg) (kGain C R Sg)ᵀ, hSKt,
      hKSKt, hKS]
    abel
  rw [joseph_eq, updM, hRHS]
  abel

/-- The update is the Joseph form at the Kalman gain. -/
lemma updM_eq_joseph (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    updM C R Sg = joseph C R (kGain C R Sg) Sg := by
  have h := joseph_sub_updM (C := C) hR hSg (kGain C R Sg)
  rw [sub_self, Matrix.zero_mul, Matrix.zero_mul] at h
  exact (sub_eq_zero.mp h).symm

/-! ### PSD, symmetry, contraction -/

/-- The Joseph form is PSD for every gain. -/
lemma joseph_posSemidef (hR : R.PosDef) (hSg : Sg.PosSemidef)
    (K : Matrix ι κ ℝ) : (joseph C R K Sg).PosSemidef := by
  unfold joseph
  have h1 : ((1 - K * C) * Sg * (1 - K * C)ᵀ).PosSemidef := by
    have h := hSg.mul_mul_conjTranspose_same (1 - K * C)
    rwa [show (1 - K * C)ᴴ = (1 - K * C)ᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h
  have h2 : (K * R * Kᵀ).PosSemidef := by
    have h := hR.posSemidef.mul_mul_conjTranspose_same K
    rwa [show Kᴴ = Kᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h
  exact h1.add h2

/-- The update stays PSD. -/
lemma updM_posSemidef (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    (updM C R Sg).PosSemidef := by
  rw [updM_eq_joseph hR hSg]
  exact joseph_posSemidef hR hSg _

/-- The update is symmetric. -/
lemma updM_isHermitian (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    (updM C R Sg).IsHermitian :=
  (updM_posSemidef hR hSg).1

/-- **The update contracts**: `Σ − U(Σ) = ΣCᵀS⁻¹CΣ ⪰ 0`. -/
lemma sub_updM_posSemidef (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    (Sg - updM C R Sg).PosSemidef := by
  have heq : Sg - updM C R Sg
      = Sg * Cᵀ * (innov C R Sg)⁻¹ * (Sg * Cᵀ)ᵀ := by
    unfold updM
    rw [Matrix.transpose_mul, Matrix.transpose_transpose,
      hSg.1.transpose_eq_self]
    abel
  rw [heq]
  have h := ((innov_posDef (C := C) hR hSg).inv.posSemidef).mul_mul_conjTranspose_same
    (Sg * Cᵀ)
  rwa [show (Sg * Cᵀ)ᴴ = (Sg * Cᵀ)ᵀ from
    Matrix.conjTranspose_eq_transpose_of_trivial _] at h

/-! ### The key identity and kernel preservation (`fact:update-kernel`) -/

/-- The factored form `U(Σ) = (I − ΣCᵀS⁻¹C)·Σ`. -/
lemma updM_eq_mul :
    updM C R Sg = (1 - Sg * Cᵀ * (innov C R Sg)⁻¹ * C) * Sg := by
  unfold updM
  rw [Matrix.sub_mul, Matrix.one_mul]
  simp only [Matrix.mul_assoc]

/-- **The key identity** `U(Σ)·(I + CᵀR⁻¹CΣ) = Σ` (inverse-free on the
`Σ` side; the analogue of `GeneralSystem.measM_mul_key`). -/
lemma updM_key (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    updM C R Sg * (1 + Cᵀ * R⁻¹ * (C * Sg)) = Sg := by
  have hRinv : R * R⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      hR.isUnit)
  have hbr : R⁻¹ - (innov C R Sg)⁻¹
      - (innov C R Sg)⁻¹ * (C * Sg * Cᵀ) * R⁻¹ = 0 := by
    have h1 : (1 : Matrix κ κ ℝ) + C * Sg * Cᵀ * R⁻¹
        = innov C R Sg * R⁻¹ := by
      unfold innov
      rw [Matrix.add_mul, hRinv]
      abel
    calc R⁻¹ - (innov C R Sg)⁻¹
          - (innov C R Sg)⁻¹ * (C * Sg * Cᵀ) * R⁻¹
        = R⁻¹ - (innov C R Sg)⁻¹ * (1 + C * Sg * Cᵀ * R⁻¹) := by
          rw [Matrix.mul_add, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
          abel
      _ = R⁻¹ - (innov C R Sg)⁻¹ * (innov C R Sg * R⁻¹) := by rw [h1]
      _ = 0 := by
          rw [← Matrix.mul_assoc, innov_inv_mul hR hSg,
            Matrix.one_mul, sub_self]
  have hexpand : updM C R Sg * (1 + Cᵀ * R⁻¹ * (C * Sg)) - Sg
      = Sg * Cᵀ * (R⁻¹ - (innov C R Sg)⁻¹
          - (innov C R Sg)⁻¹ * (C * Sg * Cᵀ) * R⁻¹)
        * (C * Sg) := by
    unfold updM
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
    abel
  rw [hbr, Matrix.mul_zero, Matrix.zero_mul] at hexpand
  exact sub_eq_zero.mp hexpand

/-- The transposed key identity `(I + ΣCᵀR⁻¹C)·U(Σ) = Σ`. -/
lemma updM_key' (hR : R.PosDef) (hSg : Sg.PosSemidef) :
    (1 + Sg * (Cᵀ * (R⁻¹ * C))) * updM C R Sg = Sg := by
  have hRit : (R⁻¹)ᵀ = R⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hR.1.transpose_eq_self]
  have h := congrArg Matrix.transpose (updM_key (C := C) hR hSg)
  rw [Matrix.transpose_mul, hSg.1.transpose_eq_self] at h
  have h2 : (1 + Cᵀ * R⁻¹ * (C * Sg))ᵀ
      = 1 + Sg * (Cᵀ * (R⁻¹ * C)) := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
    congr 1
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      hSg.1.transpose_eq_self, hRit]
    simp only [Matrix.mul_assoc]
  rw [h2, (updM_isHermitian hR hSg).transpose_eq_self] at h
  exact h

/-- **Kernel preservation** (`fact:update-kernel`):
`U(Σ)v = 0 ↔ Σv = 0`. -/
lemma updM_mulVec_eq_zero_iff (hR : R.PosDef) (hSg : Sg.PosSemidef)
    {v : ι → ℝ} : updM C R Sg *ᵥ v = 0 ↔ Sg *ᵥ v = 0 := by
  constructor
  · intro h
    have h1 := congrArg (fun M => M *ᵥ v) (updM_key' (C := C) hR hSg)
    simp only at h1
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero] at h1
    exact h1.symm
  · intro h
    rw [updM_eq_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-! ### Monotonicity and the comparison principle (`eq:comparison`) -/

/-- The Joseph form is monotone in `Σ` for a fixed gain. -/
lemma joseph_mono {Sg₁ Sg₂ : Matrix ι ι ℝ}
    (h12 : (Sg₂ - Sg₁).PosSemidef) (K : Matrix ι κ ℝ) :
    (joseph C R K Sg₂ - joseph C R K Sg₁).PosSemidef := by
  have heq : joseph C R K Sg₂ - joseph C R K Sg₁
      = (1 - K * C) * (Sg₂ - Sg₁) * (1 - K * C)ᵀ := by
    unfold joseph
    rw [Matrix.mul_sub (1 - K * C) Sg₂ Sg₁,
      Matrix.sub_mul ((1 - K * C) * Sg₂) ((1 - K * C) * Sg₁)
        (1 - K * C)ᵀ]
    abel
  rw [heq]
  have h := h12.mul_mul_conjTranspose_same (1 - K * C)
  rwa [show (1 - K * C)ᴴ = (1 - K * C)ᵀ from
    Matrix.conjTranspose_eq_transpose_of_trivial _] at h

/-- **The update is monotone in the Löwner order.** -/
lemma updM_mono {Sg₁ Sg₂ : Matrix ι ι ℝ} (hR : R.PosDef)
    (hSg₁ : Sg₁.PosSemidef) (hSg₂ : Sg₂.PosSemidef)
    (h12 : (Sg₂ - Sg₁).PosSemidef) :
    (updM C R Sg₂ - updM C R Sg₁).PosSemidef := by
  have hsplit : updM C R Sg₂ - updM C R Sg₁
      = (joseph C R (kGain C R Sg₂) Sg₂
          - joseph C R (kGain C R Sg₂) Sg₁)
        + (joseph C R (kGain C R Sg₂) Sg₁
          - updM C R Sg₁) := by
    rw [updM_eq_joseph hR hSg₂]
    abel
  rw [hsplit]
  refine Matrix.PosSemidef.add (joseph_mono h12 _) ?_
  rw [joseph_sub_updM hR hSg₁]
  have h := ((innov_posDef (C := C) hR hSg₁).posSemidef).mul_mul_conjTranspose_same
    (kGain C R Sg₂ - kGain C R Sg₁)
  rwa [show (kGain C R Sg₂ - kGain C R Sg₁)ᴴ
      = (kGain C R Sg₂ - kGain C R Sg₁)ᵀ from
    Matrix.conjTranspose_eq_transpose_of_trivial _] at h

/-- One covariance step preserves PSD. -/
lemma dareStep_posSemidef {A Qw : Matrix ι ι ℝ} (hR : R.PosDef)
    (hQw : Qw.PosSemidef) (hSg : Sg.PosSemidef) :
    (dareStep C R A Qw Sg).PosSemidef := by
  unfold dareStep
  have h1 : (A * updM C R Sg * Aᵀ).PosSemidef := by
    have h := (updM_posSemidef (C := C) hR hSg).mul_mul_conjTranspose_same A
    rwa [show Aᴴ = Aᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h
  exact h1.add hQw

/-- One covariance step is monotone in the Löwner order. -/
lemma dareStep_mono {A Qw Sg₁ Sg₂ : Matrix ι ι ℝ} (hR : R.PosDef)
    (hSg₁ : Sg₁.PosSemidef) (hSg₂ : Sg₂.PosSemidef)
    (h12 : (Sg₂ - Sg₁).PosSemidef) :
    (dareStep C R A Qw Sg₂ - dareStep C R A Qw Sg₁).PosSemidef := by
  have heq : dareStep C R A Qw Sg₂ - dareStep C R A Qw Sg₁
      = A * (updM C R Sg₂ - updM C R Sg₁) * Aᵀ := by
    unfold dareStep
    rw [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [heq]
  have h := (updM_mono (C := C) hR hSg₁ hSg₂ h12).mul_mul_conjTranspose_same A
  rwa [show Aᴴ = Aᵀ from
    Matrix.conjTranspose_eq_transpose_of_trivial _] at h

/-- The iterates stay PSD. -/
lemma dareIter_posSemidef {A Qw L : Matrix ι ι ℝ} (hR : R.PosDef)
    (hQw : Qw.PosSemidef) (hL : L.PosSemidef) :
    ∀ T, (dareIter C R A Qw L T).PosSemidef
  | 0 => hL
  | T + 1 => dareStep_posSemidef hR hQw (dareIter_posSemidef hR hQw hL T)

/-- **The comparison principle** (`eq:comparison`): the recursion is
monotone in the initial condition, at every horizon. -/
theorem dareIter_mono {A Qw L₁ L₂ : Matrix ι ι ℝ} (hR : R.PosDef)
    (hQw : Qw.PosSemidef) (hL₁ : L₁.PosSemidef) (hL₂ : L₂.PosSemidef)
    (h12 : (L₂ - L₁).PosSemidef) :
    ∀ T, (dareIter C R A Qw L₂ T - dareIter C R A Qw L₁ T).PosSemidef
  | 0 => h12
  | T + 1 => dareStep_mono hR
      (dareIter_posSemidef hR hQw hL₁ T)
      (dareIter_posSemidef hR hQw hL₂ T)
      (dareIter_mono hR hQw hL₁ hL₂ h12 T)

end Dare
end Estimation
