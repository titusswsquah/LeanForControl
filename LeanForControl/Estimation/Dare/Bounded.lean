import LeanForControl.Estimation.Dare.GapEngine
import LeanForControl.LinearSystems.StagedFacts
import Architect

/-!
# Uniform boundedness of the covariance iterates (`eq:bounded`)

The paper's `lem:structure`-2 imports the MMSE optimality of the
Kalman filter (`fact:filter-opt`) to dominate `Σ_T` by a fixed-gain
observer. Here the domination is **algebraic**: the *predictor-form*
Joseph identity

`(A−LC)Σ(A−LC)ᵀ + LRLᵀ + Q_w − R(Σ) = (L−L*)S(Σ)(L−L*)ᵀ ⪰ 0`

holds for **every** gain `L` (completed square about
`L* = AΣCᵀS⁻¹`; note the update-form `joseph` of `Update.lean` only
reaches gains of the form `A·K`, while the predictor form reaches
all `L` — which is what `fact:detect-inj` supplies). Iterating
against the Lyapunov recursion of a fixed Schur `A−LC` and unrolling
gives the uniform quadratic-form bound.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

open scoped Matrix.Norms.Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ} {Sg : Matrix ι ι ℝ}

/-- `L∞` operator norm of a transpose, up to the dimension factor
(index-generic, rectangular version of
`LinearSystems.linfty_opNorm_transpose_le`). -/
lemma linfty_opNorm_transpose_le' {κ' : Type*} [Fintype κ']
    (M : Matrix ι κ' ℝ) :
    ‖Mᵀ‖ ≤ (Fintype.card ι : ℝ) * ‖M‖ := by
  have hnn : ‖Mᵀ‖₊ ≤ (Fintype.card ι : ℕ) • ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun j _ => ?_
    have h1 : ∀ i : ι, ‖Mᵀ j i‖₊ ≤ ‖M‖₊ := by
      intro i
      rw [Matrix.linfty_opNNNorm_def]
      calc ‖Mᵀ j i‖₊ = ‖M i j‖₊ := rfl
      _ ≤ ∑ j', ‖M i j'‖₊ :=
          Finset.single_le_sum (f := fun j' => ‖M i j'‖₊)
            (fun _ _ => zero_le _) (Finset.mem_univ j)
      _ ≤ Finset.univ.sup fun i' => ∑ j', ‖M i' j'‖₊ :=
          Finset.le_sup (f := fun i' => ∑ j', ‖M i' j'‖₊)
            (Finset.mem_univ i)
    calc ∑ i, ‖Mᵀ j i‖₊ ≤ ∑ _i : ι, ‖M‖₊ :=
          Finset.sum_le_sum fun i _ => h1 i
    _ = (Fintype.card ι : ℕ) • ‖M‖₊ := by
        rw [Finset.sum_const, Finset.card_univ]
  calc ‖Mᵀ‖ = ((‖Mᵀ‖₊ : ℝ)) := rfl
  _ ≤ (((Fintype.card ι : ℕ) • ‖M‖₊ : NNReal) : ℝ) := by exact_mod_cast hnn
  _ = (Fintype.card ι : ℝ) * ‖M‖ := by push_cast; ring

/-- Quadratic form of a finite sum of matrices. -/
lemma quadForm_sum {α : Type*} (s : Finset α) (M : α → Matrix ι ι ℝ)
    (x : ι → ℝ) :
    quadForm (∑ j ∈ s, M j) x = ∑ j ∈ s, quadForm (M j) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, quadForm_add_matrix, ih]

/-! ### The predictor-form Joseph domination -/

variable (C R) in
/-- The predictor-form fixed-gain covariance step
`(A−LC)Σ(A−LC)ᵀ + LRLᵀ + Q_w`. -/
noncomputable def pjoseph (A Qw : Matrix ι ι ℝ) (L : Matrix ι κ ℝ)
    (Sg : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (A - L * C) * Sg * (A - L * C)ᵀ + L * R * Lᵀ + Qw

variable (C R) in
/-- Expansion of the predictor-form Joseph step. -/
lemma pjoseph_eq (A Qw : Matrix ι ι ℝ) (L : Matrix ι κ ℝ)
    (Sg : Matrix ι ι ℝ) :
    pjoseph C R A Qw L Sg
      = A * Sg * Aᵀ - L * (C * Sg) * Aᵀ - A * (Sg * Cᵀ) * Lᵀ
        + L * innov C R Sg * Lᵀ + Qw := by
  unfold pjoseph innov
  simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- **The predictor-form completed square**: for every gain `L`,
`pjoseph L Σ − R(Σ) = (L − AΣCᵀS⁻¹)·S(Σ)·(L − AΣCᵀS⁻¹)ᵀ`. -/
lemma pjoseph_sub_dareStep {A Qw : Matrix ι ι ℝ} (hR : R.PosDef)
    (hSg : Sg.PosSemidef) (L : Matrix ι κ ℝ) :
    pjoseph C R A Qw L Sg - dareStep C R A Qw Sg
      = (L - A * kGain C R Sg) * innov C R Sg
          * (L - A * kGain C R Sg)ᵀ := by
  have hSKt : innov C R Sg * (kGain C R Sg)ᵀ = C * Sg :=
    innov_mul_kGainT hR hSg
  have hKS : kGain C R Sg * innov C R Sg = Sg * Cᵀ :=
    kGain_mul_innov hR hSg
  have hKSKt : kGain C R Sg * innov C R Sg * (kGain C R Sg)ᵀ
      = Sg * Cᵀ * (innov C R Sg)⁻¹ * (C * Sg) := by
    rw [hKS]
    unfold kGain
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, innov_inv_transpose hR hSg,
      hSg.1.transpose_eq_self]
    simp only [Matrix.mul_assoc]
  have hdstep : dareStep C R A Qw Sg
      = A * Sg * Aᵀ
        - A * (Sg * Cᵀ * (innov C R Sg)⁻¹ * (C * Sg)) * Aᵀ + Qw := by
    unfold dareStep updM
    rw [Matrix.mul_sub A _ _, Matrix.sub_mul]
  have hRHS : (L - A * kGain C R Sg) * innov C R Sg
        * (L - A * kGain C R Sg)ᵀ
      = L * innov C R Sg * Lᵀ - L * (C * Sg) * Aᵀ
        - A * (Sg * Cᵀ) * Lᵀ
        + A * (Sg * Cᵀ * (innov C R Sg)⁻¹ * (C * Sg)) * Aᵀ := by
    simp only [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.transpose_mul]
    have h1 : L * innov C R Sg * ((kGain C R Sg)ᵀ * Aᵀ)
        = L * (C * Sg) * Aᵀ := by
      rw [← Matrix.mul_assoc (L * innov C R Sg) _ Aᵀ,
        Matrix.mul_assoc L _ _, hSKt, ← Matrix.mul_assoc]
    have h2 : A * kGain C R Sg * innov C R Sg * Lᵀ
        = A * (Sg * Cᵀ) * Lᵀ := by
      rw [Matrix.mul_assoc A (kGain C R Sg) (innov C R Sg), hKS]
    have h3 : A * kGain C R Sg * innov C R Sg
          * ((kGain C R Sg)ᵀ * Aᵀ)
        = A * (Sg * Cᵀ * (innov C R Sg)⁻¹ * (C * Sg)) * Aᵀ := by
      rw [← Matrix.mul_assoc (A * kGain C R Sg * innov C R Sg)
          (kGain C R Sg)ᵀ Aᵀ,
        Matrix.mul_assoc A (kGain C R Sg) (innov C R Sg),
        Matrix.mul_assoc A (kGain C R Sg * innov C R Sg)
          (kGain C R Sg)ᵀ,
        hKSKt]
    rw [h1, h2, h3]
    abel
  rw [pjoseph_eq, hdstep, hRHS]
  abel

/-- **The domination**: `R(Σ) ⪯ pjoseph L Σ` for every gain. -/
lemma dareStep_le_pjoseph {A Qw : Matrix ι ι ℝ} (hR : R.PosDef)
    (hSg : Sg.PosSemidef) (L : Matrix ι κ ℝ) :
    (pjoseph C R A Qw L Sg - dareStep C R A Qw Sg).PosSemidef := by
  rw [pjoseph_sub_dareStep hR hSg L]
  have h := ((innov_posDef (C := C) hR hSg).posSemidef).mul_mul_conjTranspose_same
    (L - A * kGain C R Sg)
  rwa [show (L - A * kGain C R Sg)ᴴ = (L - A * kGain C R Sg)ᵀ from
    Matrix.conjTranspose_eq_transpose_of_trivial _] at h

/-! ### The Lyapunov comparison recursion -/

/-- The fixed-loop Lyapunov iterates `Π_{T+1} = FΠ_TFᵀ + W`. -/
noncomputable def lyapIter (F W L₀ : Matrix ι ι ℝ) : ℕ → Matrix ι ι ℝ
  | 0 => L₀
  | T + 1 => F * lyapIter F W L₀ T * Fᵀ + W

lemma lyapIter_unroll (F W L₀ : Matrix ι ι ℝ) :
    ∀ T, lyapIter F W L₀ T
      = F ^ T * L₀ * (F ^ T)ᵀ
        + ∑ j ∈ Finset.range T, F ^ j * W * (F ^ j)ᵀ
  | 0 => by simp [lyapIter]
  | T + 1 => by
    show F * lyapIter F W L₀ T * Fᵀ + W = _
    rw [lyapIter_unroll F W L₀ T]
    rw [Finset.sum_range_succ' (fun j => F ^ j * W * (F ^ j)ᵀ) T]
    simp only [pow_zero, Matrix.one_mul, Matrix.transpose_one,
      Matrix.mul_one]
    rw [Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul]
    have hpow : ∀ (X : Matrix ι ι ℝ) (j : ℕ),
        F * (F ^ j * X * (F ^ j)ᵀ) * Fᵀ
          = F ^ (j + 1) * X * (F ^ (j + 1))ᵀ := by
      intro X j
      rw [pow_succ' F j, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have h1 : F * (F ^ T * L₀ * (F ^ T)ᵀ) * Fᵀ
        = F ^ (T + 1) * L₀ * (F ^ (T + 1))ᵀ := hpow L₀ T
    have h2 : ∀ j ∈ Finset.range T,
        F * (F ^ j * W * (F ^ j)ᵀ) * Fᵀ
          = F ^ (j + 1) * W * (F ^ (j + 1))ᵀ :=
      fun j _ => hpow W j
    rw [h1, Finset.sum_congr rfl h2]
    abel

/-- The covariance iterates are dominated by the fixed-gain Lyapunov
iterates seeded at the same prior. -/
lemma dareIter_le_lyapIter {A Qw : Matrix ι ι ℝ} (hR : R.PosDef)
    (hQw : Qw.PosSemidef) {L₀ : Matrix ι ι ℝ} (hL₀ : L₀.PosSemidef)
    (L : Matrix ι κ ℝ) :
    ∀ T, (lyapIter (A - L * C) (L * R * Lᵀ + Qw) L₀ T
      - dareIter C R A Qw L₀ T).PosSemidef
  | 0 => by simpa [lyapIter] using Matrix.PosSemidef.zero
  | T + 1 => by
    have hSgT := dareIter_posSemidef (C := C) (A := A) (Qw := Qw)
      hR hQw hL₀ T
    have hIH := dareIter_le_lyapIter (A := A) (Qw := Qw) hR hQw hL₀ L T
    -- Π_{T+1} − Σ_{T+1} = [F(Π_T − Σ_T)Fᵀ] + [pjoseph L Σ_T − R(Σ_T)]
    have hsplit : lyapIter (A - L * C) (L * R * Lᵀ + Qw) L₀ (T + 1)
          - dareIter C R A Qw L₀ (T + 1)
        = (A - L * C)
            * (lyapIter (A - L * C) (L * R * Lᵀ + Qw) L₀ T
                - dareIter C R A Qw L₀ T)
            * (A - L * C)ᵀ
          + (pjoseph C R A Qw L (dareIter C R A Qw L₀ T)
              - dareStep C R A Qw (dareIter C R A Qw L₀ T)) := by
      show (A - L * C) * lyapIter (A - L * C) (L * R * Lᵀ + Qw) L₀ T
            * (A - L * C)ᵀ + (L * R * Lᵀ + Qw)
          - dareIter C R A Qw L₀ (T + 1) = _
      rw [dareIter_succ]
      unfold pjoseph
      rw [Matrix.mul_sub (A - L * C)
          (lyapIter (A - L * C) (L * R * Lᵀ + Qw) L₀ T)
          (dareIter C R A Qw L₀ T),
        Matrix.sub_mul
          ((A - L * C) * lyapIter (A - L * C) (L * R * Lᵀ + Qw) L₀ T)
          ((A - L * C) * dareIter C R A Qw L₀ T) (A - L * C)ᵀ]
      abel
    rw [hsplit]
    refine Matrix.PosSemidef.add ?_ (dareStep_le_pjoseph hR hSgT L)
    have h := hIH.mul_mul_conjTranspose_same (A - L * C)
    rwa [show (A - L * C)ᴴ = (A - L * C)ᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h

/-! ### `eq:bounded` -/

/-- **Uniform boundedness of the covariance iterates**
(`lem:structure`-2, `eq:bounded`): under a stabilizing output
injection — supplied by detectability via `fact:detect-inj` — the
iterates from any PSD seed are uniformly bounded in quadratic form. -/
theorem exists_dare_bound {A Qw : Matrix ι ι ℝ} (hR : R.PosDef)
    (hQw : Qw.PosSemidef) {L₀ : Matrix ι ι ℝ} (hL₀ : L₀.PosSemidef)
    (hdet : IsDetectable (complexify A) (complexify C)) :
    ∃ b : ℝ, 0 < b ∧ ∀ (T : ℕ) (x : ι → ℝ),
      quadForm (dareIter C R A Qw L₀ T) x ≤ b * ‖x‖ ^ 2 := by
  obtain ⟨L, hL⟩ := detect_inj A C hdet
  set F := A - L * C with hF
  set W := L * R * Lᵀ + Qw with hW
  obtain ⟨c, ρ, hc, hρ0, hρ1, hpow⟩ := hL.exists_pow_norm_le
  obtain ⟨cL, hcL, hbL⟩ := exists_quadForm_le L₀
  obtain ⟨cW, hcW, hbW⟩ := exists_quadForm_le W
  set d : ℝ := (Fintype.card ι : ℝ) + 1 with hd
  have hd0 : (0 : ℝ) < d := by positivity
  have hcard : (Fintype.card ι : ℝ) ≤ d := by simp [hd]
  -- each propagated term: quadForm (FʲXFʲᵀ) x ≤ cX (d c ρʲ)² ‖x‖²
  have hterm : ∀ (X : Matrix ι ι ℝ) (cX : ℝ), 0 < cX →
      (∀ y, quadForm X y ≤ cX * ‖y‖ ^ 2) →
      ∀ (j : ℕ) (x : ι → ℝ),
        quadForm (F ^ j * X * (F ^ j)ᵀ) x
          ≤ cX * (d * c * ρ ^ j) ^ 2 * ‖x‖ ^ 2 := by
    intro X cX hcX hbX j x
    have h1 : quadForm (F ^ j * X * (F ^ j)ᵀ) x
        = quadForm X ((F ^ j)ᵀ *ᵥ x) := by
      rw [quadForm_mulVec, Matrix.transpose_transpose]
    have h2 : ‖(F ^ j)ᵀ *ᵥ x‖ ≤ d * c * ρ ^ j * ‖x‖ := by
      calc ‖(F ^ j)ᵀ *ᵥ x‖ ≤ ‖(F ^ j)ᵀ‖ * ‖x‖ :=
            Matrix.linfty_opNorm_mulVec _ _
      _ ≤ ((Fintype.card ι : ℝ) * ‖F ^ j‖) * ‖x‖ := by
            have := linfty_opNorm_transpose_le' (F ^ j)
            exact mul_le_mul_of_nonneg_right this (norm_nonneg x)
      _ ≤ (d * (c * ρ ^ j)) * ‖x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
            exact mul_le_mul hcard (hpow j) (norm_nonneg _) hd0.le
      _ = d * c * ρ ^ j * ‖x‖ := by ring
    have h3 : (0 : ℝ) ≤ ‖(F ^ j)ᵀ *ᵥ x‖ := norm_nonneg _
    calc quadForm (F ^ j * X * (F ^ j)ᵀ) x
        = quadForm X ((F ^ j)ᵀ *ᵥ x) := h1
    _ ≤ cX * ‖(F ^ j)ᵀ *ᵥ x‖ ^ 2 := hbX _
    _ ≤ cX * (d * c * ρ ^ j * ‖x‖) ^ 2 := by
          refine mul_le_mul_of_nonneg_left ?_ hcX.le
          have h4 : (0 : ℝ) ≤ d * c * ρ ^ j * ‖x‖ := by positivity
          gcongr
    _ = cX * (d * c * ρ ^ j) ^ 2 * ‖x‖ ^ 2 := by ring
  -- geometric tail bound
  have hρsq : ρ ^ 2 < 1 := by nlinarith
  have hgeom : ∀ T, ∑ j ∈ Finset.range T, (ρ ^ 2) ^ j
      ≤ (1 - ρ ^ 2)⁻¹ := by
    intro T
    have h1 : ∑ j ∈ Finset.range T, (ρ ^ 2) ^ j
        = (1 - (ρ ^ 2) ^ T) / (1 - ρ ^ 2) := by
      rw [geom_sum_eq (ne_of_lt hρsq), ← neg_div_neg_eq]
      ring_nf
    rw [h1]
    have h2 : (0 : ℝ) < 1 - ρ ^ 2 := by linarith
    have h3 : (0 : ℝ) ≤ (ρ ^ 2) ^ T := by positivity
    rw [div_le_iff₀ h2, inv_mul_cancel₀ (ne_of_gt h2)]
    linarith
  -- assemble
  have hρinv : (0 : ℝ) ≤ (1 - ρ ^ 2)⁻¹ := by
    have : (0 : ℝ) < 1 - ρ ^ 2 := by linarith
    positivity
  refine ⟨cL * (d * c) ^ 2 + cW * (d * c) ^ 2 * (1 - ρ ^ 2)⁻¹ + 1,
    ?_, fun T x => ?_⟩
  · have h1 : (0 : ℝ) ≤ cL * (d * c) ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ cW * (d * c) ^ 2 * (1 - ρ ^ 2)⁻¹ :=
      mul_nonneg (by positivity) hρinv
    linarith
  -- Σ_T ⪯ Π_T
  have hdom := dareIter_le_lyapIter (C := C) (A := A) (Qw := Qw) hR hQw hL₀ L T
  have hq1 : quadForm (dareIter C R A Qw L₀ T) x
      ≤ quadForm (lyapIter F W L₀ T) x :=
    quadForm_le_quadForm_of_posSemidef_sub hdom x
  -- Π_T unrolled and bounded
  rw [lyapIter_unroll] at hq1
  rw [quadForm_add_matrix, quadForm_sum] at hq1
  have hseed : quadForm (F ^ T * L₀ * (F ^ T)ᵀ) x
      ≤ cL * (d * c) ^ 2 * ‖x‖ ^ 2 := by
    have h := hterm L₀ cL hcL hbL T x
    have hρT : ρ ^ T ≤ 1 := pow_le_one₀ hρ0.le hρ1.le
    have h5 : cL * (d * c * ρ ^ T) ^ 2 ≤ cL * (d * c) ^ 2 := by
      have h6 : (d * c * ρ ^ T) ^ 2 ≤ (d * c) ^ 2 := by
        have h7 : d * c * ρ ^ T ≤ d * c := by
          nlinarith [mul_pos hd0 hc]
        have h8 : (0 : ℝ) ≤ d * c * ρ ^ T := by positivity
        nlinarith
      exact mul_le_mul_of_nonneg_left h6 hcL.le
    calc quadForm (F ^ T * L₀ * (F ^ T)ᵀ) x
        ≤ cL * (d * c * ρ ^ T) ^ 2 * ‖x‖ ^ 2 := h
    _ ≤ cL * (d * c) ^ 2 * ‖x‖ ^ 2 := by
        have := sq_nonneg ‖x‖
        nlinarith
  have hsum : ∑ j ∈ Finset.range T,
        quadForm (F ^ j * W * (F ^ j)ᵀ) x
      ≤ cW * (d * c) ^ 2 * (1 - ρ ^ 2)⁻¹ * ‖x‖ ^ 2 := by
    have h1 : ∀ j ∈ Finset.range T,
        quadForm (F ^ j * W * (F ^ j)ᵀ) x
          ≤ cW * (d * c) ^ 2 * (ρ ^ 2) ^ j * ‖x‖ ^ 2 := by
      intro j _
      have h := hterm W cW hcW hbW j x
      calc quadForm (F ^ j * W * (F ^ j)ᵀ) x
          ≤ cW * (d * c * ρ ^ j) ^ 2 * ‖x‖ ^ 2 := h
      _ = cW * (d * c) ^ 2 * (ρ ^ 2) ^ j * ‖x‖ ^ 2 := by ring
    calc ∑ j ∈ Finset.range T, quadForm (F ^ j * W * (F ^ j)ᵀ) x
        ≤ ∑ j ∈ Finset.range T,
            cW * (d * c) ^ 2 * (ρ ^ 2) ^ j * ‖x‖ ^ 2 :=
          Finset.sum_le_sum h1
    _ = cW * (d * c) ^ 2 * ‖x‖ ^ 2
          * ∑ j ∈ Finset.range T, (ρ ^ 2) ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ cW * (d * c) ^ 2 * ‖x‖ ^ 2 * (1 - ρ ^ 2)⁻¹ := by
        refine mul_le_mul_of_nonneg_left (hgeom T) ?_
        positivity
    _ = cW * (d * c) ^ 2 * (1 - ρ ^ 2)⁻¹ * ‖x‖ ^ 2 := by ring
  have hx2 : (0 : ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
  calc quadForm (dareIter C R A Qw L₀ T) x
      ≤ quadForm (F ^ T * L₀ * (F ^ T)ᵀ) x
        + ∑ j ∈ Finset.range T, quadForm (F ^ j * W * (F ^ j)ᵀ) x :=
        hq1
  _ ≤ cL * (d * c) ^ 2 * ‖x‖ ^ 2
        + cW * (d * c) ^ 2 * (1 - ρ ^ 2)⁻¹ * ‖x‖ ^ 2 :=
        add_le_add hseed hsum
  _ ≤ (cL * (d * c) ^ 2 + cW * (d * c) ^ 2 * (1 - ρ ^ 2)⁻¹ + 1)
        * ‖x‖ ^ 2 := by nlinarith

end Dare
end Estimation