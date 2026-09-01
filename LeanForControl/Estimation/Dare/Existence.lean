import LeanForControl.Estimation.Dare.Sylvester
import Architect

/-!
# Existence and uniqueness of the strong solution (D4: `fact:dare-strong`)

The deck's foundational import, constructed by **chart assembly**:

* `P∞` — the reduced stabilizing solution (`Dare/Reduced.lean`);
* `Λ∞` — the loading, fixed point of the Sylvester recursion
  `Λ ↦ L∞·Λ·Aₐ⁻¹ + d∞` (both factors Schur, `Dare/Sylvester.lean`);
* `J∞` — the information gramian, fixed point of
  `J ↦ Aₐ⁻ᵀ(J + Ξ∞)Aₐ⁻¹`, PSD as a limit of PSD iterates and
  **positive definite by detectability** (`gramian_fixed_posDef`): a
  kernel direction is `Aₐ⁻¹`-invariant and `Ceff∞`-unobservable, so
  its eigenvector lifts through the loading identity to an
  undetectable `|λ| > 1` mode of `(A, C)` — dead by C1;
* `Σ∞ := e₁P∞e₁ᵀ + V∞·J∞⁻¹·V∞ᵀ` — a fixed point by
  `chart_dareStep` read backwards (`assembled_lam_fixed`,
  `assembled_Saa_fixed`), with `ρ(F∞) ≤ 1` by the one-step
  PBH–Stein kill at `|μ| > 1` (`fixed_specLe`: extinction and the
  positive antistable corner leave only marginal content, which
  cannot exceed the circle).

`exists_strong_solution` needs **C1 alone**. Uniqueness
(`strong_solution_unique`) follows from `lem:supremal` seeded at
`Σ∞ + Σ∞'`.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

/-- A complexified PD matrix has trivial kernel. -/
lemma complexify_posDef_mulVec_eq_zero {ι' : Type*} [Fintype ι']
    [DecidableEq ι'] {M : Matrix ι' ι' ℝ} (hM : M.PosDef)
    {u : ι' → ℂ} (h : complexify M *ᵥ u = 0) : u = 0 := by
  have hre : M *ᵥ (fun j => (u j).re) = 0 := by
    funext i
    have h0 : (complexify M *ᵥ u) i = 0 := by rw [h]; rfl
    have h1 := complexify_mulVec_re M u i
    rw [h0] at h1
    simpa using h1.symm
  have him : M *ᵥ (fun j => (u j).im) = 0 := by
    funext i
    have h0 : (complexify M *ᵥ u) i = 0 := by rw [h]; rfl
    have h1 := complexify_mulVec_im M u i
    rw [h0] at h1
    simpa using h1.symm
  have hzr : (fun j => (u j).re) = 0 := by
    refine eq_zero_of_quadForm_eq_zero_of_posDef hM ?_
    rw [quadForm, hre, dotProduct_zero]
  have hzi : (fun j => (u j).im) = 0 := by
    refine eq_zero_of_quadForm_eq_zero_of_posDef hM ?_
    rw [quadForm, him, dotProduct_zero]
  funext j
  refine Complex.ext ?_ ?_
  · exact congrFun hzr j
  · exact congrFun hzi j

namespace DareSystem

variable {n₁ na nm m p : ℕ} (S : DareSystem n₁ na nm m p)

/-! ### The gramian is positive definite (detectability-PBH) -/

set_option maxHeartbeats 1600000 in
/-- **The information gramian is positive definite** (the true content
of `lem:structure`-1's `eq:Sinf-gram`): a kernel direction of the
fixed gramian is `Aₐ⁻¹`-invariant and killed by the effective
observation, so its eigenvector lifts through the loading identity to
an undetectable antistable mode of `(A, C)` — contradicting C1. -/
lemma gramian_fixed_posDef (hC1 : S.C1)
    {Pinf : Matrix (Fin n₁) (Fin n₁) ℝ} (hP : Pinf.PosSemidef)
    {Lam : Matrix (Fin n₁) (Fin na) ℝ}
    (hΛ : Lam * S.Aa
      = errMap S.C₁ S.R S.A₁ Pinf * Lam
        + (S.A₁₂ * ea2 na nm
          - S.A₁ * kGain S.C₁ S.R Pinf * (S.fullC * embA n₁ na nm)))
    {J : Matrix (Fin na) (Fin na) ℝ} (hJpsd : J.PosSemidef)
    (hJfix : J = (S.Aa⁻¹)ᵀ
      * (J + (S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
          * S.ceff Lam 0) * S.Aa⁻¹) :
    J.PosDef := by
  classical
  have hSt : (innov S.C₁ S.R Pinf).PosDef := innov_posDef S.hR hP
  have hΞpsd : ((S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
      * S.ceff Lam 0).PosSemidef := by
    have h := hSt.inv.posSemidef.conjTranspose_mul_mul_same
      (S.ceff Lam 0)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  -- the real kernel implication: `Jx = 0 ⇒ J(Aₐ⁻¹x) = 0 ∧ Ceff(Aₐ⁻¹x) = 0`
  have hker : ∀ x : Fin na → ℝ, J *ᵥ x = 0 →
      (J * S.Aa⁻¹) *ᵥ x = 0
        ∧ (S.ceff Lam 0 * S.Aa⁻¹) *ᵥ x = 0 := by
    intro x hx
    have h0 : quadForm J x = 0 := by
      rw [quadForm, hx, dotProduct_zero]
    have h1 : quadForm (J + (S.ceff Lam 0)ᵀ
        * (innov S.C₁ S.R Pinf)⁻¹ * S.ceff Lam 0)
        (S.Aa⁻¹ *ᵥ x) = 0 := by
      have h2 := quadForm_mulVec (J + (S.ceff Lam 0)ᵀ
        * (innov S.C₁ S.R Pinf)⁻¹ * S.ceff Lam 0) (S.Aa⁻¹) x
      rw [h2, ← hJfix] at *
      exact h0
    rw [quadForm_add_matrix] at h1
    have hq1 := hJpsd.quadForm_nonneg (S.Aa⁻¹ *ᵥ x)
    have hq2 := hΞpsd.quadForm_nonneg (S.Aa⁻¹ *ᵥ x)
    have hJz : quadForm J (S.Aa⁻¹ *ᵥ x) = 0 := by linarith
    have hΞz : quadForm ((S.ceff Lam 0)ᵀ
        * (innov S.C₁ S.R Pinf)⁻¹ * S.ceff Lam 0)
        (S.Aa⁻¹ *ᵥ x) = 0 := by linarith
    constructor
    · rw [← Matrix.mulVec_mulVec]
      exact hJpsd.mulVec_eq_zero_of_quadForm_eq_zero hJz
    · rw [← Matrix.mulVec_mulVec]
      have h3 : quadForm (innov S.C₁ S.R Pinf)⁻¹
          (S.ceff Lam 0 *ᵥ (S.Aa⁻¹ *ᵥ x)) = 0 := by
        have h4 := quadForm_mulVec (innov S.C₁ S.R Pinf)⁻¹
          (S.ceff Lam 0) (S.Aa⁻¹ *ᵥ x)
        rw [h4]
        exact hΞz
      exact eq_zero_of_quadForm_eq_zero_of_posDef hSt.inv h3
  -- positivity, or a kernel eigenvector lifts to an undetectable mode
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hJpsd.1 fun v hvne => ?_
  rcases lt_or_eq_of_le (hJpsd.quadForm_nonneg v) with hq | hq
  · exact hq
  exfalso
  have hvker : J *ᵥ v = 0 :=
    hJpsd.mulVec_eq_zero_of_quadForm_eq_zero hq.symm
  -- complexified kernel, `Aₐ⁻¹`-invariant
  set Kc : Submodule ℂ (Fin na → ℂ) :=
    LinearMap.ker (Matrix.mulVecLin (complexify J)) with hKc
  have hvKc : complexifyVec v ∈ Kc := by
    rw [hKc, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      complexify_mulVec, hvker, complexifyVec_zero]
  have hKcne : Kc ≠ ⊥ :=
    (Submodule.ne_bot_iff Kc).mpr ⟨complexifyVec v, hvKc,
      fun h0 => hvne (complexifyVec_eq_zero_iff.mp h0)⟩
  have hinv : ∀ u ∈ Kc,
      Matrix.mulVecLin (complexify (S.Aa⁻¹)) u ∈ Kc := by
    intro u hu
    rw [hKc, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hu ⊢
    have h := complexify_mulVec_eq_on_ker
      (M₁ := J * S.Aa⁻¹) (M₂ := 0) (N := J)
      (fun x hx => by rw [(hker x hx).1, Matrix.zero_mulVec]) hu
    rw [complexify_zero, Matrix.zero_mulVec, complexify_mul,
      ← Matrix.mulVec_mulVec] at h
    exact h
  have hne : Nontrivial Kc := Submodule.nontrivial_iff_ne_bot.mpr hKcne
  obtain ⟨ν, hν⟩ := Module.End.exists_eigenvalue
    ((Matrix.mulVecLin (complexify (S.Aa⁻¹))).restrict hinv)
  obtain ⟨⟨u, huK⟩, huvec⟩ := hν.exists_hasEigenvector
  have hune : u ≠ 0 := by
    intro h0
    exact huvec.2 (by simp [h0])
  have heig : complexify (S.Aa⁻¹) *ᵥ u = ν • u := by
    have h1 := huvec.apply_eq_smul
    have h2 := congrArg Subtype.val h1
    rw [LinearMap.restrict_apply] at h2
    simpa [Matrix.mulVecLin_apply] using h2
  have huKc : complexify J *ᵥ u = 0 := by
    have h := huK
    rwa [hKc, LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
  -- `ν ≠ 0` and the lifted eigenvalue of `Aₐ`
  have hν0 : ν ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at heig
    apply hune
    calc u = complexify S.Aa *ᵥ (complexify (S.Aa⁻¹) *ᵥ u) := by
          rw [Matrix.mulVec_mulVec, ← complexify_mul,
            Matrix.mul_nonsing_inv _ S.isUnit_Aa_det, complexify_one,
            Matrix.one_mulVec]
    _ = 0 := by rw [heig, Matrix.mulVec_zero]
  have heigAa : complexify S.Aa *ᵥ u = ν⁻¹ • u := by
    have h1 : u = ν • (complexify S.Aa *ᵥ u) := by
      calc u = complexify S.Aa *ᵥ (complexify (S.Aa⁻¹) *ᵥ u) := by
            rw [Matrix.mulVec_mulVec, ← complexify_mul,
              Matrix.mul_nonsing_inv _ S.isUnit_Aa_det, complexify_one,
              Matrix.one_mulVec]
      _ = ν • (complexify S.Aa *ᵥ u) := by
            rw [heig, Matrix.mulVec_smul]
    have h2 := congrArg (fun z => ν⁻¹ • z) h1
    simpa [smul_smul, inv_mul_cancel₀ hν0] using h2.symm
  have hlspec : ν⁻¹ ∈ spectrum ℂ (complexify S.Aa) :=
    mem_spectrum_of_mulVec_eq_smul hune heigAa
  have hlgt : 1 < ‖ν⁻¹‖ := S.hAnti _ hlspec
  -- the effective observation kills `u`
  have hceffu : complexify (S.ceff Lam 0) *ᵥ u = 0 := by
    have h1 := complexify_mulVec_eq_on_ker
      (M₁ := S.ceff Lam 0 * S.Aa⁻¹) (M₂ := 0) (N := J)
      (fun x hx => by rw [(hker x hx).2, Matrix.zero_mulVec]) huKc
    rw [complexify_zero, Matrix.zero_mulVec, complexify_mul,
      ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul] at h1
    have h2 := congrArg (fun z => ν⁻¹ • z) h1
    simpa [smul_smul, inv_mul_cancel₀ hν0] using h2
  -- the lifted undetectable mode
  have hkey : S.A₁ * Lam + S.A₁₂ * ea2 na nm + S.A₁₂ * em2 na nm * (0 : Matrix (Fin nm) (Fin na) ℝ)
      = Lam * S.Aa + S.A₁ * kGain S.C₁ S.R Pinf * S.ceff Lam 0 := by
    rw [hΛ]
    unfold errMap ceff
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, Matrix.mul_assoc]
    abel
  have hArel : S.fullA * condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)
      = condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ) * S.Aa
        + emb1 n₁ na nm * (S.A₁ * kGain S.C₁ S.R Pinf)
          * S.ceff Lam 0 := by
    rw [S.fullA_mul_condV, hkey]
    unfold condV
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, Matrix.mul_assoc]
    abel
  have hxA : complexify S.fullA *ᵥ (complexify (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)) *ᵥ u)
      = ν⁻¹ • (complexify (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)) *ᵥ u) := by
    calc complexify S.fullA *ᵥ (complexify (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)) *ᵥ u)
        = complexify (S.fullA * condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)) *ᵥ u := by
          rw [complexify_mul, ← Matrix.mulVec_mulVec]
    _ = complexify (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)) *ᵥ (complexify S.Aa *ᵥ u)
          + complexify (emb1 n₁ na nm
              * (S.A₁ * kGain S.C₁ S.R Pinf))
            *ᵥ (complexify (S.ceff Lam 0) *ᵥ u) := by
          rw [hArel, complexify_add, Matrix.add_mulVec,
            complexify_mul, ← Matrix.mulVec_mulVec, complexify_mul,
            ← Matrix.mulVec_mulVec]
    _ = ν⁻¹ • (complexify (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)) *ᵥ u) := by
          rw [heigAa, hceffu, Matrix.mulVec_zero, add_zero,
            Matrix.mulVec_smul]
  have hxC : complexify S.fullC
      *ᵥ (complexify (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)) *ᵥ u) = 0 := by
    rw [Matrix.mulVec_mulVec, ← complexify_mul, S.fullC_mul_condV,
      hceffu]
  have hxne : complexify (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)) *ᵥ u ≠ 0 := by
    intro h0
    apply hune
    have h1 : complexify ((embA n₁ na nm)ᵀ)
        *ᵥ (complexify (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)) *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, ← complexify_mul, embAt_mul_condV,
        complexify_one, Matrix.one_mulVec]
    rw [h0, Matrix.mulVec_zero] at h1
    exact h1.symm
  have h0 := hC1 (ν⁻¹) _ (le_of_lt hlgt) hxA hxC
  exact hxne h0

/-! ### The assembled fixed point -/

/-- The loading fixed point makes `lamNext` fixed. -/
lemma assembled_lam_fixed
    {Pinf : Matrix (Fin n₁) (Fin n₁) ℝ}
    {Lam : Matrix (Fin n₁) (Fin na) ℝ}
    (hΛ : Lam * S.Aa
      = errMap S.C₁ S.R S.A₁ Pinf * Lam
        + (S.A₁₂ * ea2 na nm
          - S.A₁ * kGain S.C₁ S.R Pinf * (S.fullC * embA n₁ na nm))) :
    S.lamNext Pinf Lam 0 = Lam := by
  unfold lamNext lamHat
  have hkey : S.A₁ * (Lam - Pinf * S.C₁ᵀ
        * (innov S.C₁ S.R Pinf)⁻¹ * S.ceff Lam 0)
      + S.A₁₂ * ea2 na nm
      + S.A₁₂ * em2 na nm * (0 : Matrix (Fin nm) (Fin na) ℝ)
      = Lam * S.Aa := by
    rw [hΛ]
    unfold errMap kGain ceff
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, Matrix.mul_assoc]
    abel
  rw [hkey, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ S.isUnit_Aa_det, Matrix.mul_one]

/-- The gramian fixed point makes the antistable block fixed. -/
lemma assembled_Saa_fixed
    {Pinf : Matrix (Fin n₁) (Fin n₁) ℝ} (hP : Pinf.PosSemidef)
    {Lam : Matrix (Fin n₁) (Fin na) ℝ}
    {J : Matrix (Fin na) (Fin na) ℝ} (hJPD : J.PosDef)
    (hJfix : J = (S.Aa⁻¹)ᵀ
      * (J + (S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
          * S.ceff Lam 0) * S.Aa⁻¹) :
    S.Aa * S.uhatOf Pinf Lam 0 J⁻¹ * S.Aaᵀ = J⁻¹ := by
  have hSt : (innov S.C₁ S.R Pinf).PosDef := innov_posDef S.hR hP
  have hJdet : IsUnit J.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hJPD.isUnit
  have hJinvPD : (J⁻¹).PosDef := hJPD.inv
  have hΞpsd : ((S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
      * S.ceff Lam 0).PosSemidef := by
    have h := hSt.inv.posSemidef.conjTranspose_mul_mul_same
      (S.ceff Lam 0)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hJΞPD : (J + (S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
      * S.ceff Lam 0).PosDef := hJPD.add_posSemidef hΞpsd
  have hJΞdet : IsUnit (J + (S.ceff Lam 0)ᵀ
      * (innov S.C₁ S.R Pinf)⁻¹ * S.ceff Lam 0).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hJΞPD.isUnit
  -- `Û⁻¹ = J + Ξ`
  have hUdef := uhat_inv_eq
    (Sfull := S.sfullOf Pinf Lam 0 J⁻¹)
    (Stil := innov S.C₁ S.R Pinf) (Ceff := S.ceff Lam 0)
    (Saa := J⁻¹) rfl
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (S.sfullOf_posDef hP Lam 0 hJinvPD.posSemidef).isUnit)
    ((Matrix.isUnit_iff_isUnit_det _).mp hSt.isUnit)
    ((Matrix.isUnit_iff_isUnit_det _).mp hJinvPD.isUnit)
  have hUinv : (S.uhatOf Pinf Lam 0 J⁻¹)⁻¹
      = J + (S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
          * S.ceff Lam 0 := by
    unfold uhatOf
    rw [hUdef, Matrix.nonsing_inv_nonsing_inv _ hJdet]
  have hUPD : (S.uhatOf Pinf Lam 0 J⁻¹).PosDef :=
    S.uhatOf_posDef hP Lam 0 hJinvPD
  have hUdet : IsUnit (S.uhatOf Pinf Lam 0 J⁻¹).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hUPD.isUnit
  have hUeq : S.uhatOf Pinf Lam 0 J⁻¹
      = (J + (S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
          * S.ceff Lam 0)⁻¹ := by
    rw [← hUinv, Matrix.nonsing_inv_nonsing_inv _ hUdet]
  rw [hUeq]
  -- the sandwich inverts to the fixed equation
  have hsand : (S.Aa * (J + (S.ceff Lam 0)ᵀ
      * (innov S.C₁ S.R Pinf)⁻¹ * S.ceff Lam 0)⁻¹ * S.Aaᵀ)⁻¹
      = J := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hJΞdet]
    conv_rhs => rw [hJfix]
    rw [← Matrix.transpose_nonsing_inv]
    simp only [Matrix.mul_assoc]
  have hdetAa := S.isUnit_Aa_det
  have hsanddet : IsUnit (S.Aa * (J + (S.ceff Lam 0)ᵀ
      * (innov S.C₁ S.R Pinf)⁻¹ * S.ceff Lam 0)⁻¹ * S.Aaᵀ).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_nonsing_inv]
    rw [Ring.inverse_eq_inv]
    exact (hdetAa.mul hJΞdet.inv).mul hdetAa
  calc S.Aa * (J + (S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
        * S.ceff Lam 0)⁻¹ * S.Aaᵀ
      = ((S.Aa * (J + (S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
          * S.ceff Lam 0)⁻¹ * S.Aaᵀ)⁻¹)⁻¹ := by
        rw [Matrix.nonsing_inv_nonsing_inv _ hsanddet]
  _ = J⁻¹ := by rw [hsand]


/-! ### `ρ(F∞) ≤ 1` for the assembled fixed point -/

set_option maxHeartbeats 1600000 in
/-- **`specLe` from structure**: a PSD fixed point with marginal
extinction and positive antistable corner has `ρ(F) ≤ 1` — the
one-step PBH–Stein kill at `|μ| > 1`: the strict over-balance forces
both the noise inputs and the `Σ`-energy of a left eigenvector to
vanish, so it is a left eigenvector of `A` unexcited by `G` **and**
in `ker Σ`; stabilizability kills `e₁`, the positive corner kills
`a`, and the marginal spectrum cannot exceed the circle. -/
lemma fixed_specLe {Sinf : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hpsd : Sinf.PosSemidef)
    (hfix : dareStep S.fullC S.R S.fullA S.Qw Sinf = Sinf)
    (hext : Sinf * embM n₁ na nm = 0)
    (hcorner : ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm).PosDef) :
    ∀ μ ∈ spectrum ℂ (complexify (errMap S.fullC S.R S.fullA Sinf)),
      ‖μ‖ ≤ 1 := by
  intro μ hμ
  by_contra hlt
  rw [not_le] at hlt
  have hμt : μ ∈ spectrum ℂ
      (complexify ((errMap S.fullC S.R S.fullA Sinf)ᵀ)) := by
    rw [complexify_transpose]
    exact mem_spectrum_transpose_iff.mpr hμ
  obtain ⟨e, hene, heeq⟩ := exists_eigenvector_of_mem_spectrum hμt
  obtain ⟨er, herdef⟩ : ∃ er, er = fun i => (e i).re := ⟨_, rfl⟩
  obtain ⟨ei, heidef⟩ : ∃ ei, ei = fun i => (e i).im := ⟨_, rfl⟩
  have hre1 : (errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ er
      = μ.re • er - μ.im • ei := by
    rw [herdef, heidef]
    funext i
    have h1 := complexify_mulVec_re
      ((errMap S.fullC S.R S.fullA Sinf)ᵀ) e i
    rw [heeq] at h1
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h1]
  have him1 : (errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ ei
      = μ.im • er + μ.re • ei := by
    rw [herdef, heidef]
    funext i
    have h1 := complexify_mulVec_im
      ((errMap S.fullC S.R S.fullA Sinf)ᵀ) e i
    rw [heeq] at h1
    simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← h1]
    ring
  have hsym : Sinf.IsHermitian := hpsd.1
  -- dissipation from the predictor-Joseph fixed point
  have hdiss : ∀ x : ix n₁ na nm → ℝ,
      quadForm Sinf ((errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ x)
        = quadForm Sinf x
          - quadForm S.R
              ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ x)
          - quadForm S.Q (S.fullGᵀ *ᵥ x) := by
    intro x
    have hF := quadForm_mulVec Sinf
      ((errMap S.fullC S.R S.fullA Sinf)ᵀ) x
    rw [Matrix.transpose_transpose] at hF
    have hK := quadForm_mulVec S.R
      ((S.fullA * kGain S.fullC S.R Sinf)ᵀ) x
    rw [Matrix.transpose_transpose] at hK
    have hG := quadForm_mulVec S.Q (S.fullGᵀ) x
    rw [Matrix.transpose_transpose] at hG
    have h1 : quadForm Sinf x
        = quadForm Sinf ((errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ x)
          + quadForm S.R
              ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ x)
          + quadForm S.Q (S.fullGᵀ *ᵥ x) := by
      conv_lhs => rw [fixed_predictor_stein S.hR hpsd hfix]
      rw [quadForm_add_matrix, quadForm_add_matrix, hF, hK]
      congr 1
      rw [hG]
      rfl
    linarith
  -- rotation identity (exact)
  have hrot : quadForm Sinf
        ((errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ er)
      + quadForm Sinf ((errMap S.fullC S.R S.fullA Sinf)ᵀ *ᵥ ei)
      = (μ.re ^ 2 + μ.im ^ 2)
        * (quadForm Sinf er + quadForm Sinf ei) := by
    rw [hre1, him1]
    have hsub : μ.re • er - μ.im • ei
        = μ.re • er + (-μ.im) • ei := by
      module
    rw [hsub, quadForm_add_of_isHermitian hsym,
      quadForm_add_of_isHermitian hsym, quadForm_smul,
      quadForm_smul, quadForm_smul, quadForm_smul,
      Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul,
      dotProduct_smul, smul_dotProduct, smul_dotProduct,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  -- strict over-balance: `Σ`-energy and noise inputs both vanish
  have hn : 1 < μ.re ^ 2 + μ.im ^ 2 := by
    have h1 : Complex.normSq μ = μ.re * μ.re + μ.im * μ.im :=
      Complex.normSq_apply μ
    have h2 : Complex.normSq μ = ‖μ‖ ^ 2 := by
      rw [Complex.sq_norm]
    nlinarith [hlt]
  have h1 := hdiss er
  have h2 := hdiss ei
  have hqe1 := hpsd.quadForm_nonneg er
  have hqe2 := hpsd.quadForm_nonneg ei
  have hr1 := S.hR.posSemidef.quadForm_nonneg
    ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ er)
  have hr2 := S.hR.posSemidef.quadForm_nonneg
    ((S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ ei)
  have hg1 := S.hQ.posSemidef.quadForm_nonneg (S.fullGᵀ *ᵥ er)
  have hg2 := S.hQ.posSemidef.quadForm_nonneg (S.fullGᵀ *ᵥ ei)
  have hqer0 : quadForm Sinf er = 0 := by nlinarith
  have hqei0 : quadForm Sinf ei = 0 := by nlinarith
  have hKr : (S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ er = 0 :=
    eq_zero_of_quadForm_eq_zero_of_posDef S.hR (by nlinarith)
  have hKi : (S.fullA * kGain S.fullC S.R Sinf)ᵀ *ᵥ ei = 0 :=
    eq_zero_of_quadForm_eq_zero_of_posDef S.hR (by nlinarith)
  have hGr : S.fullGᵀ *ᵥ er = 0 :=
    eq_zero_of_quadForm_eq_zero_of_posDef S.hQ (by nlinarith)
  have hGi : S.fullGᵀ *ᵥ ei = 0 :=
    eq_zero_of_quadForm_eq_zero_of_posDef S.hQ (by nlinarith)
  -- recombine over ℂ
  have hkerc : complexify Sinf *ᵥ e = 0 := by
    refine complexify_mulVec_eq_zero _ _ ?_ ?_
    · rw [← herdef]
      exact hpsd.mulVec_eq_zero_of_quadForm_eq_zero hqer0
    · rw [← heidef]
      exact hpsd.mulVec_eq_zero_of_quadForm_eq_zero hqei0
  have hKc : complexify ((S.fullA * kGain S.fullC S.R Sinf)ᵀ)
      *ᵥ e = 0 := by
    refine complexify_mulVec_eq_zero _ _ ?_ ?_
    · rw [← herdef]; exact hKr
    · rw [← heidef]; exact hKi
  have hGc : complexify (S.fullGᵀ) *ᵥ e = 0 := by
    refine complexify_mulVec_eq_zero _ _ ?_ ?_
    · rw [← herdef]; exact hGr
    · rw [← heidef]; exact hGi
  have hAt : complexify (S.fullAᵀ) *ᵥ e = μ • e := by
    have h3 : complexify ((errMap S.fullC S.R S.fullA Sinf)ᵀ) *ᵥ e
        = complexify (S.fullAᵀ) *ᵥ e
          - complexify (S.fullCᵀ)
            *ᵥ (complexify
              ((S.fullA * kGain S.fullC S.R Sinf)ᵀ) *ᵥ e) := by
      rw [S.errMap_transpose_eq, complexify_sub, Matrix.sub_mulVec,
        complexify_mul, ← Matrix.mulVec_mulVec]
    rw [hKc, Matrix.mulVec_zero, sub_zero] at h3
    rw [← h3, heeq]
  -- the `e₁` part dies by stabilizability
  have hv1 : complexify (S.A₁ᵀ)
      *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e)
      = μ • (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e) := by
    have h3 : (emb1 n₁ na nm)ᵀ * S.fullAᵀ
        = S.A₁ᵀ * (emb1 n₁ na nm)ᵀ := by
      have h := congrArg Matrix.transpose S.fullA_mul_emb1
      rwa [Matrix.transpose_mul, Matrix.transpose_mul] at h
    calc complexify (S.A₁ᵀ)
        *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e)
        = complexify ((emb1 n₁ na nm)ᵀ)
            *ᵥ (complexify (S.fullAᵀ) *ᵥ e) := by
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            ← complexify_mul, ← complexify_mul, h3]
    _ = μ • (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e) := by
          rw [hAt, Matrix.mulVec_smul]
  have hG1 : complexify (S.G₁ᵀ)
      *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e) = 0 := by
    have h3 : S.fullGᵀ = S.G₁ᵀ * (emb1 n₁ na nm)ᵀ := by
      have h := congrArg Matrix.transpose S.fullG_eq
      rwa [Matrix.transpose_mul] at h
    rw [Matrix.mulVec_mulVec, ← complexify_mul, ← h3]
    exact hGc
  have hv10 : complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e = 0 :=
    S.hStab μ _ (le_of_lt hlt) hv1 hG1
  -- the `a` part dies by the positive corner
  have hedec : e
      = complexify (emb1 n₁ na nm)
          *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e)
        + complexify (embA n₁ na nm)
          *ᵥ (complexify ((embA n₁ na nm)ᵀ) *ᵥ e)
        + complexify (embM n₁ na nm)
          *ᵥ (complexify ((embM n₁ na nm)ᵀ) *ᵥ e) := by
    calc e = complexify
          (1 : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ) *ᵥ e := by
          rw [complexify_one, Matrix.one_mulVec]
    _ = complexify (emb1 n₁ na nm * (emb1 n₁ na nm)ᵀ
          + embA n₁ na nm * (embA n₁ na nm)ᵀ
          + embM n₁ na nm * (embM n₁ na nm)ᵀ) *ᵥ e := by
          rw [partition3]
    _ = _ := by
          rw [complexify_add, complexify_add, Matrix.add_mulVec,
            Matrix.add_mulVec, complexify_mul, complexify_mul,
            complexify_mul, ← Matrix.mulVec_mulVec,
            ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hea0 : complexify ((embA n₁ na nm)ᵀ) *ᵥ e = 0 := by
    have hcornerkill : complexify ((embA n₁ na nm)ᵀ * Sinf)
        *ᵥ e = 0 := by
      rw [complexify_mul, ← Matrix.mulVec_mulVec, hkerc,
        Matrix.mulVec_zero]
    have hAM : (embA n₁ na nm)ᵀ * Sinf * embM n₁ na nm = 0 := by
      rw [Matrix.mul_assoc, hext, Matrix.mul_zero]
    have hmat : (embA n₁ na nm)ᵀ * Sinf
        = ((embA n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm)
            * (emb1 n₁ na nm)ᵀ
          + ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
            * (embA n₁ na nm)ᵀ := by
      calc (embA n₁ na nm)ᵀ * Sinf
          = (embA n₁ na nm)ᵀ * Sinf * 1 := (Matrix.mul_one _).symm
      _ = (embA n₁ na nm)ᵀ * Sinf
            * (emb1 n₁ na nm * (emb1 n₁ na nm)ᵀ
              + embA n₁ na nm * (embA n₁ na nm)ᵀ
              + embM n₁ na nm * (embM n₁ na nm)ᵀ) := by
            rw [partition3]
      _ = _ := by
            rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc,
              ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAM,
              Matrix.zero_mul, add_zero]
    have h6 : complexify ((embA n₁ na nm)ᵀ * Sinf) *ᵥ e
        = complexify ((embA n₁ na nm)ᵀ * Sinf * emb1 n₁ na nm)
            *ᵥ (complexify ((emb1 n₁ na nm)ᵀ) *ᵥ e)
          + complexify ((embA n₁ na nm)ᵀ * Sinf * embA n₁ na nm)
            *ᵥ (complexify ((embA n₁ na nm)ᵀ) *ᵥ e) := by
      conv_lhs => rw [hmat]
      simp only [complexify_add, complexify_mul, Matrix.add_mulVec,
        ← Matrix.mulVec_mulVec]
    rw [hcornerkill, hv10, Matrix.mulVec_zero, zero_add] at h6
    exact complexify_posDef_mulVec_eq_zero hcorner h6.symm
  -- only marginal content remains: it cannot exceed the circle
  have hem : e = complexify (embM n₁ na nm)
      *ᵥ (complexify ((embM n₁ na nm)ᵀ) *ᵥ e) := by
    conv_lhs => rw [hedec]
    rw [hv10, hea0, Matrix.mulVec_zero, Matrix.mulVec_zero,
      zero_add, zero_add]
  have hemne : complexify ((embM n₁ na nm)ᵀ) *ᵥ e ≠ 0 := by
    intro h0
    apply hene
    rw [hem, h0, Matrix.mulVec_zero]
  have hmeig : complexify (S.Amᵀ)
      *ᵥ (complexify ((embM n₁ na nm)ᵀ) *ᵥ e)
      = μ • (complexify ((embM n₁ na nm)ᵀ) *ᵥ e) := by
    have h3 : complexify (S.fullAᵀ)
        *ᵥ (complexify (embM n₁ na nm)
          *ᵥ (complexify ((embM n₁ na nm)ᵀ) *ᵥ e))
        = complexify (embM n₁ na nm)
          *ᵥ (complexify (S.Amᵀ)
            *ᵥ (complexify ((embM n₁ na nm)ᵀ) *ᵥ e)) := by
      rw [Matrix.mulVec_mulVec _ (complexify (S.fullAᵀ))
        (complexify (embM n₁ na nm)), ← complexify_mul,
        S.fullA_transpose_mul_embM, complexify_mul,
        ← Matrix.mulVec_mulVec]
    have h4 : μ • e = complexify (embM n₁ na nm)
        *ᵥ (complexify (S.Amᵀ)
          *ᵥ (complexify ((embM n₁ na nm)ᵀ) *ᵥ e)) := by
      rw [← hAt]
      conv_lhs => rw [hem]
      exact h3
    have h5 := congrArg
      (fun z => complexify ((embM n₁ na nm)ᵀ) *ᵥ z) h4
    dsimp only at h5
    rw [Matrix.mulVec_smul,
      Matrix.mulVec_mulVec _ (complexify ((embM n₁ na nm)ᵀ))
        (complexify (embM n₁ na nm)), ← complexify_mul,
      embMt_mul_embM, complexify_one, Matrix.one_mulVec] at h5
    exact h5.symm
  have hμm : μ ∈ spectrum ℂ (complexify S.Am) := by
    refine mem_spectrum_transpose_iff.mp ?_
    rw [← complexify_transpose]
    exact mem_spectrum_of_mulVec_eq_smul hemne hmeig
  have h5 := S.hMarg μ hμm
  rw [h5] at hlt
  exact lt_irrefl 1 hlt

/-! ### Existence and uniqueness -/

set_option maxHeartbeats 1600000 in
/-- **`fact:dare-strong`, existence** (D4): under C1 alone, the DARE
has a strong solution — assembled on the conditional chart from the
reduced stabilizing solution, the loading Sylvester fixed point, and
the inverse information gramian. -/
theorem exists_strong_solution (hC1 : S.C1) :
    ∃ Sinf, S.IsStrongSolution Sinf := by
  classical
  obtain ⟨Pinf, hPpsd, hPfix, hPschur, _⟩ :=
    exists_stabilizing_solution S.hR S.hQ
      (S.reduced_detectable hC1) S.hStab
  have hAaInv : IsSchurStable S.Aa⁻¹ := S.Aa_inv_isSchurStable
  obtain ⟨Lam, hLamfix, _⟩ := sylvester_exists
    (errMap S.C₁ S.R S.A₁ Pinf) (S.Aa⁻¹)
    ((S.A₁₂ * ea2 na nm
      - S.A₁ * kGain S.C₁ S.R Pinf * (S.fullC * embA n₁ na nm))
      * S.Aa⁻¹) hPschur hAaInv
  have hΛ : Lam * S.Aa
      = errMap S.C₁ S.R S.A₁ Pinf * Lam
        + (S.A₁₂ * ea2 na nm
          - S.A₁ * kGain S.C₁ S.R Pinf
            * (S.fullC * embA n₁ na nm)) := by
    conv_lhs => rw [hLamfix]
    rw [Matrix.add_mul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ S.isUnit_Aa_det]
    simp only [Matrix.mul_one]
  -- the gramian
  have hSt : (innov S.C₁ S.R Pinf).PosDef := innov_posDef S.hR hPpsd
  have hΞpsd : ((S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
      * S.ceff Lam 0).PosSemidef := by
    have h := hSt.inv.posSemidef.conjTranspose_mul_mul_same
      (S.ceff Lam 0)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hAaInvT : IsSchurStable ((S.Aa⁻¹)ᵀ) := hAaInv.transpose
  obtain ⟨J, hJfix0, hJiter⟩ := sylvester_exists
    ((S.Aa⁻¹)ᵀ) (S.Aa⁻¹)
    ((S.Aa⁻¹)ᵀ * ((S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
      * S.ceff Lam 0) * S.Aa⁻¹) hAaInvT hAaInv
  have hdpsd : ((S.Aa⁻¹)ᵀ * ((S.ceff Lam 0)ᵀ
      * (innov S.C₁ S.R Pinf)⁻¹ * S.ceff Lam 0)
      * S.Aa⁻¹).PosSemidef := by
    have h := hΞpsd.conjTranspose_mul_mul_same (S.Aa⁻¹)
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hJpsd : J.PosSemidef := by
    refine posSemidef_of_tendsto (M := fun N => sylvIter
      ((S.Aa⁻¹)ᵀ) (S.Aa⁻¹)
      ((S.Aa⁻¹)ᵀ * ((S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
        * S.ceff Lam 0) * S.Aa⁻¹) N) ?_ hJiter
    intro n
    induction n with
    | zero => exact Matrix.PosSemidef.zero
    | succ n ih =>
      show ((S.Aa⁻¹)ᵀ * sylvIter _ _ _ n * S.Aa⁻¹ + _).PosSemidef
      refine Matrix.PosSemidef.add ?_ hdpsd
      have h := ih.conjTranspose_mul_mul_same (S.Aa⁻¹)
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hJfix : J = (S.Aa⁻¹)ᵀ
      * (J + (S.ceff Lam 0)ᵀ * (innov S.C₁ S.R Pinf)⁻¹
          * S.ceff Lam 0) * S.Aa⁻¹ := by
    conv_lhs => rw [hJfix0]
    rw [Matrix.mul_add ((S.Aa⁻¹)ᵀ) J, Matrix.add_mul]
  have hJPD : J.PosDef :=
    S.gramian_fixed_posDef hC1 hPpsd hΛ hJpsd hJfix
  have hJinvPD : (J⁻¹).PosDef := hJPD.inv
  -- assemble
  obtain ⟨Sg, hSgdef⟩ : ∃ x, x = emb1 n₁ na nm * Pinf
      * (emb1 n₁ na nm)ᵀ
      + condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ) * J⁻¹
        * (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ))ᵀ := ⟨_, rfl⟩
  have hSgpsd : Sg.PosSemidef :=
    CondChart.posSemidef (Sg := Sg)
      ⟨Pinf, Lam, (0 : Matrix (Fin nm) (Fin na) ℝ), J⁻¹,
        hPpsd, hJinvPD, hSgdef⟩
  have hSgfix : dareStep S.fullC S.R S.fullA S.Qw Sg = Sg := by
    have hstep := S.chart_dareStep (Sg := Sg)
      ⟨Pinf, Lam, (0 : Matrix (Fin nm) (Fin na) ℝ), J⁻¹,
        hPpsd, hJinvPD, hSgdef⟩
    rw [hstep, hPfix, S.assembled_lam_fixed hΛ,
      S.assembled_Saa_fixed hPpsd hJPD hJfix]
    have h0 : S.Am * (0 : Matrix (Fin nm) (Fin na) ℝ) * S.Aa⁻¹
        = 0 := by
      rw [Matrix.mul_zero, Matrix.zero_mul]
    rw [h0, ← hSgdef]
  -- extinction and the positive corner
  have hVtM : (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ))ᵀ
      * embM n₁ na nm = 0 := by
    have h := congrArg Matrix.transpose
      (embMt_mul_condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ))
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] at h
  have hVtA : (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ))ᵀ
      * embA n₁ na nm = 1 := by
    have h := congrArg Matrix.transpose
      (embAt_mul_condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ))
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_one] at h
  have hext : Sg * embM n₁ na nm = 0 := by
    rw [hSgdef, Matrix.add_mul,
      Matrix.mul_assoc (emb1 n₁ na nm * Pinf), emb1t_mul_embM,
      Matrix.mul_zero,
      Matrix.mul_assoc (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ)
        * J⁻¹), hVtM, Matrix.mul_zero, add_zero]
  have hcorner : ((embA n₁ na nm)ᵀ * Sg * embA n₁ na nm).PosDef := by
    have heq : (embA n₁ na nm)ᵀ * Sg * embA n₁ na nm = J⁻¹ := by
      rw [hSgdef, Matrix.mul_add, Matrix.add_mul]
      have ht1 : (embA n₁ na nm)ᵀ
          * (emb1 n₁ na nm * Pinf * (emb1 n₁ na nm)ᵀ)
          * embA n₁ na nm = 0 := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, embAt_mul_emb1,
          Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
      have ht2 : (embA n₁ na nm)ᵀ
          * (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ) * J⁻¹
            * (condV Lam (0 : Matrix (Fin nm) (Fin na) ℝ))ᵀ)
          * embA n₁ na nm = J⁻¹ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, embAt_mul_condV,
          Matrix.one_mul, Matrix.mul_assoc, hVtA, Matrix.mul_one]
      rw [ht1, ht2, zero_add]
    rw [heq]
    exact hJinvPD
  exact ⟨Sg, hSgpsd, hSgfix,
    S.fixed_specLe hSgpsd hSgfix hext hcorner⟩

/-- **`fact:dare-strong`, uniqueness**: two strong solutions coincide
— `lem:supremal` seeded at `Σ∞ + Σ∞'` converges to both. -/
theorem strong_solution_unique (hC1 : S.C1)
    {Sinf Sinf' : Matrix (ix n₁ na nm) (ix n₁ na nm) ℝ}
    (hS : S.IsStrongSolution Sinf) (hS' : S.IsStrongSolution Sinf')
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    Sinf = Sinf' := by
  have hL0 : (Sinf + Sinf').PosSemidef :=
    hS.posSemidef.add hS'.posSemidef
  have hdom : (Sinf + Sinf' - Sinf).PosSemidef := by
    rw [add_sub_cancel_left]
    exact hS'.posSemidef
  have hdom' : (Sinf + Sinf' - Sinf').PosSemidef := by
    rw [add_sub_cancel_right]
    exact hS.posSemidef
  have h1 := S.supremal_tendsto hC1 hS hL0 hdom hcm hPB
    (S.strong_Fs_schur hC1 hS)
  have h2 := S.supremal_tendsto hC1 hS' hL0 hdom' hcm hPB
    (S.strong_Fs_schur hC1 hS')
  have hb : ∀ T, ‖Sinf - Sinf'‖
      ≤ ‖S.dareFrom (Sinf + Sinf') T - Sinf'‖
        + ‖S.dareFrom (Sinf + Sinf') T - Sinf‖ := by
    intro T
    calc ‖Sinf - Sinf'‖
        = ‖(S.dareFrom (Sinf + Sinf') T - Sinf')
            - (S.dareFrom (Sinf + Sinf') T - Sinf)‖ := by
          congr 1
          abel
    _ ≤ _ := norm_sub_le _ _
  have hsum : Tendsto (fun T =>
      ‖S.dareFrom (Sinf + Sinf') T - Sinf'‖
        + ‖S.dareFrom (Sinf + Sinf') T - Sinf‖) atTop (nhds 0) := by
    have h := h2.add h1
    simpa using h
  have hle : ‖Sinf - Sinf'‖ ≤ 0 :=
    ge_of_tendsto hsum (Filter.Eventually.of_forall hb)
  have h0 : Sinf - Sinf' = 0 := by
    rw [← norm_le_zero_iff]
    exact hle
  exact sub_eq_zero.mp h0

/-- `fact:dare-strong` in one statement: the strong solution exists
and is unique (uniqueness under the power-bounded marginal). -/
theorem existsUnique_strong_solution (hC1 : S.C1)
    {cm : ℝ} (hcm : 0 ≤ cm) (hPB : ∀ k : ℕ, ‖S.Am ^ k‖ ≤ cm) :
    ∃! Sinf, S.IsStrongSolution Sinf := by
  obtain ⟨Sg, hSg⟩ := S.exists_strong_solution hC1
  exact ⟨Sg, hSg, fun y hy =>
    S.strong_solution_unique hC1 hy hSg hcm hPB⟩

end DareSystem


end Dare
end Estimation
