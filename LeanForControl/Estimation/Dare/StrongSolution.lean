import LeanForControl.Estimation.Dare.KernelInvariance
import Architect

/-!
# The corner-kernel spectrum theorem (risk R3, resolved)

Assembly of `KernelInvariance.lean` into the deck's
`lem:structure`-1 / `lem:structure-marg` mechanism, made honest: at a
PSD fixed point `Σ∞`, if a corner of `Σ∞` — carried by a rectangular
embedding `E` intertwining the dynamics, `AᵀE = EAaᵀ` — has a
nontrivial kernel, then `spec(Aa)` and `spec(F∞)` share an
eigenvalue. Instantiated at the antistable corner, `|spec(Aa)| > 1`
against the strong solution's `ρ(F∞) ≤ 1` forces the corner to be
positive definite.

Design: all block manipulation is real (the corner is `EᵀΣ∞E`, the
invariance and filter-agreement facts are real vector statements);
complexification is purely functorial through one transport lemma
(`complexify_mulVec_eq_on_ker`), and the eigenvalue comes from the
restriction of `complexify Aaᵀ` to the complexified corner kernel.
Note the route consumes only `ρ(F∞) ≤ 1` from the `fact:dare-strong`
bundle — not the spectrum split `eq:Finf-spec`.
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems

/-! ### Transport of real kernel-conditioned identities to ℂ -/

/-- Spectrum is invariant under transpose (complex matrices). -/
lemma mem_spectrum_transpose_iff {ι' : Type*} [Fintype ι'] [DecidableEq ι']
    {M : Matrix ι' ι' ℂ} {μ : ℂ} :
    μ ∈ spectrum ℂ Mᵀ ↔ μ ∈ spectrum ℂ M := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly,
    Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_transpose]

/-- **Transport lemma**: a real identity `M₁x = M₂x`, valid on the
real kernel of `N`, holds complexified on the complex kernel of `N`
(split into real and imaginary parts, apply, recombine). -/
lemma complexify_mulVec_eq_on_ker {ι' ιa : Type*} [Fintype ι']
    [DecidableEq ι'] [Fintype ιa] [DecidableEq ιa]
    {M₁ M₂ : Matrix ι' ιa ℝ} {N : Matrix ιa ιa ℝ}
    (h : ∀ x : ιa → ℝ, N *ᵥ x = 0 → M₁ *ᵥ x = M₂ *ᵥ x)
    {u : ιa → ℂ} (hu : complexify N *ᵥ u = 0) :
    complexify M₁ *ᵥ u = complexify M₂ *ᵥ u := by
  have hur : N *ᵥ (fun j => (u j).re) = 0 := by
    funext i
    have h0 : (complexify N *ᵥ u) i = 0 := by rw [hu]; rfl
    have hre := complexify_mulVec_re N u i
    rw [h0] at hre
    simpa using hre.symm
  have hui : N *ᵥ (fun j => (u j).im) = 0 := by
    funext i
    have h0 : (complexify N *ᵥ u) i = 0 := by rw [hu]; rfl
    have him := complexify_mulVec_im N u i
    rw [h0] at him
    simpa using him.symm
  have h1 := h _ hur
  have h2 := h _ hui
  funext i
  have e1 : ∀ M : Matrix ι' ιa ℝ, (complexify M *ᵥ u) i
      = ((M *ᵥ fun j => (u j).re) i : ℝ)
        + ((M *ᵥ fun j => (u j).im) i : ℝ) * Complex.I := by
    intro M
    rw [← Complex.re_add_im ((complexify M *ᵥ u) i),
      complexify_mulVec_re, complexify_mulVec_im]
  rw [e1 M₁, e1 M₂, h1, h2]

/-- A corner-kernel vector, embedded, lies in the full kernel
(PSD needed). -/
lemma mulVec_corner_eq_zero {ι ιa : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype ιa] [DecidableEq ιa]
    {M : Matrix ι ι ℝ} (hM : M.PosSemidef)
    {E : Matrix ι ιa ℝ} {x : ιa → ℝ} (hx : (Eᵀ * M * E) *ᵥ x = 0) :
    M *ᵥ (E *ᵥ x) = 0 := by
  refine hM.mulVec_eq_zero_of_quadForm_eq_zero ?_
  rw [quadForm_mulVec, quadForm, hx, dotProduct_zero]

/-! ### Corner positivity along the recursion -/

section Corner

variable {ι κ ιa : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype ιa] [DecidableEq ιa]

variable {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ} {Sg : Matrix ι ι ℝ}
variable {E : Matrix ι ιa ℝ}

/-- The update preserves corner positivity: `EᵀΣE ≻ 0 ⇒ EᵀU(Σ)E ≻ 0`
(`fact:update-kernel`, corner form — fully generic in the
embedding). -/
lemma updM_corner_posDef (hR : R.PosDef) (hSg : Sg.PosSemidef)
    (hc : (Eᵀ * Sg * E).PosDef) :
    (Eᵀ * updM C R Sg * E).PosDef := by
  have hU := updM_posSemidef (C := C) hR hSg
  have hpsd : (Eᵀ * updM C R Sg * E).PosSemidef := by
    have h := hU.conjTranspose_mul_mul_same E
    rwa [show Eᴴ = Eᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun v hv => ?_
  rcases lt_or_eq_of_le (hpsd.quadForm_nonneg v) with h | h
  · exact h
  · exfalso
    have hker : (Eᵀ * updM C R Sg * E) *ᵥ v = 0 :=
      hpsd.mulVec_eq_zero_of_quadForm_eq_zero h.symm
    have hUker : updM C R Sg *ᵥ (E *ᵥ v) = 0 :=
      mulVec_corner_eq_zero hU hker
    have hSker : Sg *ᵥ (E *ᵥ v) = 0 :=
      (updM_mulVec_eq_zero_iff hR hSg).mp hUker
    have hq : quadForm (Eᵀ * Sg * E) v = 0 := by
      rw [← quadForm_mulVec, quadForm, hSker, dotProduct_zero]
    exact absurd hq (ne_of_gt (hc.quadForm_pos hv))

variable {A Qw : Matrix ι ι ℝ} {Aa : Matrix ιa ιa ℝ}

/-- The corner step identity: with the intertwining `AᵀE = EAaᵀ` and
no noise reaching the corner (`EᵀQ_wE = 0`),
`Eᵀ·R(Σ)·E = Aa·(EᵀU(Σ)E)·Aaᵀ`. -/
lemma dareStep_corner_eq (hint : Aᵀ * E = E * Aaᵀ)
    (hQE : Eᵀ * Qw * E = 0) :
    Eᵀ * dareStep C R A Qw Sg * E
      = Aa * (Eᵀ * updM C R Sg * E) * Aaᵀ := by
  have hEA : Eᵀ * A = Aa * Eᵀ := by
    have h := congrArg Matrix.transpose hint
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose] at h
    exact h
  unfold dareStep
  rw [Matrix.mul_add, Matrix.add_mul, hQE, add_zero]
  calc Eᵀ * (A * updM C R Sg * Aᵀ) * E
      = (Eᵀ * A) * updM C R Sg * (Aᵀ * E) := by
        simp only [Matrix.mul_assoc]
  _ = (Aa * Eᵀ) * updM C R Sg * (E * Aaᵀ) := by rw [hEA, hint]
  _ = Aa * (Eᵀ * updM C R Sg * E) * Aaᵀ := by
        simp only [Matrix.mul_assoc]

/-- Corner positivity propagates through one covariance step
(`lem:structure`-3, one step): `EᵀΣE ≻ 0`, `Aa` nonsingular give
`Eᵀ·R(Σ)·E ≻ 0`. -/
lemma dareStep_corner_posDef (hR : R.PosDef) (hSg : Sg.PosSemidef)
    (hc : (Eᵀ * Sg * E).PosDef) (hint : Aᵀ * E = E * Aaᵀ)
    (hQE : Eᵀ * Qw * E = 0) (hAa : IsUnit Aa.det) :
    (Eᵀ * dareStep C R A Qw Sg * E).PosDef := by
  rw [dareStep_corner_eq hint hQE]
  have hU := updM_corner_posDef (C := C) hR hSg hc
  have hherm : (Aa * (Eᵀ * updM C R Sg * E) * Aaᵀ).IsHermitian := by
    have h := hU.posSemidef.mul_mul_conjTranspose_same Aa
    rw [show Aaᴴ = Aaᵀ from
      Matrix.conjTranspose_eq_transpose_of_trivial _] at h
    exact h.1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun v hv => ?_
  have hAv : Aaᵀ *ᵥ v ≠ 0 := by
    intro h0
    apply hv
    have h1 := congrArg (fun w => (Aaᵀ)⁻¹ *ᵥ w) h0
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h1
    rwa [Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose]),
      Matrix.one_mulVec] at h1
  have hq : quadForm (Eᵀ * updM C R Sg * E) (Aaᵀ *ᵥ v)
      = quadForm (Aa * (Eᵀ * updM C R Sg * E) * Aaᵀ) v := by
    rw [quadForm_mulVec, Matrix.transpose_transpose]
  show 0 < quadForm (Aa * (Eᵀ * updM C R Sg * E) * Aaᵀ) v
  rw [← hq]
  exact hU.quadForm_pos hAv

end Corner

/-! ### The corner-kernel spectrum theorem -/

variable {ι κ κg ιa : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype κg]
  [Fintype ιa] [DecidableEq ιa]

variable {C : Matrix κ ι ℝ} {R : Matrix κ κ ℝ} {A Qw Sinf : Matrix ι ι ℝ}

/-- **The corner-kernel spectrum theorem**: at a PSD fixed point with
`Q_w = GQGᵀ`, `Q ≻ 0`, if an intertwined corner `EᵀΣ∞E` of the
covariance (with `AᵀE = EAaᵀ`, `E` injective over ℂ) kills a nonzero
vector, then `spec(Aa)` and `spec(F∞)` share an eigenvalue — the
corner's mode is left un-reflected by the filter. -/
theorem exists_common_spectrum_of_corner_kernel
    (hR : R.PosDef) (hSinf : Sinf.PosSemidef)
    (hfix : dareStep C R A Qw Sinf = Sinf)
    {G : Matrix ι κg ℝ} {Q : Matrix κg κg ℝ} (hQ : Q.PosDef)
    (hQw : Qw = G * Q * Gᵀ)
    {E : Matrix ι ιa ℝ} {Aa : Matrix ιa ιa ℝ}
    (hint : Aᵀ * E = E * Aaᵀ)
    (hEinj : ∀ u : ιa → ℂ, complexify E *ᵥ u = 0 → u = 0)
    {v : ιa → ℝ} (hv : v ≠ 0) (hker : (Eᵀ * Sinf * E) *ᵥ v = 0) :
    ∃ μ : ℂ, μ ∈ spectrum ℂ (complexify Aa)
      ∧ μ ∈ spectrum ℂ (complexify (errMap C R A Sinf)) := by
  classical
  -- the real facts on the corner kernel
  have hcorner : ∀ x : ιa → ℝ, (Eᵀ * Sinf * E) *ᵥ x = 0 →
      Sinf *ᵥ (E *ᵥ x) = 0 :=
    fun x hx => mulVec_corner_eq_zero hSinf hx
  have hinv_real : ∀ x : ιa → ℝ, (Eᵀ * Sinf * E) *ᵥ x = 0 →
      (Eᵀ * Sinf * E * Aaᵀ) *ᵥ x = (0 : Matrix ιa ιa ℝ) *ᵥ x := by
    intro x hx
    have h1 := hcorner x hx
    have h2 : Sinf *ᵥ (Aᵀ *ᵥ (E *ᵥ x)) = 0 :=
      (ker_fixedPoint hR hSinf hfix hQ hQw h1).1
    have h3 : Aᵀ *ᵥ (E *ᵥ x) = E *ᵥ (Aaᵀ *ᵥ x) := by
      rw [Matrix.mulVec_mulVec, hint, ← Matrix.mulVec_mulVec]
    rw [h3] at h2
    have h5 : (Eᵀ * Sinf * E * Aaᵀ) *ᵥ x
        = Eᵀ *ᵥ (Sinf *ᵥ (E *ᵥ (Aaᵀ *ᵥ x))) := by
      simp only [← Matrix.mulVec_mulVec]
    rw [h5, h2, Matrix.mulVec_zero, Matrix.zero_mulVec]
  have hagree_real : ∀ x : ιa → ℝ, (Eᵀ * Sinf * E) *ᵥ x = 0 →
      ((errMap C R A Sinf)ᵀ * E) *ᵥ x = (E * Aaᵀ) *ᵥ x := by
    intro x hx
    have h1 := hcorner x hx
    have h2 : Sinf *ᵥ (Aᵀ *ᵥ (E *ᵥ x)) = 0 :=
      (ker_fixedPoint hR hSinf hfix hQ hQw h1).1
    have h3 := errMap_transpose_mulVec_eq (C := C) hR hSinf h2
    calc ((errMap C R A Sinf)ᵀ * E) *ᵥ x
        = (errMap C R A Sinf)ᵀ *ᵥ (E *ᵥ x) := by
          rw [← Matrix.mulVec_mulVec]
    _ = Aᵀ *ᵥ (E *ᵥ x) := h3
    _ = (E * Aaᵀ) *ᵥ x := by
          rw [Matrix.mulVec_mulVec, hint]
  -- the complexified corner kernel
  set Kc : Submodule ℂ (ιa → ℂ) :=
    LinearMap.ker (Matrix.mulVecLin (complexify (Eᵀ * Sinf * E)))
    with hKc
  have hvKc : complexifyVec v ∈ Kc := by
    rw [hKc, LinearMap.mem_ker, Matrix.mulVecLin_apply,
      complexify_mulVec, hker, complexifyVec_zero]
  have hKcne : Kc ≠ ⊥ :=
    (Submodule.ne_bot_iff Kc).mpr ⟨complexifyVec v, hvKc,
      fun h0 => hv (complexifyVec_eq_zero_iff.mp h0)⟩
  -- the complexified corner kernel is `complexify Aaᵀ`-invariant
  have hinv : ∀ u ∈ Kc,
      Matrix.mulVecLin (complexify Aaᵀ) u ∈ Kc := by
    intro u hu
    rw [hKc, LinearMap.mem_ker, Matrix.mulVecLin_apply] at hu ⊢
    have h := complexify_mulVec_eq_on_ker hinv_real hu
    rw [complexify_zero, Matrix.zero_mulVec, complexify_mul,
      ← Matrix.mulVec_mulVec] at h
    exact h
  -- an eigenvalue of the restriction
  have hne : Nontrivial Kc := Submodule.nontrivial_iff_ne_bot.mpr hKcne
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue
    ((Matrix.mulVecLin (complexify Aaᵀ)).restrict hinv)
  obtain ⟨⟨u, huK⟩, huvec⟩ := hμ.exists_hasEigenvector
  have hune : u ≠ 0 := by
    intro h0
    exact huvec.2 (by simp [h0])
  have heig : complexify Aaᵀ *ᵥ u = μ • u := by
    have h1 := huvec.apply_eq_smul
    have h2 := congrArg Subtype.val h1
    rw [LinearMap.restrict_apply] at h2
    simpa [Matrix.mulVecLin_apply] using h2
  -- μ is an eigenvalue of Aa
  have hμAa : μ ∈ spectrum ℂ (complexify Aa) := by
    refine mem_spectrum_transpose_iff.mp ?_
    rw [← complexify_transpose]
    exact mem_spectrum_of_mulVec_eq_smul hune heig
  -- μ is an eigenvalue of F∞, via the embedded eigenvector
  have huKc : complexify (Eᵀ * Sinf * E) *ᵥ u = 0 := by
    have := huK
    rwa [hKc, LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  have hFeq : complexify ((errMap C R A Sinf)ᵀ)
      *ᵥ (complexify E *ᵥ u)
      = μ • (complexify E *ᵥ u) := by
    calc complexify ((errMap C R A Sinf)ᵀ) *ᵥ (complexify E *ᵥ u)
        = complexify ((errMap C R A Sinf)ᵀ * E) *ᵥ u := by
          rw [complexify_mul, ← Matrix.mulVec_mulVec]
    _ = complexify (E * Aaᵀ) *ᵥ u :=
          complexify_mulVec_eq_on_ker hagree_real huKc
    _ = complexify E *ᵥ (complexify Aaᵀ *ᵥ u) := by
          rw [complexify_mul, ← Matrix.mulVec_mulVec]
    _ = complexify E *ᵥ (μ • u) := by rw [heig]
    _ = μ • (complexify E *ᵥ u) := by
          rw [Matrix.mulVec_smul]
  have huhne : complexify E *ᵥ u ≠ 0 := fun h0 => hune (hEinj u h0)
  refine ⟨μ, hμAa, ?_⟩
  refine mem_spectrum_transpose_iff.mp ?_
  rw [← complexify_transpose]
  exact mem_spectrum_of_mulVec_eq_smul huhne hFeq

end Dare
end Estimation