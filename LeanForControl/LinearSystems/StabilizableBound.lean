import LeanForControl.LinearSystems.LQ
import LeanForControl.LinearSystems.Schur
import LeanForControl.LinearSystems.Detectability
import LeanForControl.LinearSystems.StagedFacts
import LeanForControl.LinearSystems.Controllability
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Architect

/-!
# Uniform value bounds under stabilizability (M2 layer)

The quantitative heart of `fact:lqr`: under stabilizability the Riccati
value iterates admit a uniform quadratic bound. The route is a
**polynomial spectral split**: Bezout projections built from the
stable/antistable factors of the characteristic polynomial separate the
state into a geometrically decaying part (Gelfand, applied to `M·Ps`)
and a part inside the reachable subspace (Hautus pairing), which a
minimum-energy control removes in `n` steps.
-/

namespace LinearSystems

open Matrix Polynomial Filter

open scoped Matrix.Norms.Operator

variable {d : ℕ}

/-- The stable factor of the characteristic polynomial. -/
noncomputable def stabPoly (M : Matrix (Fin d) (Fin d) ℂ) : Polynomial ℂ :=
  ((M.charpoly.roots.filter (fun μ => ‖μ‖ < 1)).map
    (fun μ => Polynomial.X - Polynomial.C μ)).prod

/-- The antistable factor of the characteristic polynomial. -/
noncomputable def antiPoly (M : Matrix (Fin d) (Fin d) ℂ) : Polynomial ℂ :=
  ((M.charpoly.roots.filter (fun μ => ¬ ‖μ‖ < 1)).map
    (fun μ => Polynomial.X - Polynomial.C μ)).prod

lemma stabPoly_mul_antiPoly (M : Matrix (Fin d) (Fin d) ℂ) :
    stabPoly M * antiPoly M = M.charpoly := by
  have hmonic := M.charpoly_monic
  have hsplits : M.charpoly.Splits := IsAlgClosed.splits M.charpoly
  have hcard : Multiset.card M.charpoly.roots = M.charpoly.natDegree :=
    Polynomial.splits_iff_card_roots.mp hsplits
  have h1 := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (p := M.charpoly) hcard
  rw [hmonic.leadingCoeff, Polynomial.C_1, one_mul] at h1
  calc stabPoly M * antiPoly M
      = ((M.charpoly.roots.filter (fun μ => ‖μ‖ < 1)).map
          (fun μ => Polynomial.X - Polynomial.C μ)).prod
        * ((M.charpoly.roots.filter (fun μ => ¬ ‖μ‖ < 1)).map
          (fun μ => Polynomial.X - Polynomial.C μ)).prod := rfl
  _ = ((M.charpoly.roots.filter (fun μ => ‖μ‖ < 1)
        + M.charpoly.roots.filter (fun μ => ¬ ‖μ‖ < 1)).map
          (fun μ => Polynomial.X - Polynomial.C μ)).prod := by
      rw [Multiset.map_add, Multiset.prod_add]
  _ = M.charpoly := by
      rw [Multiset.filter_add_not]
      exact h1

lemma stabPoly_monic (M : Matrix (Fin d) (Fin d) ℂ) :
    (stabPoly M).Monic :=
  Polynomial.monic_multisetProd_X_sub_C _

lemma antiPoly_monic (M : Matrix (Fin d) (Fin d) ℂ) :
    (antiPoly M).Monic :=
  Polynomial.monic_multisetProd_X_sub_C _

lemma stabPoly_root_lt {M : Matrix (Fin d) (Fin d) ℂ} {μ : ℂ}
    (h : (stabPoly M).IsRoot μ) : ‖μ‖ < 1 := by
  unfold stabPoly at h
  rw [Polynomial.IsRoot.def, Polynomial.eval_multiset_prod] at h
  have hz := Multiset.prod_eq_zero_iff.mp h
  rw [Multiset.map_map, Multiset.mem_map] at hz
  obtain ⟨ν, hν, hz0⟩ := hz
  have h2 : μ = ν := by
    have h3 : Polynomial.eval μ (Polynomial.X - Polynomial.C ν) = 0 := by
      have h5 := hz0
      simpa using h5
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at h3
    exact h3
  have h4 := (Multiset.mem_filter.mp hν).2
  rwa [← h2] at h4

lemma antiPoly_root_ge {M : Matrix (Fin d) (Fin d) ℂ} {μ : ℂ}
    (h : (antiPoly M).IsRoot μ) : ¬ ‖μ‖ < 1 := by
  unfold antiPoly at h
  rw [Polynomial.IsRoot.def, Polynomial.eval_multiset_prod] at h
  have hz := Multiset.prod_eq_zero_iff.mp h
  rw [Multiset.map_map, Multiset.mem_map] at hz
  obtain ⟨ν, hν, hz0⟩ := hz
  have h2 : μ = ν := by
    have h3 : Polynomial.eval μ (Polynomial.X - Polynomial.C ν) = 0 := by
      have h5 := hz0
      simpa using h5
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at h3
    exact h3
  have h4 := (Multiset.mem_filter.mp hν).2
  rwa [← h2] at h4

/-- The stable and antistable factors are coprime. -/
lemma isCoprime_stabPoly_antiPoly (M : Matrix (Fin d) (Fin d) ℂ) :
    IsCoprime (stabPoly M) (antiPoly M) := by
  by_contra hnc
  have hgu : ¬ IsUnit (EuclideanDomain.gcd (stabPoly M) (antiPoly M)) :=
    fun h => hnc (EuclideanDomain.gcd_isUnit_iff.mp h)
  set g := EuclideanDomain.gcd (stabPoly M) (antiPoly M) with hgdef
  have hgs : g ∣ stabPoly M := EuclideanDomain.gcd_dvd_left _ _
  have hga : g ∣ antiPoly M := EuclideanDomain.gcd_dvd_right _ _
  have hg0 : g ≠ 0 := by
    intro h0
    have h1 : stabPoly M = 0 := by
      have := hgs
      rw [h0] at this
      exact zero_dvd_iff.mp this
    exact (stabPoly_monic M).ne_zero h1
  have hdeg : 0 < g.degree := by
    rcases le_or_gt g.degree 0 with h | h
    · exfalso
      have hgc : g = Polynomial.C (g.coeff 0) :=
        Polynomial.eq_C_of_degree_le_zero h
      have ha : g.coeff 0 ≠ 0 := by
        intro h0
        exact hg0 (by rw [hgc, h0, Polynomial.C_0])
      refine hgu ?_
      rw [hgc]
      exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha)
    · exact h
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  have hz1 : (stabPoly M).IsRoot z := by
    obtain ⟨q, hq⟩ := hgs
    rw [Polynomial.IsRoot.def, hq, Polynomial.eval_mul, hz, zero_mul]
  have hz2 : (antiPoly M).IsRoot z := by
    obtain ⟨q, hq⟩ := hga
    rw [Polynomial.IsRoot.def, hq, Polynomial.eval_mul, hz, zero_mul]
  exact antiPoly_root_ge hz2 (stabPoly_root_lt hz1)

/-- Polynomial calculus on an eigenvector. -/
lemma aeval_mulVec_eigenvector {M : Matrix (Fin d) (Fin d) ℂ} {μ : ℂ}
    {w : Fin d → ℂ} (hw : M *ᵥ w = μ • w) (p : Polynomial ℂ) :
    Polynomial.aeval M p *ᵥ w = Polynomial.eval μ p • w := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Matrix.add_mulVec, hp, hq, Polynomial.eval_add,
      add_smul]
  | monomial n a =>
    have hpow : ∀ k : ℕ, M ^ k *ᵥ w = μ ^ k • w := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
          hw, smul_smul, ← pow_succ]
    have h1 : (algebraMap ℂ (Matrix (Fin d) (Fin d) ℂ)) a *ᵥ w
        = a • w := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
        Matrix.one_mulVec]
    rw [Polynomial.aeval_monomial, Polynomial.eval_monomial,
      ← Matrix.mulVec_mulVec, hpow, Matrix.mulVec_smul, h1, smul_smul]
    congr 1
    ring

/-- **The Bezout spectral split**: idempotent commuting projections with
a geometrically decaying stable part and a `χₐ`-annihilated antistable
part. -/
theorem exists_stable_split (M : Matrix (Fin d) (Fin d) ℂ) :
    ∃ (Ps Pa : Matrix (Fin d) (Fin d) ℂ) (c ρ : ℝ),
      0 < c ∧ 0 < ρ ∧ ρ < 1 ∧
      Ps + Pa = 1 ∧
      M * Pa = Pa * M ∧ Pa * Pa = Pa ∧
      Polynomial.aeval M (antiPoly M) * Pa = 0 ∧
      (∀ (k : ℕ) (x : Fin d → ℂ),
        ‖M ^ k *ᵥ (Ps *ᵥ x)‖ ≤ c * ρ ^ k * ‖x‖) := by
  classical
  obtain ⟨u, v, huv⟩ := isCoprime_stabPoly_antiPoly M
  set Ps := Polynomial.aeval M (v * antiPoly M) with hPs
  set Pa := Polynomial.aeval M (u * stabPoly M) with hPa
  -- basic algebra of the projections
  have hsum : Ps + Pa = 1 := by
    rw [hPs, hPa, ← map_add, add_comm (v * antiPoly M) (u * stabPoly M),
      huv, map_one]
  have hcomm : ∀ p : Polynomial ℂ,
      M * Polynomial.aeval M p = Polynomial.aeval M p * M := by
    intro p
    have h1 : M * Polynomial.aeval M p
        = Polynomial.aeval M (Polynomial.X * p) := by
      rw [map_mul, Polynomial.aeval_X]
    have h2 : Polynomial.aeval M p * M
        = Polynomial.aeval M (p * Polynomial.X) := by
      rw [map_mul, Polynomial.aeval_X]
    rw [h1, h2, mul_comm p Polynomial.X]
  have hchar0 : Polynomial.aeval M M.charpoly = 0 :=
    Matrix.aeval_self_charpoly M
  have hPsPa : Ps * Pa = 0 := by
    rw [hPs, hPa, ← map_mul,
      show v * antiPoly M * (u * stabPoly M)
        = v * u * (stabPoly M * antiPoly M) from by ring,
      stabPoly_mul_antiPoly, map_mul, hchar0, mul_zero]
  have hPaPs : Pa * Ps = 0 := by
    rw [hPs, hPa, ← map_mul,
      show u * stabPoly M * (v * antiPoly M)
        = u * v * (stabPoly M * antiPoly M) from by ring,
      stabPoly_mul_antiPoly, map_mul, hchar0, mul_zero]
  have hPa2 : Pa * Pa = Pa := by
    have h1 : Pa * (Ps + Pa) = Pa := by rw [hsum, Matrix.mul_one]
    rw [Matrix.mul_add, hPaPs, zero_add] at h1
    exact h1
  have hPaM : M * Pa = Pa * M := hcomm _
  have hPaAnti : Polynomial.aeval M (antiPoly M) * Pa = 0 := by
    rw [hPa, ← map_mul,
      show antiPoly M * (u * stabPoly M)
        = u * (stabPoly M * antiPoly M) from by ring,
      stabPoly_mul_antiPoly, map_mul, hchar0, mul_zero]
  have hPsStab : Polynomial.aeval M (stabPoly M) * Ps = 0 := by
    rw [hPs, ← map_mul,
      show stabPoly M * (v * antiPoly M)
        = v * (stabPoly M * antiPoly M) from by ring,
      stabPoly_mul_antiPoly, map_mul, hchar0, mul_zero]
  -- the stable closed part has spectrum in the open disc
  have hspec : ∀ μ ∈ spectrum ℂ (M * Ps), ‖μ‖ < 1 := by
    intro μ hμ
    rcases eq_or_ne μ 0 with h0 | hne
    · rw [h0, norm_zero]
      norm_num
    have hspec' : μ ∈ spectrum ℂ (Matrix.toLin' (M * Ps)) := by
      rw [Matrix.spectrum_toLin']
      exact hμ
    obtain ⟨w, hw⟩ := (Module.End.hasEigenvalue_iff_mem_spectrum.mpr
      hspec').exists_hasEigenvector
    have hMPsw : (M * Ps) *ᵥ w = μ • w := by
      have := hw.apply_eq_smul
      rwa [Matrix.toLin'_apply] at this
    -- the stable factor annihilates `M * Ps`
    have hstabMPs : Polynomial.aeval M (stabPoly M) * (M * Ps) = 0 := by
      calc Polynomial.aeval M (stabPoly M) * (M * Ps)
          = Polynomial.aeval M (stabPoly M) * M * Ps := by
            rw [Matrix.mul_assoc]
      _ = M * Polynomial.aeval M (stabPoly M) * Ps := by
            rw [hcomm]
      _ = M * (Polynomial.aeval M (stabPoly M) * Ps) := by
            rw [Matrix.mul_assoc]
      _ = 0 := by rw [hPsStab, Matrix.mul_zero]
    have hstabw : Polynomial.aeval M (stabPoly M) *ᵥ w = 0 := by
      have h1 : Polynomial.aeval M (stabPoly M) *ᵥ ((M * Ps) *ᵥ w)
          = 0 := by
        rw [Matrix.mulVec_mulVec, hstabMPs, Matrix.zero_mulVec]
      rw [hMPsw, Matrix.mulVec_smul] at h1
      have h2 := congrArg (fun z => μ⁻¹ • z) h1
      simpa [smul_smul, inv_mul_cancel₀ hne] using h2
    -- hence the eigenvector is genuinely stable
    have hPaw : Pa *ᵥ w = 0 := by
      rw [hPa, map_mul, ← Matrix.mulVec_mulVec, hstabw,
        Matrix.mulVec_zero]
    have hPsw : Ps *ᵥ w = w := by
      have h1 : (Ps + Pa) *ᵥ w = w := by
        rw [hsum, Matrix.one_mulVec]
      rw [Matrix.add_mulVec, hPaw, add_zero] at h1
      exact h1
    have hMw : M *ᵥ w = μ • w := by
      have h1 : (M * Ps) *ᵥ w = M *ᵥ (Ps *ᵥ w) :=
        (Matrix.mulVec_mulVec _ _ _).symm
      rw [hPsw] at h1
      rw [← h1, hMPsw]
    have hroot : Polynomial.eval μ (stabPoly M) • w = 0 := by
      rw [← aeval_mulVec_eigenvector hMw, hstabw]
    have hzero : Polynomial.eval μ (stabPoly M) = 0 := by
      by_contra hne'
      have := congrArg (fun z => (Polynomial.eval μ (stabPoly M))⁻¹ • z)
        hroot
      simp [smul_smul, inv_mul_cancel₀ hne'] at this
      exact hw.2 this
    exact stabPoly_root_lt hzero
  obtain ⟨c, ρ, hc, hρ0, hρ1, hdecay⟩ :=
    exists_pow_norm_le_of_spectrum_lt_one hspec
  -- convert the closed-loop decay to open powers against `Ps`
  have hPs2 : Ps * Ps = Ps := by
    have h1 : Ps * (Ps + Pa) = Ps := by rw [hsum, Matrix.mul_one]
    rw [Matrix.mul_add, hPsPa, add_zero] at h1
    exact h1
  have hPsM : M * Ps = Ps * M := hcomm _
  have hMkPs : ∀ k : ℕ, Ps * M ^ k = M ^ k * Ps := by
    intro k
    induction k with
    | zero => simp
    | succ k ih2 =>
      calc Ps * M ^ (k + 1) = Ps * M ^ k * M := by
            rw [pow_succ, Matrix.mul_assoc]
      _ = M ^ k * Ps * M := by rw [ih2]
      _ = M ^ k * (Ps * M) := by rw [Matrix.mul_assoc]
      _ = M ^ k * (M * Ps) := by rw [hPsM]
      _ = M ^ (k + 1) * Ps := by
          rw [pow_succ]
          simp only [Matrix.mul_assoc]
  have hpowPs : ∀ k : ℕ, M ^ k * Ps = (M * Ps) ^ k * Ps := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep : (M * Ps) ^ (k + 1) * Ps = M ^ (k + 1) * Ps := by
        calc (M * Ps) ^ (k + 1) * Ps
            = (M * Ps) * ((M * Ps) ^ k * Ps) := by
              rw [pow_succ']
              simp only [Matrix.mul_assoc]
        _ = (M * Ps) * (M ^ k * Ps) := by rw [ih]
        _ = M * (Ps * M ^ k) * Ps := by simp only [Matrix.mul_assoc]
        _ = M * (M ^ k * Ps) * Ps := by rw [hMkPs k]
        _ = M ^ (k + 1) * (Ps * Ps) := by
            rw [pow_succ']
            simp only [Matrix.mul_assoc]
        _ = M ^ (k + 1) * Ps := by rw [hPs2]
      exact hstep.symm
  refine ⟨Ps, Pa, c * (‖Ps‖ + 1), ρ, ?_, hρ0, hρ1, hsum, hPaM, hPa2,
    hPaAnti, ?_⟩
  · have := norm_nonneg Ps
    positivity
  intro k x
  have h1 : M ^ k *ᵥ (Ps *ᵥ x) = (M * Ps) ^ k *ᵥ (Ps *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hpowPs k]
  rw [h1]
  have h2 : ‖(M * Ps) ^ k *ᵥ (Ps *ᵥ x)‖
      ≤ ‖(M * Ps) ^ k‖ * ‖Ps *ᵥ x‖ := Matrix.linfty_opNorm_mulVec _ _
  have h3 : ‖Ps *ᵥ x‖ ≤ ‖Ps‖ * ‖x‖ := Matrix.linfty_opNorm_mulVec _ _
  have h4 := hdecay k
  have h5 : (0:ℝ) ≤ ρ ^ k := pow_nonneg hρ0.le k
  have h6 := norm_nonneg Ps
  have h7 := norm_nonneg x
  have h8 := norm_nonneg ((M * Ps) ^ k)
  calc ‖(M * Ps) ^ k *ᵥ (Ps *ᵥ x)‖
      ≤ ‖(M * Ps) ^ k‖ * ‖Ps *ᵥ x‖ := h2
  _ ≤ (c * ρ ^ k) * (‖Ps‖ * ‖x‖) := by
      refine mul_le_mul h4 h3 (norm_nonneg _) ?_
      positivity
  _ ≤ c * (‖Ps‖ + 1) * ρ ^ k * ‖x‖ := by nlinarith
  
/-! ### The antistable part is reachable (Hautus pairing) -/

lemma aeval_transpose (M : Matrix (Fin d) (Fin d) ℂ) (p : Polynomial ℂ) :
    (Polynomial.aeval M p)ᵀ = Polynomial.aeval Mᵀ p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.transpose_add, hp, hq, map_add]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Algebra.algebraMap_eq_smul_one,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul,
      Matrix.transpose_smul, Matrix.transpose_pow]

private lemma mulVec_dot {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ)
    (x : Fin l → ℂ) (y : Fin k → ℂ) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]
  congr 1
  rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose]

variable {m' : ℕ}

/-- The `d`-step reachability map. -/
noncomputable def reachMap (M : Matrix (Fin d) (Fin d) ℂ)
    (Bc : Matrix (Fin d) (Fin m') ℂ) :
    (Fin d → Fin m' → ℂ) →ₗ[ℂ] (Fin d → ℂ) where
  toFun := fun us => ∑ j : Fin d, (M ^ (j : ℕ) * Bc) *ᵥ us j
  map_add' := fun us vs => by
    simp only [Pi.add_apply, Matrix.mulVec_add]
    rw [Finset.sum_add_distrib]
  map_smul' := fun c us => by
    simp only [Pi.smul_apply, Matrix.mulVec_smul, RingHom.id_apply]
    rw [Finset.smul_sum]

/-- **The antistable projection lands in the reachable space** — the
quantitative content of Hautus stabilizability, extracted by duality:
a functional killing the reachable space extends, through the
Cayley–Hamilton closure and the surjectivity of the antistable factor
on the annihilator, to one that must vanish on the antistable range. -/
theorem antistable_mem_reach {M : Matrix (Fin d) (Fin d) ℂ}
    {Bc : Matrix (Fin d) (Fin m') ℂ}
    (hstab : IsDetectable Mᵀ Bcᵀ)
    {Pa : Matrix (Fin d) (Fin d) ℂ}
    (hPaAnti : Polynomial.aeval M (antiPoly M) * Pa = 0)
    (x : Fin d → ℂ) :
    Pa *ᵥ x ∈ LinearMap.range (reachMap M Bc) := by
  classical
  by_contra hnot
  obtain ⟨f, hfx, hker⟩ :=
    Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  -- realize the functional as a pairing vector
  set φ : Fin d → ℂ := fun i => f (fun j => if i = j then 1 else 0)
    with hφ
  have hfeq : ∀ y : Fin d → ℂ, f y = y ⬝ᵥ φ := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ f y]
    simp only [dotProduct, hφ, smul_eq_mul]
  -- the annihilation of the reachable space, componentwise
  have hann : ∀ j : Fin d, Bcᵀ *ᵥ (Mᵀ ^ (j : ℕ) *ᵥ φ) = 0 := by
    intro j
    funext l
    set us : Fin d → Fin m' → ℂ := Pi.single j (Pi.single l 1)
      with hus
    have h1 : reachMap M Bc us = (M ^ (j : ℕ) * Bc) *ᵥ Pi.single l 1 := by
      show (∑ i : Fin d, (M ^ (i : ℕ) * Bc) *ᵥ us i) = _
      rw [Finset.sum_eq_single j]
      · rw [hus, Pi.single_eq_same]
      · intro i _ hij
        rw [hus, Pi.single_eq_of_ne hij, Matrix.mulVec_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have h2 : f (reachMap M Bc us) = 0 := by
      have h3 : reachMap M Bc us ∈ LinearMap.range (reachMap M Bc) :=
        LinearMap.mem_range_self _ _
      have h4 := hker ▸ Submodule.mem_map_of_mem
        (p := LinearMap.range (reachMap M Bc)) (f := f) h3
      simpa using h4
    rw [h1, hfeq] at h2
    have h5 : ((M ^ (j : ℕ) * Bc) *ᵥ Pi.single l 1) ⬝ᵥ φ
        = (Bcᵀ *ᵥ (Mᵀ ^ (j : ℕ) *ᵥ φ)) l := by
      rw [mulVec_dot, Matrix.transpose_mul, Matrix.transpose_pow,
        ← Matrix.mulVec_mulVec]
      simp [dotProduct, Pi.single_apply]
    rw [h5] at h2
    have h6 : (0 : Fin m' → ℂ) l = 0 := rfl
    rw [h6]
    exact h2
  -- the Cayley–Hamilton closure: the annihilator is `Mᵀ`-invariant
  set W : Submodule ℂ (Fin d → ℂ) :=
    { carrier := {ψ | ∀ j : Fin d, Bcᵀ *ᵥ (Mᵀ ^ (j : ℕ) *ᵥ ψ) = 0}
      add_mem' := fun ha hb => by
        intro j
        rw [Matrix.mulVec_add, Matrix.mulVec_add, ha j, hb j, add_zero]
      zero_mem' := by
        intro j
        rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
      smul_mem' := fun c ψ hψ => by
        intro j
        rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hψ j, smul_zero] }
    with hW
  have hφW : φ ∈ W := hann
  -- powers beyond `d` stay annihilated, via Cayley–Hamilton
  have hCH : ∀ ψ ∈ W, Bcᵀ *ᵥ (Mᵀ ^ d *ᵥ ψ) = 0 := by
    intro ψ hψ
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0
      funext l
      simp [Matrix.mulVec, dotProduct]
    -- `X^d - charpoly` has degree `< d`
    set q : Polynomial ℂ := Polynomial.X ^ d - Mᵀ.charpoly with hq
    have hMd : Mᵀ ^ d = Polynomial.aeval Mᵀ q := by
      rw [hq, map_sub, Matrix.aeval_self_charpoly, sub_zero,
        map_pow, Polynomial.aeval_X]
    have hdegq : q.natDegree < d := by
      have hmon := Mᵀ.charpoly_monic
      have hdeg : Mᵀ.charpoly.natDegree = d := by
        rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      rcases eq_or_ne q 0 with h0 | h0
      · rw [h0]
        simpa using hd0
      have h1 : q.degree < (Polynomial.X ^ d : Polynomial ℂ).degree := by
        rw [hq]
        refine Polynomial.degree_sub_lt ?_
          (pow_ne_zero d Polynomial.X_ne_zero) ?_
        · rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree
            hmon.ne_zero, hdeg]
        · rw [Polynomial.leadingCoeff_X_pow, hmon.leadingCoeff]
      have h2 : q.degree < (d : ℕ) := by
        rwa [Polynomial.degree_X_pow] at h1
      exact Polynomial.natDegree_lt_iff_degree_lt h0 |>.mpr
        (by exact_mod_cast h2)
    -- expand `aeval q` into low powers
    have hexp := Polynomial.aeval_eq_sum_range (R := ℂ)
      (S := Matrix (Fin d) (Fin d) ℂ) (x := Mᵀ) (p := q)
    have hsum : Polynomial.aeval Mᵀ q *ᵥ ψ
        = ∑ i ∈ Finset.range (q.natDegree + 1),
          q.coeff i • (Mᵀ ^ i *ᵥ ψ) := by
      rw [hexp, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.smul_mulVec]
    rw [hMd, hsum, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hid : i < d := by
      have := Finset.mem_range.mp hi
      omega
    rw [Matrix.mulVec_smul, hψ ⟨i, hid⟩, smul_zero]
  have hWinv : ∀ ψ ∈ W, Mᵀ *ᵥ ψ ∈ W := by
    intro ψ hψ j
    have h1 : Mᵀ ^ (j : ℕ) *ᵥ (Mᵀ *ᵥ ψ) = Mᵀ ^ ((j : ℕ) + 1) *ᵥ ψ := by
      rw [Matrix.mulVec_mulVec, ← pow_succ]
    show Bcᵀ *ᵥ (Mᵀ ^ (j : ℕ) *ᵥ (Mᵀ *ᵥ ψ)) = 0
    rw [h1]
    rcases Nat.lt_or_ge ((j : ℕ) + 1) d with hj | hj
    · exact hψ ⟨(j : ℕ) + 1, hj⟩
    · have hjd : (j : ℕ) + 1 = d := by omega
      rw [hjd]
      exact hCH ψ hψ
  -- the antistable factor acts bijectively on the annihilator
  have hWaeval : ∀ ψ ∈ W, Polynomial.aeval Mᵀ (antiPoly M) *ᵥ ψ ∈ W := by
    intro ψ hψ
    -- polynomial in `Mᵀ` preserves the invariant subspace
    have hgen : ∀ p : Polynomial ℂ, Polynomial.aeval Mᵀ p *ᵥ ψ ∈ W := by
      intro p
      induction p using Polynomial.induction_on' with
      | add p q hp hq =>
        rw [map_add, Matrix.add_mulVec]
        exact W.add_mem hp hq
      | monomial n a =>
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
          Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec]
        refine W.smul_mem a ?_
        induction n with
        | zero =>
          simpa using hψ
        | succ n ihn =>
          rw [pow_succ', ← Matrix.mulVec_mulVec]
          exact hWinv _ ihn
    exact hgen _
  -- injectivity of the antistable factor on the annihilator
  have hinj : ∀ w ∈ W, Polynomial.aeval Mᵀ (antiPoly M) *ᵥ w = 0
      → w = 0 := by
    intro w hwW hw0
    by_contra hwne
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · exact hwne (funext fun l => absurd l.2 (by omega))
    set K : Submodule ℂ (Fin d → ℂ) := W ⊓ LinearMap.ker
      ((Polynomial.aeval Mᵀ (antiPoly M)).mulVecLin) with hK
    have hwK : w ∈ K := by
      refine Submodule.mem_inf.mpr ⟨hwW, LinearMap.mem_ker.mpr ?_⟩
      rw [Matrix.mulVecLin_apply]
      exact hw0
    haveI hKnt : Nontrivial K := by
      refine ⟨⟨⟨w, hwK⟩, 0, ?_⟩⟩
      intro h
      exact hwne (congrArg Subtype.val h)
    have hKinv : ∀ z ∈ K, Mᵀ *ᵥ z ∈ K := by
      intro z hzK
      obtain ⟨hz1, hz2m⟩ := Submodule.mem_inf.mp hzK
      have hz2 : Polynomial.aeval Mᵀ (antiPoly M) *ᵥ z = 0 := by
        have h0 := LinearMap.mem_ker.mp hz2m
        rwa [Matrix.mulVecLin_apply] at h0
      refine Submodule.mem_inf.mpr ⟨hWinv z hz1,
        LinearMap.mem_ker.mpr ?_⟩
      rw [Matrix.mulVecLin_apply]
      have hcommT : Polynomial.aeval Mᵀ (antiPoly M) * Mᵀ
          = Mᵀ * Polynomial.aeval Mᵀ (antiPoly M) := by
        rw [show Polynomial.aeval Mᵀ (antiPoly M) * Mᵀ
            = Polynomial.aeval Mᵀ (antiPoly M * Polynomial.X) from by
          rw [map_mul, Polynomial.aeval_X],
          show Mᵀ * Polynomial.aeval Mᵀ (antiPoly M)
            = Polynomial.aeval Mᵀ (Polynomial.X * antiPoly M) from by
          rw [map_mul, Polynomial.aeval_X],
          mul_comm (antiPoly M) Polynomial.X]
      rw [Matrix.mulVec_mulVec, hcommT, ← Matrix.mulVec_mulVec, hz2,
        Matrix.mulVec_zero]
    set g : K →ₗ[ℂ] K := (Matrix.mulVecLin Mᵀ).restrict
      (fun z hz => by
        rw [Matrix.mulVecLin_apply]
        exact hKinv z hz) with hg
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue g
    obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
    have hzval : Mᵀ *ᵥ (z : Fin d → ℂ) = μ • (z : Fin d → ℂ) := by
      have h1 := hz.apply_eq_smul
      have h2 := congrArg Subtype.val h1
      rw [hg] at h2
      simpa only [LinearMap.restrict_apply, Matrix.mulVecLin_apply,
        SetLike.val_smul] using h2
    have hzne : (z : Fin d → ℂ) ≠ 0 := by
      intro h0
      exact hz.2 (Subtype.ext h0)
    have hBz : Bcᵀ *ᵥ (z : Fin d → ℂ) = 0 := by
      obtain ⟨hz1, _⟩ := Submodule.mem_inf.mp z.2
      have h1 := hz1 ⟨0, hd0⟩
      simpa using h1
    have hμroot : Polynomial.eval μ (antiPoly M) = 0 := by
      have h1 : Polynomial.aeval Mᵀ (antiPoly M)
          *ᵥ (z : Fin d → ℂ) = 0 := by
        obtain ⟨_, hz2m⟩ := Submodule.mem_inf.mp z.2
        have h2 := LinearMap.mem_ker.mp hz2m
        rwa [Matrix.mulVecLin_apply] at h2
      rw [aeval_mulVec_eigenvector hzval] at h1
      by_contra hne
      have h3 : (z : Fin d → ℂ) = 0 := by
        have h4 := congrArg
          (fun y => (Polynomial.eval μ (antiPoly M))⁻¹ • y) h1
        simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul,
          smul_zero] using h4
      exact hzne h3
    have hμge : (1:ℝ) ≤ ‖μ‖ := not_lt.mp (antiPoly_root_ge hμroot)
    exact hzne (hstab μ (z : Fin d → ℂ) hμge hzval hBz)
  -- surjectivity of the antistable factor on the annihilator
  have hWmap : ∀ ψ ∈ W,
      ((Polynomial.aeval Mᵀ (antiPoly M)).mulVecLin) ψ ∈ W := by
    intro ψ hψ
    rw [Matrix.mulVecLin_apply]
    exact hWaeval ψ hψ
  set gW : W →ₗ[ℂ] W :=
    ((Polynomial.aeval Mᵀ (antiPoly M)).mulVecLin).restrict hWmap
    with hgW
  have hgWinj : Function.Injective gW := by
    intro a b hab
    have h1 : Polynomial.aeval Mᵀ (antiPoly M) *ᵥ ((a : Fin d → ℂ)
        - (b : Fin d → ℂ)) = 0 := by
      have h2 := congrArg Subtype.val hab
      simp only [hgW, LinearMap.restrict_apply,
        Matrix.mulVecLin_apply] at h2
      rw [Matrix.mulVec_sub, h2, sub_self]
    have h3 : (a : Fin d → ℂ) - (b : Fin d → ℂ) = 0 :=
      hinj _ (W.sub_mem a.2 b.2) h1
    exact Subtype.ext (sub_eq_zero.mp h3)
  have hgWsurj : Function.Surjective gW :=
    LinearMap.injective_iff_surjective.mp hgWinj
  obtain ⟨ψ, hψeq⟩ := hgWsurj ⟨φ, hφW⟩
  have hψval : Polynomial.aeval Mᵀ (antiPoly M)
      *ᵥ (ψ : Fin d → ℂ) = φ := by
    have h1 := congrArg Subtype.val hψeq
    simpa [hgW, LinearMap.restrict_apply, Matrix.mulVecLin_apply]
      using h1
  -- the pairing kills the functional on the antistable range
  have hpair : (Pa *ᵥ x) ⬝ᵥ φ = 0 := by
    rw [← hψval, ← aeval_transpose,
      ← mulVec_dot (Polynomial.aeval M (antiPoly M)) (Pa *ᵥ x)
        (ψ : Fin d → ℂ)]
    rw [Matrix.mulVec_mulVec, hPaAnti, Matrix.zero_mulVec,
      zero_dotProduct]
  rw [hfeq] at hfx
  exact hfx hpair

end LinearSystems
