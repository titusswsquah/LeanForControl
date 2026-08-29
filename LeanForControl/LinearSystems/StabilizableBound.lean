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
  
end LinearSystems
