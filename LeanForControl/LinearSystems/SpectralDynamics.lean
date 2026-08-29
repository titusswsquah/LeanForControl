import LeanForControl.LinearSystems.Complexify
import LeanForControl.LinearSystems.PolynomialSampling
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RingTheory.Polynomial.Pochhammer
import Architect

/-!
# Spectral dynamics: growth of matrix powers along generalized eigenspaces

Infrastructure for the "spectral dynamics" facts of the `costogo` papers
(`fact:poly-growth`, `fact:no-decay`, and the quantitative Gramian bound
`eq:gramian`), phrased without Jordan normal form. The engine is an *adapted
basis*: over `ℂ` the generalized eigenspaces of an endomorphism decompose the
space (`Module.End.iSup_maxGenEigenspace_eq_top` +
`Module.End.independent_maxGenEigenspace`), and collecting bases of the
summands yields a basis whose coordinate functionals see exactly one
generalized eigenspace each. On a generalized eigenspace the binomial
expansion `f = μ•1 + (f - μ•1)` truncates at order `n`, so each coordinate of
`f^k v` is `μ^k` times a polynomial in `k` of degree `< n`
(`coord_pow_apply`). Combining with the sampled polynomial lower bound
(`sum_sq_norm_eval_ge`) yields the growth facts in
`LinearSystems.SpectralGrowth` (companion file).
-/

namespace LinearSystems

open Module Finset

variable {n : ℕ}

section AdaptedBasis

variable (f : Module.End ℂ (Fin n → ℂ))

/-- The generalized eigenspaces of an endomorphism of `ℂⁿ` decompose the
space internally. -/
lemma isInternal_maxGenEigenspace :
    DirectSum.IsInternal (fun μ : ℂ => f.maxGenEigenspace μ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    f.independent_maxGenEigenspace f.iSup_maxGenEigenspace_eq_top

/-- Index type of the adapted basis: one block of coordinates per
(generalized) eigenvalue. Only finitely many fibers are nonempty. -/
abbrev AdaptedIndex :=
  Σ μ : ℂ, Fin (finrank ℂ (f.maxGenEigenspace μ))

/-- A basis of `ℂⁿ` adapted to the generalized eigenspace decomposition:
each basis vector lies in the generalized eigenspace of its label. -/
noncomputable def adaptedBasis : Basis (AdaptedIndex f) ℂ (Fin n → ℂ) :=
  (isInternal_maxGenEigenspace f).collectedBasis
    (fun μ => Module.finBasis ℂ (f.maxGenEigenspace μ))

/-- The index type of the adapted basis is finite. -/
noncomputable instance : Fintype (AdaptedIndex f) :=
  FiniteDimensional.fintypeBasisIndex (adaptedBasis f)

lemma adaptedBasis_mem (j : AdaptedIndex f) :
    adaptedBasis f j ∈ f.maxGenEigenspace j.1 :=
  (isInternal_maxGenEigenspace f).collectedBasis_mem _ j

/-- A coordinate functional of the adapted basis annihilates every
generalized eigenspace other than its own. -/
lemma adaptedBasis_repr_eq_zero {μ : ℂ} {x : Fin n → ℂ}
    (hx : x ∈ f.maxGenEigenspace μ) (j : AdaptedIndex f) (hj : j.1 ≠ μ) :
    (adaptedBasis f).repr x j = 0 :=
  (isInternal_maxGenEigenspace f).collectedBasis_repr_of_mem_ne _
    (Ne.symm hj) hx

/-- Every adapted-basis label is an eigenvalue, hence in the spectrum. -/
lemma adaptedBasis_label_mem_spectrum (j : AdaptedIndex f) :
    j.1 ∈ spectrum ℂ f := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  have hmem := adaptedBasis_mem f j
  have hne := (adaptedBasis f).ne_zero j
  rw [Module.End.mem_maxGenEigenspace] at hmem
  obtain ⟨l, hl⟩ := hmem
  have hl0 : l ≠ 0 := by
    intro h
    rw [h, pow_zero, Module.End.one_apply] at hl
    exact hne hl
  refine Module.End.hasEigenvalue_of_hasGenEigenvalue (k := l) ?_
  intro hbot
  have hmem' : adaptedBasis f j ∈ f.genEigenspace j.1 l :=
    Module.End.mem_genEigenspace_nat.mpr (LinearMap.mem_ker.mpr hl)
  rw [hbot] at hmem'
  exact hne (by simpa using hmem')

/-- On a generalized eigenspace, `(f - μ•1)^n` vanishes. -/
lemma pow_sub_smul_eq_zero_of_mem {μ : ℂ} {x : Fin n → ℂ}
    (hx : x ∈ f.maxGenEigenspace μ) :
    ((f - μ • 1) ^ n) x = 0 := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank] at hx
  have hn : finrank ℂ (Fin n → ℂ) = n := by simp
  rw [hn, Module.End.mem_genEigenspace_nat, LinearMap.mem_ker] at hx
  exact hx

/-- Generalized eigenspaces are invariant under powers of `f`. -/
lemma pow_apply_mem {μ : ℂ} {x : Fin n → ℂ} (hx : x ∈ f.maxGenEigenspace μ)
    (k : ℕ) : (f ^ k) x ∈ f.maxGenEigenspace μ :=
  Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right k) μ hx

/-- Generalized eigenspaces are invariant under powers of `f - c•1` for any
`c`. -/
lemma pow_sub_smul_apply_mem {μ c : ℂ} {x : Fin n → ℂ}
    (hx : x ∈ f.maxGenEigenspace μ) (r : ℕ) :
    ((f - c • 1) ^ r) x ∈ f.maxGenEigenspace μ := by
  have hcomm : Commute f ((f - c • 1) ^ r) :=
    ((Commute.refl f).sub_right ((Commute.one_right f).smul_right c)).pow_right r
  exact Module.End.mapsTo_maxGenEigenspace_of_comm hcomm μ hx

/-- **Truncated binomial expansion** on a generalized eigenspace: for
`x ∈ E_μ`,
`f^k x = ∑_{r<n} C(k,r) μ^(k-r) (f - μ•1)^r x`. Terms `r ≥ n` die by
nilpotency, terms `r > k` by `C(k,r) = 0`. -/
lemma pow_apply_eq_sum_of_mem {μ : ℂ} {x : Fin n → ℂ}
    (hx : x ∈ f.maxGenEigenspace μ) (k : ℕ) :
    (f ^ k) x = ∑ r ∈ range n,
      ((k.choose r : ℂ) * μ ^ (k - r)) • (((f - μ • 1) ^ r) x) := by
  have hcomm : Commute (f - μ • 1) (μ • (1 : Module.End ℂ (Fin n → ℂ))) :=
    (Commute.one_right (f - μ • 1)).smul_right μ
  have hf : f = (f - μ • 1) + μ • 1 := by abel
  have hexp := hcomm.add_pow k
  rw [← hf] at hexp
  -- Evaluate the operator identity at `x`.
  have happ : (f ^ k) x
      = ∑ m ∈ range (k + 1),
          (((f - μ • 1) ^ m) * ((μ • 1) ^ (k - m)) *
            (k.choose m : Module.End ℂ (Fin n → ℂ))) x := by
    rw [hexp, LinearMap.sum_apply]
  -- Simplify each summand: `(μ•1)^(k-m) = μ^(k-m) • 1` and the Nat cast acts
  -- as scalar multiplication.
  have hterm : ∀ m : ℕ,
      (((f - μ • 1) ^ m) * ((μ • 1) ^ (k - m)) * (k.choose m : Module.End ℂ (Fin n → ℂ))) x
        = ((k.choose m : ℂ) * μ ^ (k - m)) • (((f - μ • 1) ^ m) x) := by
    intro m
    have h1 : ((μ • 1 : Module.End ℂ (Fin n → ℂ)) ^ (k - m)) = μ ^ (k - m) • 1 := by
      rw [smul_pow, one_pow]
    have h2 : ((k.choose m : Module.End ℂ (Fin n → ℂ))) x = (k.choose m : ℂ) • x := by
      rw [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    rw [Module.End.mul_apply, Module.End.mul_apply, h2, map_smul, h1]
    simp only [LinearMap.smul_apply, Module.End.one_apply, map_smul]
    rw [smul_smul, mul_comm]
  simp only [hterm] at happ
  rw [happ]
  -- Convert the range `k+1` sum into a range `n` sum.
  rcases le_or_gt (k + 1) n with hkn | hkn
  · -- `range (k+1) ⊆ range n`; extra terms have `C(k,r) = 0`.
    refine Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hkn))
      fun r _ hr => ?_
    rw [Finset.mem_range, not_lt] at hr
    have : k.choose r = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [this]
    simp
  · -- `range n ⊆ range (k+1)`; extra terms have `(f-μ•1)^r x = 0`.
    refine (Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
      fun r _ hr => ?_).symm
    rw [Finset.mem_range, not_lt] at hr
    have hzero : ((f - μ • 1) ^ r) x = 0 := by
      have : (f - μ • 1) ^ r = (f - μ • 1) ^ (r - n) * (f - μ • 1) ^ n := by
        rw [← pow_add]
        congr 1
        omega
      rw [this, Module.End.mul_apply, pow_sub_smul_eq_zero_of_mem f hx, map_zero]
    rw [hzero, smul_zero]

/-- **Scalarization**: the `j`-th adapted coordinate of `f^k v` is the
binomial combination of the coordinates of `(f - μ_j•1)^r v`, `r < n`, with
`μ_j` the label of `j`. This is the identity that turns matrix-power growth
questions into scalar polynomial ones. -/
lemma coord_pow_apply (j : AdaptedIndex f) (v : Fin n → ℂ) (k : ℕ) :
    (adaptedBasis f).repr ((f ^ k) v) j
      = ∑ r ∈ range n, (k.choose r : ℂ) * j.1 ^ (k - r) *
          (adaptedBasis f).repr (((f - j.1 • 1) ^ r) v) j := by
  set b := adaptedBasis f with hb
  -- Both sides are linear functionals in `v`; compare them on the basis.
  have key : (b.coord j) ∘ₗ (f ^ k : Module.End ℂ (Fin n → ℂ))
      = ∑ r ∈ range n, ((k.choose r : ℂ) * j.1 ^ (k - r)) •
          ((b.coord j) ∘ₗ ((f - j.1 • 1) ^ r : Module.End ℂ (Fin n → ℂ))) := by
    refine b.ext fun m => ?_
    rcases eq_or_ne m.1 j.1 with hm | hm
    · -- Same eigenvalue block: use the truncated binomial expansion.
      have hmem : b m ∈ f.maxGenEigenspace j.1 := hm ▸ adaptedBasis_mem f m
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [pow_apply_eq_sum_of_mem f hmem k, map_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [map_smul, smul_eq_mul]
    · -- Different block: both sides vanish coordinate-wise.
      have hmem := adaptedBasis_mem f m
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul]
      have h1 : b.coord j ((f ^ k) (b m)) = 0 := by
        rw [Basis.coord_apply]
        exact adaptedBasis_repr_eq_zero f (pow_apply_mem f hmem k) j hm.symm
      have h2 : ∀ r ∈ range n,
          (k.choose r : ℂ) * j.1 ^ (k - r) * b.coord j (((f - j.1 • 1) ^ r) (b m)) = 0 := by
        intro r _
        have := adaptedBasis_repr_eq_zero f
          (pow_sub_smul_apply_mem f (c := j.1) hmem r) j hm.symm
        rw [Basis.coord_apply, this, mul_zero]
      rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, smul_zero]
  have := LinearMap.congr_fun key v
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Basis.coord_apply] using this

end AdaptedBasis

section Growth

open Polynomial

/-- `descPochhammer` evaluated at a natural number is the descending
factorial. -/
lemma descPochhammer_eval_natCast (r k : ℕ) :
    (descPochhammer ℂ r).eval (k : ℂ) = (k.descFactorial r : ℂ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [descPochhammer_succ_eval, ih, Nat.descFactorial_succ]
    rcases le_or_gt r k with h | h
    · rw [Nat.cast_mul, Nat.cast_sub h]
      ring
    · have h0 : k.descFactorial r = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr h
      rw [h0]
      push_cast
      ring

variable (f : Module.End ℂ (Fin n → ℂ))

/-- The scalar polynomial behind the `j`-th adapted coordinate of `f^k v`:
`coordPoly f j v` satisfies
`(adaptedBasis f).repr (f^k v) j = μ_j^k · (coordPoly f j v).eval k`
whenever `μ_j ≠ 0` (`repr_pow_apply_eq_pow_mul_eval`). -/
noncomputable def coordPoly (j : AdaptedIndex f) (v : Fin n → ℂ) :
    Polynomial ℂ :=
  ∑ r ∈ range n,
    Polynomial.C ((adaptedBasis f).repr (((f - j.1 • 1) ^ r) v) j *
      (j.1⁻¹) ^ r * ((r.factorial : ℂ))⁻¹) * descPochhammer ℂ r

lemma coordPoly_natDegree_le (j : AdaptedIndex f) (v : Fin n → ℂ) :
    (coordPoly f j v).natDegree ≤ n - 1 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun r hr => ?_
  rw [Finset.mem_range] at hr
  calc (Polynomial.C ((adaptedBasis f).repr (((f - j.1 • 1) ^ r) v) j *
        (j.1⁻¹) ^ r * ((r.factorial : ℂ))⁻¹) * descPochhammer ℂ r).natDegree
      ≤ (Polynomial.C ((adaptedBasis f).repr (((f - j.1 • 1) ^ r) v) j *
        (j.1⁻¹) ^ r * ((r.factorial : ℂ))⁻¹)).natDegree +
        (descPochhammer ℂ r).natDegree := Polynomial.natDegree_mul_le
  _ ≤ 0 + r := by
      gcongr
      · exact le_of_eq (Polynomial.natDegree_C _)
      · exact le_of_eq (descPochhammer_natDegree (R := ℂ) r)
  _ ≤ n - 1 := by omega

lemma coordPoly_eval_natCast (j : AdaptedIndex f) (v : Fin n → ℂ) (k : ℕ) :
    (coordPoly f j v).eval (k : ℂ)
      = ∑ r ∈ range n, (k.choose r : ℂ) * (j.1⁻¹) ^ r *
          (adaptedBasis f).repr (((f - j.1 • 1) ^ r) v) j := by
  rw [coordPoly, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, descPochhammer_eval_natCast]
  have hfac : ((r.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast r.factorial_ne_zero
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp

lemma coordPoly_eval_zero (j : AdaptedIndex f) (v : Fin n → ℂ) :
    (coordPoly f j v).eval 0 = (adaptedBasis f).repr v j := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      have hle : finrank ℂ (f.maxGenEigenspace j.1) ≤ finrank ℂ (Fin n → ℂ) :=
        Submodule.finrank_le _
      have hn0 : finrank ℂ (Fin n → ℂ) = 0 := by rw [h]; simp
      have hlt := j.2.isLt
      omega
    · exact h
  rw [coordPoly, Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro r _ hr
    rw [Polynomial.eval_mul, descPochhammer_ne_zero_eval_zero (R := ℂ) hr, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hn) h

/-- The scalarization identity in polynomial form: for a nonzero label,
the `j`-th coordinate of `f^k v` is `μ_j^k` times a polynomial in `k` of
degree `< n`. -/
lemma repr_pow_apply_eq_pow_mul_eval (j : AdaptedIndex f) (hj : j.1 ≠ 0)
    (v : Fin n → ℂ) (k : ℕ) :
    (adaptedBasis f).repr ((f ^ k) v) j
      = j.1 ^ k * (coordPoly f j v).eval (k : ℂ) := by
  rw [coord_pow_apply, coordPoly_eval_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rcases le_or_gt r k with h | h
  · have hpow : j.1 ^ (k - r) = j.1 ^ k * (j.1⁻¹) ^ r := by
      rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero r hj), ← pow_add]
      congr 1
      omega
    rw [hpow]
    ring
  · have h0 : k.choose r = 0 := Nat.choose_eq_zero_of_lt h
    rw [h0]
    push_cast
    ring

end Growth

end LinearSystems
