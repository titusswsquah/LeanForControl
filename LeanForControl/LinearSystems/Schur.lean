import LeanForControl.LinearSystems.Complexify
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Architect

/-!
# Schur stability

A real square matrix `A` is *Schur stable* when every complex eigenvalue lies
strictly inside the unit disc. This is the discrete-time stability notion the
`Estimation` track is built on: the closed-loop filter matrices produced by
the Riccati/LQR machinery are Schur, and Schur stability is exactly geometric
decay of the powers `A ^ k`.

Main results:

* `LinearSystems.IsSchurStable` — the defining predicate, via `spectrum ℂ`.
* `LinearSystems.isSchurStable_iff_spectralRadius_lt_one` — the
  `spectralRadius` form.
* `LinearSystems.IsSchurStable.exists_pow_norm_le` — Schur stability implies
  `‖A ^ k‖ ≤ c * ρ ^ k` with `ρ < 1` (via Gelfand's formula, in the `L∞`
  operator norm).
* `LinearSystems.isSchurStable_of_pow_norm_le` — the converse, by an
  eigenvector argument.
* `LinearSystems.isSchurStable_iff_exists_pow_norm_le` — the packaged iff.

Norm conventions: matrix norms in this file are the `L∞` operator norm
(`Matrix.Norms.Operator`), vector norms the sup norm; by finite-dimensional
norm equivalence the *existence* statements are norm-independent.
-/

namespace LinearSystems

open Matrix Filter

open scoped Matrix.Norms.Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real square matrix is **Schur stable** if every eigenvalue of its
complexification lies strictly inside the unit disc of `ℂ`. -/
@[blueprint "def:isSchurStable"
  (statement := /-- A matrix $A \in \mathbb{R}^{n \times n}$ is \emph{Schur
    stable} if every eigenvalue $\mu \in \mathbb{C}$ of $A$ satisfies
    $|\mu| < 1$. -/)]
def IsSchurStable (A : Matrix ι ι ℝ) : Prop :=
  ∀ μ ∈ spectrum ℂ (complexify A), ‖μ‖ < 1

/-- With an empty index type the matrix algebra is trivial and the spectrum
is empty. -/
private lemma spectrum_complexify_eq_empty (A : Matrix ι ι ℝ)
    (hn : IsEmpty ι) : spectrum ℂ (complexify A) = ∅ := by
  haveI : Subsingleton (Matrix ι ι ℂ) :=
    ⟨fun M N => by ext i j; exact (hn.false i).elim⟩
  exact spectrum.of_subsingleton _

/-- Schur stability is equivalent to `spectralRadius ℂ A < 1`. -/
@[blueprint "lem:isSchurStable-iff-spectralRadius"
  (statement := /-- $A$ is Schur stable if and only if its spectral radius
    satisfies $\rho(A) < 1$. -/)
  (proof := /-- The spectral radius is the supremum of $|\mu|$ over the
    spectrum, which over $\mathbb{C}$ is nonempty and compact, so the
    supremum is attained; the two conditions coincide. -/)]
theorem isSchurStable_iff_spectralRadius_lt_one (A : Matrix ι ι ℝ) :
    IsSchurStable A ↔ spectralRadius ℂ (complexify A) < 1 := by
  rcases isEmpty_or_nonempty ι with hn | hn
  · constructor
    · intro _
      rw [spectralRadius, spectrum_complexify_eq_empty A hn]
      simp
    · intro _ μ hμ
      rw [spectrum_complexify_eq_empty A hn] at hμ
      exact absurd hμ (Set.notMem_empty μ)
  · constructor
    · intro hA
      haveI : Nontrivial (Matrix ι ι ℂ) := by
        refine ⟨0, 1, fun h => ?_⟩
        obtain ⟨i⟩ := hn
        have := congrFun (congrFun h i) i
        simp at this
      have h1 : ∀ z ∈ spectrum ℂ (complexify A), ‖z‖₊ < 1 := fun z hz => by
        have := hA z hz
        simpa [← NNReal.coe_lt_coe] using this
      simpa using spectrum.spectralRadius_lt_of_forall_lt (complexify A) h1
    · intro hrad μ hμ
      have hle : (‖μ‖₊ : ENNReal) ≤ spectralRadius ℂ (complexify A) :=
        le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (complexify A)) => (‖k‖₊ : ENNReal)) μ hμ
      have hlt := lt_of_le_of_lt hle hrad
      have h1 : ‖μ‖₊ < 1 := ENNReal.coe_lt_one_iff.mp hlt
      exact_mod_cast h1

/-- **Schur stability implies geometric decay of powers.** If every eigenvalue
of `A` lies strictly inside the unit disc, then `‖A ^ k‖ ≤ c * ρ ^ k` for some
`c > 0` and `ρ ∈ (0, 1)`, in the `L∞` operator norm. The proof goes through
the Gelfand formula for the spectral radius. -/
@[blueprint "thm:schur-pow-decay"
  (statement := /-- If $A$ is Schur stable, there exist $c > 0$ and
    $\rho \in (0, 1)$ with $\|A^{k}\| \le c\,\rho^{k}$ for every $k \ge 0$. -/)
  (proof := /-- Pick $\rho$ with $\rho(A) < \rho < 1$. By the Gelfand
    formula $\|A^{k}\|^{1/k} \to \rho(A)$, so $\|A^{k}\| \le \rho^{k}$ for
    all large $k$; enlarging the constant covers the finite prefix. -/)]
theorem IsSchurStable.exists_pow_norm_le {A : Matrix ι ι ℝ}
    (hA : IsSchurStable A) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k : ℕ, ‖A ^ k‖ ≤ c * ρ ^ k := by
  have hrad : spectralRadius ℂ (complexify A) < 1 :=
    (isSchurStable_iff_spectralRadius_lt_one A).mp hA
  obtain ⟨r, hr₁, hr₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hrad
  have hr0 : 0 < r := by
    rcases eq_or_lt_of_le (zero_le r) with h | h
    · exact absurd (h ▸ hr₁) (by simp)
    · exact h
  have hrlt1 : (r : ℝ) < 1 := by exact_mod_cast hr₂
  -- Gelfand: the `limsup` of `‖Aᵏ‖^(1/k)` is at most the spectral radius,
  -- hence eventually below `r`.
  have hev : ∀ᶠ k : ℕ in atTop,
      (‖complexify A ^ k‖₊ : ENNReal) ^ (1 / (k : ℝ)) < (r : ENNReal) :=
    Filter.eventually_lt_of_limsup_lt
      (lt_of_le_of_lt
        (spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius (complexify A)) hr₁)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  -- Convert the eventual root bound into `‖A ^ k‖ ≤ r ^ k` for `k ≥ K + 1`.
  have key : ∀ k : ℕ, K + 1 ≤ k → ‖A ^ k‖ ≤ (r : ℝ) ^ k := by
    intro k hk
    have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 K) hk
    have hknz : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 := hK k (le_trans (Nat.le_succ K) hk)
    have h2 : ((‖complexify A ^ k‖₊ : ENNReal) ^ (1 / (k : ℝ))) ^ (k : ℝ)
        ≤ ((r : ENNReal)) ^ (k : ℝ) :=
      ENNReal.rpow_le_rpow h1.le (Nat.cast_nonneg k)
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hknz, ENNReal.rpow_one,
      ENNReal.rpow_natCast] at h2
    have h3 : ‖complexify A ^ k‖₊ ≤ r ^ k := by
      have := (ENNReal.coe_le_coe (r := ‖complexify A ^ k‖₊) (q := r ^ k)).mpr
      exact_mod_cast h2
    have h4 : ‖A ^ k‖₊ ≤ r ^ k := by
      rwa [← complexify_pow, linfty_opNNNorm_complexify] at h3
    calc ‖A ^ k‖ = ((‖A ^ k‖₊ : ℝ)) := rfl
    _ ≤ ((r ^ k : NNReal) : ℝ) := by exact_mod_cast h4
    _ = (r : ℝ) ^ k := by push_cast; ring
  -- Absorb the finite prefix into the constant.
  set ρ : ℝ := (r : ℝ) with hρ
  have hρ0 : 0 < ρ := hr0
  refine ⟨1 + ∑ j ∈ Finset.range (K + 1), ‖A ^ j‖ / ρ ^ j, ρ, by positivity,
    hρ0, hrlt1, fun k => ?_⟩
  rcases lt_or_ge k (K + 1) with hk | hk
  · -- `k` in the finite prefix: its own term of the sum dominates.
    have hterm : ‖A ^ k‖ / ρ ^ k ≤ ∑ j ∈ Finset.range (K + 1), ‖A ^ j‖ / ρ ^ j :=
      Finset.single_le_sum (f := fun j => ‖A ^ j‖ / ρ ^ j)
        (fun j _ => by positivity) (Finset.mem_range.mpr hk)
    have hpow : (0 : ℝ) < ρ ^ k := by positivity
    calc ‖A ^ k‖ = ‖A ^ k‖ / ρ ^ k * ρ ^ k := by field_simp
    _ ≤ (1 + ∑ j ∈ Finset.range (K + 1), ‖A ^ j‖ / ρ ^ j) * ρ ^ k := by
        have h1 : ‖A ^ k‖ / ρ ^ k
            ≤ 1 + ∑ j ∈ Finset.range (K + 1), ‖A ^ j‖ / ρ ^ j :=
          le_trans hterm (by linarith)
        exact mul_le_mul_of_nonneg_right h1 hpow.le
  · -- `k` beyond the prefix: the Gelfand bound applies and the constant is `≥ 1`.
    have h1 : ‖A ^ k‖ ≤ ρ ^ k := key k hk
    have h2 : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (K + 1), ‖A ^ j‖ / ρ ^ j := by
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (K + 1), ‖A ^ j‖ / ρ ^ j :=
        Finset.sum_nonneg fun j _ => by positivity
      linarith
    calc ‖A ^ k‖ ≤ ρ ^ k := h1
    _ = 1 * ρ ^ k := (one_mul _).symm
    _ ≤ (1 + ∑ j ∈ Finset.range (K + 1), ‖A ^ j‖ / ρ ^ j) * ρ ^ k := by
        exact mul_le_mul_of_nonneg_right h2 (by positivity)

/-- **Geometric decay of powers implies Schur stability.** The converse
direction, by the eigenvector argument: an eigenvalue on or outside the unit
circle would make `‖A ^ k *ᵥ v‖` non-decaying. -/
@[blueprint "thm:schur-of-pow-decay"
  (statement := /-- If $\|A^{k}\| \le c\,\rho^{k}$ for all $k \ge 0$ with
    $0 \le \rho < 1$, then $A$ is Schur stable. -/)
  (proof := /-- Let $A v = \mu v$ with $v \ne 0$. Then
    $|\mu|^{k}\,\|v\| = \|A^{k} v\| \le c\,\rho^{k}\,\|v\|$; if $|\mu| \ge 1$
    the left side stays at least $\|v\|$ while the right side vanishes as
    $k \to \infty$, a contradiction. -/)]
theorem isSchurStable_of_pow_norm_le {A : Matrix ι ι ℝ} {c ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (h : ∀ k : ℕ, ‖A ^ k‖ ≤ c * ρ ^ k) :
    IsSchurStable A := by
  intro μ hμ
  by_contra hge
  push Not at hge
  -- Extract an eigenvector for `μ`.
  have hspec : μ ∈ spectrum ℂ (Matrix.toLin' (complexify A)) := by
    rw [Matrix.spectrum_toLin']
    exact hμ
  have heig : Module.End.HasEigenvalue (Matrix.toLin' (complexify A)) μ :=
    Module.End.hasEigenvalue_iff_mem_spectrum.mpr hspec
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hAv : complexify A *ᵥ v = μ • v := by
    have := hv.apply_eq_smul
    rwa [Matrix.toLin'_apply] at this
  have hpow : ∀ k : ℕ, complexify A ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, ih,
        smul_smul]
      congr 1
      ring
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv.2
  -- The eigenvalue bound `‖μ‖ ^ k ≤ c * ρ ^ k`.
  have hμk : ∀ k : ℕ, ‖μ‖ ^ k ≤ c * ρ ^ k := by
    intro k
    have h1 : ‖μ‖ ^ k * ‖v‖ = ‖complexify A ^ k *ᵥ v‖ := by
      rw [hpow, norm_smul, norm_pow]
    have h2 : ‖complexify A ^ k *ᵥ v‖ ≤ ‖complexify A ^ k‖ * ‖v‖ :=
      Matrix.linfty_opNorm_mulVec _ _
    have h3 : ‖complexify A ^ k‖ = ‖A ^ k‖ := by
      rw [← complexify_pow, linfty_opNorm_complexify]
    have h4 : ‖μ‖ ^ k * ‖v‖ ≤ c * ρ ^ k * ‖v‖ := by
      rw [h1]
      exact le_trans h2 (by rw [h3]; exact mul_le_mul_of_nonneg_right (h k) hvnorm.le)
    exact le_of_mul_le_mul_right h4 hvnorm
  -- But `1 ≤ ‖μ‖ ^ k` while `c * ρ ^ k → 0`.
  have h1k : ∀ k : ℕ, (1 : ℝ) ≤ c * ρ ^ k := fun k =>
    le_trans (one_le_pow₀ hge) (hμk k)
  have htend : Tendsto (fun k : ℕ => c * ρ ^ k) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1).const_mul c
  have hev : ∀ᶠ k : ℕ in atTop, c * ρ ^ k < 1 :=
    htend.eventually_lt_const one_pos
  obtain ⟨k, hk⟩ := hev.exists
  exact absurd (h1k k) (not_le.mpr hk)

/-- **Schur stability iff geometric decay of powers**, packaged. -/
@[blueprint "thm:isSchurStable-iff-pow-decay"
  (statement := /-- $A$ is Schur stable if and only if there exist $c > 0$
    and $\rho \in (0, 1)$ with $\|A^{k}\| \le c\,\rho^{k}$ for all
    $k \ge 0$. -/)
  (proof := /-- Combine \cref{thm:schur-pow-decay} and
    \cref{thm:schur-of-pow-decay}. -/)]
theorem isSchurStable_iff_exists_pow_norm_le (A : Matrix ι ι ℝ) :
    IsSchurStable A
      ↔ ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k : ℕ, ‖A ^ k‖ ≤ c * ρ ^ k := by
  constructor
  · exact IsSchurStable.exists_pow_norm_le
  · rintro ⟨c, ρ, _, hρ0, hρ1, h⟩
    exact isSchurStable_of_pow_norm_le hρ0.le hρ1 h

/-- Powers of a Schur-stable matrix send any vector to zero geometrically:
`‖A ^ k *ᵥ x‖ ≤ c * ρ ^ k * ‖x‖`. -/
theorem IsSchurStable.exists_pow_mulVec_le {A : Matrix ι ι ℝ}
    (hA : IsSchurStable A) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (k : ℕ) (x : ι → ℝ), ‖A ^ k *ᵥ x‖ ≤ c * ρ ^ k * ‖x‖ := by
  obtain ⟨c, ρ, hc, hρ0, hρ1, h⟩ := hA.exists_pow_norm_le
  refine ⟨c, ρ, hc, hρ0, hρ1, fun k x => ?_⟩
  calc ‖A ^ k *ᵥ x‖ ≤ ‖A ^ k‖ * ‖x‖ := Matrix.linfty_opNorm_mulVec _ _
  _ ≤ c * ρ ^ k * ‖x‖ := mul_le_mul_of_nonneg_right (h k) (norm_nonneg x)

/-- Schur stability is invariant under transposition (the spectrum is). -/
lemma IsSchurStable.transpose {A : Matrix ι ι ℝ}
    (hA : IsSchurStable A) : IsSchurStable Aᵀ := by
  intro μ hμ
  refine hA μ ?_
  rcases isEmpty_or_nonempty ι with hn | hn
  · exfalso
    rw [spectrum_complexify_eq_empty Aᵀ hn] at hμ
    exact absurd hμ (Set.notMem_empty μ)
  · rw [Matrix.mem_spectrum_iff_isRoot_charpoly] at hμ ⊢
    rwa [show complexify Aᵀ = (complexify A)ᵀ from rfl,
      Matrix.charpoly_transpose] at hμ

lemma isSchurStable_transpose_iff {A : Matrix ι ι ℝ} :
    IsSchurStable Aᵀ ↔ IsSchurStable A :=
  ⟨fun h => by simpa using h.transpose, IsSchurStable.transpose⟩

/-- **Geometric decay for complex matrices** with spectrum inside the
open unit disc (the complex-matrix core of the Gelfand argument). -/
theorem exists_pow_norm_le_of_spectrum_lt_one {M : Matrix ι ι ℂ}
    (hM : ∀ μ ∈ spectrum ℂ M, ‖μ‖ < 1) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ k : ℕ, ‖M ^ k‖ ≤ c * ρ ^ k := by
  have hrad : spectralRadius ℂ M < 1 := by
    rcases isEmpty_or_nonempty ι with hn | hn
    · haveI : Subsingleton (Matrix ι ι ℂ) :=
        ⟨fun P Q => by ext i j; exact (hn.false i).elim⟩
      rw [spectralRadius, spectrum.of_subsingleton (a := M)]
      simp
    · haveI : Nontrivial (Matrix ι ι ℂ) := by
        refine ⟨0, 1, fun h => ?_⟩
        obtain ⟨i⟩ := hn
        have := congrFun (congrFun h i) i
        simp at this
      have h1 : ∀ z ∈ spectrum ℂ M, ‖z‖₊ < 1 := fun z hz => by
        have := hM z hz
        simpa [← NNReal.coe_lt_coe] using this
      simpa using spectrum.spectralRadius_lt_of_forall_lt M h1
  obtain ⟨r, hr₁, hr₂⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hrad
  have hr0 : 0 < r := by
    rcases eq_or_lt_of_le (zero_le r) with h | h
    · exact absurd (h ▸ hr₁) (by simp)
    · exact h
  have hrlt1 : (r : ℝ) < 1 := by exact_mod_cast hr₂
  have hev : ∀ᶠ k : ℕ in atTop,
      (‖M ^ k‖₊ : ENNReal) ^ (1 / (k : ℝ)) < (r : ENNReal) :=
    Filter.eventually_lt_of_limsup_lt
      (lt_of_le_of_lt
        (spectrum.limsup_pow_nnnorm_pow_one_div_le_spectralRadius M) hr₁)
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  have key : ∀ k : ℕ, K + 1 ≤ k → ‖M ^ k‖ ≤ (r : ℝ) ^ k := by
    intro k hk
    have hknz : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have h1 := hK k (le_trans (Nat.le_succ K) hk)
    have h2 : ((‖M ^ k‖₊ : ENNReal) ^ (1 / (k : ℝ))) ^ (k : ℝ)
        ≤ ((r : ENNReal)) ^ (k : ℝ) :=
      ENNReal.rpow_le_rpow h1.le (Nat.cast_nonneg k)
    rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hknz,
      ENNReal.rpow_one, ENNReal.rpow_natCast] at h2
    have h3 : ‖M ^ k‖₊ ≤ r ^ k := by exact_mod_cast h2
    calc ‖M ^ k‖ = ((‖M ^ k‖₊ : ℝ)) := rfl
    _ ≤ ((r ^ k : NNReal) : ℝ) := by exact_mod_cast h3
    _ = (r : ℝ) ^ k := by push_cast; ring
  set ρ : ℝ := (r : ℝ) with hρ
  have hρ0 : 0 < ρ := hr0
  refine ⟨1 + ∑ j ∈ Finset.range (K + 1), ‖M ^ j‖ / ρ ^ j, ρ,
    by positivity, hρ0, hrlt1, fun k => ?_⟩
  rcases lt_or_ge k (K + 1) with hk | hk
  · have hterm : ‖M ^ k‖ / ρ ^ k
        ≤ ∑ j ∈ Finset.range (K + 1), ‖M ^ j‖ / ρ ^ j :=
      Finset.single_le_sum (f := fun j => ‖M ^ j‖ / ρ ^ j)
        (fun j _ => by positivity) (Finset.mem_range.mpr hk)
    have hpow : (0 : ℝ) < ρ ^ k := by positivity
    calc ‖M ^ k‖ = ‖M ^ k‖ / ρ ^ k * ρ ^ k := by field_simp
    _ ≤ (1 + ∑ j ∈ Finset.range (K + 1), ‖M ^ j‖ / ρ ^ j) * ρ ^ k := by
        have h1 : ‖M ^ k‖ / ρ ^ k
            ≤ 1 + ∑ j ∈ Finset.range (K + 1), ‖M ^ j‖ / ρ ^ j :=
          le_trans hterm (by linarith)
        exact mul_le_mul_of_nonneg_right h1 hpow.le
  · have h1 : ‖M ^ k‖ ≤ ρ ^ k := key k hk
    have h2 : (1 : ℝ) ≤ 1 + ∑ j ∈ Finset.range (K + 1), ‖M ^ j‖ / ρ ^ j := by
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range (K + 1), ‖M ^ j‖ / ρ ^ j :=
        Finset.sum_nonneg fun j _ => by positivity
      linarith
    calc ‖M ^ k‖ ≤ ρ ^ k := h1
    _ = 1 * ρ ^ k := (one_mul _).symm
    _ ≤ (1 + ∑ j ∈ Finset.range (K + 1), ‖M ^ j‖ / ρ ^ j) * ρ ^ k :=
        mul_le_mul_of_nonneg_right h2 (by positivity)

end LinearSystems
