import LeanForControl.Estimation.Dare.Reduced
import Architect

/-!
# Discrete Sylvester equations with Schur factors (D4 support)

The chart-assembly of the strong solution needs two fixed points of
affine recursions `X ↦ L·X·A + d` with both factors Schur — the
loading `Λ∞` (factors `L∞`, `Aₐ⁻¹`) and the information gramian `J∞`
(factors `Aₐ⁻ᵀ`, `Aₐ⁻¹`). This file provides:

* `sylvIter` — the zero-seed iteration, whose increments are
  `L^N·d·A^N`, geometrically small;
* `sylvester_exists` — the limit exists (entrywise Cauchy by the
  geometric bound) and is the fixed point;
* `sylvester_unique` — fixed points are unique (`Δ = L^kΔA^k → 0`);
* `posSemidef_of_tendsto` — PSD passes to norm limits (used to read
  positivity off the PSD iterates).
-/

namespace Estimation
namespace Dare

open Matrix LinearSystems Filter Topology

open scoped Matrix.Norms.Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- Entry bound by the `L∞` norm (local restatement). -/
private lemma abs_entry_le_linfty' {ι' κ' : Type*} [Fintype ι']
    [Fintype κ'] (M : Matrix ι' κ' ℝ) (i : ι') (j : κ') :
    |M i j| ≤ ‖M‖ := by
  have h : ‖M i j‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine le_trans ?_ (Finset.le_sup (f := fun i' => ∑ j', ‖M i' j'‖₊)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j' => ‖M i j'‖₊)
      (fun _ _ => zero_le _) (Finset.mem_univ j)
  calc |M i j| = ‖M i j‖ := (Real.norm_eq_abs _).symm
  _ = ((‖M i j‖₊ : ℝ)) := rfl
  _ ≤ ((‖M‖₊ : ℝ)) := by exact_mod_cast h
  _ = ‖M‖ := rfl

/-- The zero-seed iteration of `X ↦ L·X·A + d`. -/
noncomputable def sylvIter (L : Matrix ι ι ℝ) (A : Matrix κ κ ℝ)
    (d : Matrix ι κ ℝ) : ℕ → Matrix ι κ ℝ
  | 0 => 0
  | N + 1 => L * sylvIter L A d N * A + d

/-- The increments are conjugated drives: `X_{N+1} − X_N = L^N·d·A^N`. -/
lemma sylvIter_succ_sub (L : Matrix ι ι ℝ) (A : Matrix κ κ ℝ)
    (d : Matrix ι κ ℝ) (N : ℕ) :
    sylvIter L A d (N + 1) - sylvIter L A d N
      = L ^ N * d * A ^ N := by
  induction N with
  | zero => simp [sylvIter]
  | succ N ih =>
    have h1 : sylvIter L A d (N + 2) - sylvIter L A d (N + 1)
        = L * (sylvIter L A d (N + 1) - sylvIter L A d N) * A := by
      show L * sylvIter L A d (N + 1) * A + d
          - (L * sylvIter L A d N * A + d) = _
      rw [Matrix.mul_sub L (sylvIter L A d (N + 1))
        (sylvIter L A d N), Matrix.sub_mul]
      abel
    rw [h1, ih]
    calc L * (L ^ N * d * A ^ N) * A
        = (L * L ^ N) * d * (A ^ N * A) := by
          simp only [Matrix.mul_assoc]
    _ = L ^ (N + 1) * d * A ^ (N + 1) := by
        rw [← pow_succ', ← pow_succ]

set_option maxHeartbeats 800000 in
/-- **Existence for the discrete Sylvester equation**: with both
factors Schur, the zero-seed iteration converges and its limit is a
fixed point of `X ↦ L·X·A + d`. -/
theorem sylvester_exists (L : Matrix ι ι ℝ) (A : Matrix κ κ ℝ)
    (d : Matrix ι κ ℝ) (hL : IsSchurStable L) (hA : IsSchurStable A) :
    ∃ X : Matrix ι κ ℝ, X = L * X * A + d
      ∧ Tendsto (fun N => ‖sylvIter L A d N - X‖) atTop (nhds 0) := by
  classical
  obtain ⟨c, ρ, hc, hρ0, hρ1, hpow⟩ := hL.exists_pow_norm_le
  obtain ⟨c', ρ', hc', hρ0', hρ1', hpow'⟩ := hA.exists_pow_norm_le
  have hρρ0 : 0 ≤ ρ * ρ' := by positivity
  have hρρ1 : ρ * ρ' < 1 := by nlinarith
  set Cg : ℝ := c * ‖d‖ * c' with hCg
  have hCg0 : 0 ≤ Cg := by positivity
  -- geometric increments
  have hinc : ∀ N, ‖sylvIter L A d (N + 1) - sylvIter L A d N‖
      ≤ Cg * (ρ * ρ') ^ N := by
    intro N
    rw [sylvIter_succ_sub]
    calc ‖L ^ N * d * A ^ N‖
        ≤ ‖L ^ N‖ * ‖d‖ * ‖A ^ N‖ := norm_triple_le _ _ _
    _ ≤ (c * ρ ^ N) * ‖d‖ * (c' * ρ' ^ N) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hpow N)
          (norm_nonneg d)) (hpow' N) (norm_nonneg _) ?_
        positivity
    _ = Cg * (ρ * ρ') ^ N := by
        rw [hCg, mul_pow]
        ring
  -- each entry is a Cauchy sequence
  have hentry_cauchy : ∀ (i : ι) (j : κ),
      CauchySeq (fun N => sylvIter L A d N i j) := by
    intro i j
    refine cauchySeq_of_le_geometric (ρ * ρ') Cg hρρ1 fun N => ?_
    rw [Real.dist_eq]
    calc |sylvIter L A d N i j - sylvIter L A d (N + 1) i j|
        = |(sylvIter L A d (N + 1) - sylvIter L A d N) i j| := by
          rw [Matrix.sub_apply, abs_sub_comm]
    _ ≤ ‖sylvIter L A d (N + 1) - sylvIter L A d N‖ :=
        abs_entry_le_linfty' _ i j
    _ ≤ Cg * (ρ * ρ') ^ N := hinc N
  choose Xf hXf using fun i j =>
    cauchySeq_tendsto_of_complete (hentry_cauchy i j)
  set X : Matrix ι κ ℝ := Matrix.of Xf with hXdef
  have hlim : Tendsto (fun N => ‖sylvIter L A d N - X‖)
      atTop (nhds 0) :=
    tendsto_norm_sub_of_entry fun i j => hXf i j
  refine ⟨X, ?_, hlim⟩
  -- the limit is a fixed point (shift + continuity)
  have hshift : Tendsto (fun N => ‖sylvIter L A d (N + 1) - X‖)
      atTop (nhds 0) := by
    have h1 : (fun N => ‖sylvIter L A d (N + 1) - X‖)
        = (fun N => ‖sylvIter L A d N - X‖) ∘ (fun N => N + 1) := rfl
    rw [h1]
    exact hlim.comp (tendsto_add_atTop_nat 1)
  have hnext : Tendsto (fun N => ‖sylvIter L A d (N + 1)
      - (L * X * A + d)‖) atTop (nhds 0) := by
    have h1 := tendsto_matadd
      (X := fun N => L * sylvIter L A d N * A) (Xl := L * X * A)
      (Y := fun _ => d) (Yl := d)
      (tendsto_matmul (X := fun N => L * sylvIter L A d N)
        (Xl := L * X) (Y := fun _ => A) (Yl := A)
        (tendsto_matmul (X := fun _ => L) (Xl := L)
          (Y := fun N => sylvIter L A d N) (Yl := X)
          (tendsto_matconst L) hlim) (tendsto_matconst A))
      (tendsto_matconst d)
    exact h1
  have hb : ∀ N, ‖X - (L * X * A + d)‖
      ≤ ‖sylvIter L A d (N + 1) - (L * X * A + d)‖
        + ‖sylvIter L A d (N + 1) - X‖ := by
    intro N
    calc ‖X - (L * X * A + d)‖
        = ‖(sylvIter L A d (N + 1) - (L * X * A + d))
            - (sylvIter L A d (N + 1) - X)‖ := by
          congr 1
          abel
    _ ≤ _ := norm_sub_le _ _
  have hsum : Tendsto (fun N =>
      ‖sylvIter L A d (N + 1) - (L * X * A + d)‖
        + ‖sylvIter L A d (N + 1) - X‖) atTop (nhds 0) := by
    have h := hnext.add hshift
    simpa using h
  have hle : ‖X - (L * X * A + d)‖ ≤ 0 :=
    ge_of_tendsto hsum (Filter.Eventually.of_forall hb)
  have h0 : X - (L * X * A + d) = 0 := by
    rw [← norm_le_zero_iff]
    exact hle
  exact sub_eq_zero.mp h0

/-- **Uniqueness for the discrete Sylvester equation**. -/
theorem sylvester_unique {L : Matrix ι ι ℝ} {A : Matrix κ κ ℝ}
    {d X X' : Matrix ι κ ℝ}
    (hL : IsSchurStable L) (hA : IsSchurStable A)
    (hX : X = L * X * A + d) (hX' : X' = L * X' * A + d) :
    X = X' := by
  have hone : X - X' = L * (X - X') * A := by
    conv_lhs => rw [hX, hX']
    rw [Matrix.mul_sub L X X', Matrix.sub_mul]
    abel
  have hdiff : ∀ k : ℕ, X - X' = L ^ k * (X - X') * A ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc X - X' = L * (X - X') * A := hone
      _ = L * (L ^ k * (X - X') * A ^ k) * A := by rw [← ih]
      _ = (L * L ^ k) * (X - X') * (A ^ k * A) := by
          simp only [Matrix.mul_assoc]
      _ = L ^ (k + 1) * (X - X') * A ^ (k + 1) := by
          rw [← pow_succ', ← pow_succ]
  obtain ⟨c, ρ, hc, hρ0, hρ1, hpow⟩ := hL.exists_pow_norm_le
  obtain ⟨c', ρ', hc', hρ0', hρ1', hpow'⟩ := hA.exists_pow_norm_le
  have hbound : ∀ k, ‖X - X'‖
      ≤ (c * ‖X - X'‖ * c') * (ρ * ρ') ^ k := by
    intro k
    calc ‖X - X'‖ = ‖L ^ k * (X - X') * A ^ k‖ := by
          rw [← hdiff k]
    _ ≤ ‖L ^ k‖ * ‖X - X'‖ * ‖A ^ k‖ := norm_triple_le _ _ _
    _ ≤ (c * ρ ^ k) * ‖X - X'‖ * (c' * ρ' ^ k) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (hpow k)
          (norm_nonneg _)) (hpow' k) (norm_nonneg _) ?_
        positivity
    _ = (c * ‖X - X'‖ * c') * (ρ * ρ') ^ k := by
        rw [mul_pow]
        ring
  have hρρ0 : 0 ≤ ρ * ρ' := by positivity
  have hρρ1 : ρ * ρ' < 1 := by nlinarith
  have hlim : Tendsto (fun k =>
      (c * ‖X - X'‖ * c') * (ρ * ρ') ^ k) atTop (nhds 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hρρ0
      hρρ1).const_mul (c * ‖X - X'‖ * c')
    simpa using h1
  have hle : ‖X - X'‖ ≤ 0 :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hbound)
  have h0 : X - X' = 0 := by
    rw [← norm_le_zero_iff]
    exact hle
  exact sub_eq_zero.mp h0

/-! ### PSD limits -/

/-- `|quadForm M x| ≤ card·‖M‖·‖x‖²` (local restatement). -/
private lemma abs_quadForm_le_card_norm' (M : Matrix ι ι ℝ)
    (x : ι → ℝ) :
    |quadForm M x| ≤ (Fintype.card ι : ℝ) * ‖M‖ * ‖x‖ ^ 2 := by
  rw [abs_le]
  refine ⟨?_, quadForm_le_card_norm M x⟩
  have h := quadForm_le_card_norm (-M) x
  have hneg : quadForm (-M) x = -quadForm M x := by
    simp [quadForm, Matrix.neg_mulVec]
  rw [hneg, norm_neg] at h
  linarith

/-- PSD passes to norm limits. -/
lemma posSemidef_of_tendsto {M : ℕ → Matrix ι ι ℝ}
    {Minf : Matrix ι ι ℝ} (hpsd : ∀ n, (M n).PosSemidef)
    (h : Tendsto (fun n => ‖M n - Minf‖) atTop (nhds 0)) :
    Minf.PosSemidef := by
  -- symmetry in the limit
  have hherm : Minf.IsHermitian := by
    rw [Matrix.IsHermitian,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    have hb : ∀ n, ‖Minfᵀ - Minf‖
        ≤ (Fintype.card ι : ℝ) * ‖M n - Minf‖ + ‖M n - Minf‖ := by
      intro n
      have h1 : Minfᵀ - Minf
          = -((M n - Minf)ᵀ) + (M n - Minf) := by
        rw [Matrix.transpose_sub, (hpsd n).1.transpose_eq_self]
        abel
      calc ‖Minfᵀ - Minf‖
          = ‖-((M n - Minf)ᵀ) + (M n - Minf)‖ := by rw [h1]
      _ ≤ ‖-((M n - Minf)ᵀ)‖ + ‖M n - Minf‖ := norm_add_le _ _
      _ = ‖(M n - Minf)ᵀ‖ + ‖M n - Minf‖ := by rw [norm_neg]
      _ ≤ (Fintype.card ι : ℝ) * ‖M n - Minf‖ + ‖M n - Minf‖ := by
          refine add_le_add (linfty_opNorm_transpose_le' _) le_rfl
    have hsum : Tendsto (fun n =>
        (Fintype.card ι : ℝ) * ‖M n - Minf‖ + ‖M n - Minf‖)
        atTop (nhds 0) := by
      have h1 := (h.const_mul (Fintype.card ι : ℝ)).add h
      simpa using h1
    have hle : ‖Minfᵀ - Minf‖ ≤ 0 :=
      ge_of_tendsto hsum (Filter.Eventually.of_forall hb)
    have h0 : Minfᵀ - Minf = 0 := by
      rw [← norm_le_zero_iff]
      exact hle
    exact sub_eq_zero.mp h0
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm
    fun x => ?_
  rw [star_trivial]
  have hq : Tendsto (fun n => quadForm (M n) x) atTop
      (nhds (quadForm Minf x)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hε' : Tendsto (fun n =>
        (Fintype.card ι : ℝ) * ‖M n - Minf‖ * ‖x‖ ^ 2)
        atTop (nhds 0) := by
      have h1 := (h.const_mul (Fintype.card ι : ℝ)).mul_const
        (‖x‖ ^ 2)
      simpa using h1
    rw [Metric.tendsto_atTop] at hε'
    obtain ⟨N, hN⟩ := hε' ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h2 := hN n hn
    rw [Real.dist_eq] at h2 ⊢
    have h3 : quadForm (M n) x - quadForm Minf x
        = quadForm (M n - Minf) x := by
      rw [quadForm_sub_matrix]
    rw [h3]
    calc |quadForm (M n - Minf) x|
        ≤ (Fintype.card ι : ℝ) * ‖M n - Minf‖ * ‖x‖ ^ 2 :=
          abs_quadForm_le_card_norm' _ x
    _ = |(Fintype.card ι : ℝ) * ‖M n - Minf‖ * ‖x‖ ^ 2 - 0| := by
        rw [sub_zero, abs_of_nonneg (by positivity)]
    _ < ε := h2
  exact ge_of_tendsto hq (Filter.Eventually.of_forall
    fun n => (hpsd n).quadForm_nonneg x)

/-- A Schur-stable transpose (spectrum is transpose-invariant). -/
lemma IsSchurStable.transpose {M : Matrix ι ι ℝ}
    (hM : IsSchurStable M) : IsSchurStable Mᵀ := by
  intro μ hμ
  refine hM μ ?_
  rw [complexify_transpose] at hμ
  exact mem_spectrum_transpose_iff.mp hμ

end Dare
end Estimation
