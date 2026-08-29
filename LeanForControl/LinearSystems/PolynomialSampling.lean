import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Sum
import Architect

/-!
# Sampled lower bound for polynomials

The quantitative Gramian bound of the `costogo` C2-necessity argument
(`eq:polysample` of Rawlings–Quah–Müller 2026a) rests on the following fact:
for a complex polynomial `q` of degree at most `d`, the sampled energy
`∑_{k < T} ‖q(k)‖²` grows at least linearly in `T`, with rate proportional
to `‖q(0)‖²` and a constant depending only on `d`:

`∑_{k < T} ‖q(k)‖² ≥ γ_d · T · ‖q(0)‖²`, with `γ_d := 1 / (2 (d+1)³ 4^(d+1))`.

The proof avoids Lagrange interpolation: for every stride `h` the
`(d+1)`-st forward difference of `x ↦ q(hx)` vanishes
(`Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`), which expresses `q(0)` as
a signed binomial combination of `q(h), q(2h), …, q((d+1)h)` and yields
`‖q(0)‖² ≤ (d+1)·4^(d+1) · ∑_{r=1}^{d+1} ‖q(rh)‖²`. Summing over the strides
`h = 1, …, H` with `H := (T-1)/(d+1)` and counting multiplicities (each
sample point `k = r·h` arises for at most `d+1` pairs) gives the linear
growth.
-/

namespace LinearSystems

open Finset Polynomial

open scoped fwdDiff

/-- The sampling constant `γ_d = 1 / (2 (d+1)³ 4^(d+1))` of
`sum_sq_norm_eval_ge`. Only positivity and the explicit form matter. -/
noncomputable def samplingConst (d : ℕ) : ℝ :=
  (2 * (d + 1 : ℝ) ^ 3 * 4 ^ (d + 1))⁻¹

lemma samplingConst_pos (d : ℕ) : 0 < samplingConst d := by
  unfold samplingConst
  positivity

/-- **Stride bound**: for a polynomial of degree `≤ d` and any stride `h`,
`‖q(0)‖² ≤ (d+1)·4^(d+1) · ∑_{i<d+1} ‖q((i+1)h)‖²`. This is the vanishing of
the `(d+1)`-st forward difference of `x ↦ q(hx)`, read as an expression for
`q(0)` and estimated by Cauchy–Schwarz. -/
private lemma stride_bound (d : ℕ) (q : Polynomial ℂ) (hq : q.natDegree ≤ d)
    (h : ℕ) :
    ‖q.eval 0‖ ^ 2
      ≤ ((d + 1 : ℝ) * 4 ^ (d + 1)) *
        ∑ i ∈ range (d + 1), ‖q.eval (((i + 1) * h : ℕ) : ℂ)‖ ^ 2 := by
  -- The rescaled polynomial `Q(x) = q(hx)` has degree ≤ d.
  set Q : Polynomial ℂ := q.comp (C (h : ℂ) * X) with hQ
  have hQdeg : Q.natDegree < d + 1 := by
    have h1 : Q.natDegree ≤ q.natDegree * (C (h : ℂ) * X).natDegree :=
      natDegree_comp_le
    have h2 : (C (h : ℂ) * X).natDegree ≤ 1 := by
      calc (C (h : ℂ) * X).natDegree ≤ (C (h : ℂ)).natDegree + X.natDegree :=
        natDegree_mul_le
      _ ≤ 1 := by simp
    have := le_trans h1 (Nat.mul_le_mul_left _ h2)
    omega
  have hQeval : ∀ i : ℕ, Q.eval ((0 : ℂ) + (i : ℕ) • (1 : ℂ))
      = q.eval ((i * h : ℕ) : ℂ) := by
    intro i
    rw [hQ, eval_comp]
    congr 1
    simp only [eval_mul, eval_C, eval_X]
    push_cast
    ring
  -- The `(d+1)`-st forward difference of `Q.eval` vanishes; expand it at `0`.
  have hvanish : Δ_[(1 : ℂ)]^[d + 1] Q.eval = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hQdeg
  have hsum := fwdDiff_iter_eq_sum_shift (1 : ℂ) Q.eval (d + 1) 0
  rw [hvanish] at hsum
  simp only [Pi.zero_apply] at hsum
  rw [Finset.sum_range_succ'] at hsum
  -- `hsum : 0 = ∑_{i<d+1} c_{i+1} • Q((i+1)·1) + c₀ • Q(0)`.
  have hmain : ((-1 : ℤ) ^ (d + 1 - 0) * ((d + 1).choose 0 : ℤ)) •
        Q.eval ((0 : ℂ) + (0 : ℕ) • (1 : ℂ))
      = -∑ i ∈ range (d + 1),
          ((-1 : ℤ) ^ (d + 1 - (i + 1)) * ((d + 1).choose (i + 1) : ℤ)) •
            Q.eval ((0 : ℂ) + (i + 1 : ℕ) • (1 : ℂ)) :=
    eq_neg_of_add_eq_zero_right hsum.symm
  -- Norm of the left side is `‖q(0)‖`; bound the right side term by term.
  have hnorm0 : ‖((-1 : ℤ) ^ (d + 1 - 0) * ((d + 1).choose 0 : ℤ)) •
      Q.eval ((0 : ℂ) + (0 : ℕ) • (1 : ℂ))‖ = ‖q.eval 0‖ := by
    have h0 := hQeval 0
    simp only [Nat.zero_mul, Nat.cast_zero] at h0
    rw [h0, zsmul_eq_mul]
    push_cast
    simp [norm_pow]
  have hbound : ‖q.eval 0‖
      ≤ ∑ i ∈ range (d + 1),
          ((d + 1).choose (i + 1) : ℝ) * ‖q.eval (((i + 1) * h : ℕ) : ℂ)‖ := by
    rw [← hnorm0, hmain, norm_neg]
    refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    rw [hQeval (i + 1), zsmul_eq_mul]
    push_cast
    simp [norm_pow]
  -- Square and apply Cauchy–Schwarz.
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (range (d + 1))
    (fun i => ((d + 1).choose (i + 1) : ℝ))
    (fun i => ‖q.eval (((i + 1) * h : ℕ) : ℂ)‖)
  have hsq1 : ‖q.eval 0‖ ^ 2
      ≤ (∑ i ∈ range (d + 1),
          ((d + 1).choose (i + 1) : ℝ) * ‖q.eval (((i + 1) * h : ℕ) : ℂ)‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖q.eval 0‖ := norm_nonneg _
    gcongr
  have hsq := hsq1.trans hCS
  -- Bound the binomial-square sum by `(d+1)·4^(d+1)`.
  have hchoose : ∀ i ∈ range (d + 1),
      (((d + 1).choose (i + 1) : ℝ)) ^ 2 ≤ (4 : ℝ) ^ (d + 1) := by
    intro i _
    have h1 : (d + 1).choose (i + 1) ≤ 2 ^ (d + 1) := by
      calc (d + 1).choose (i + 1)
          ≤ ∑ m ∈ range (d + 2), (d + 1).choose m := by
            rcases le_or_gt (i + 1) (d + 1) with hle | hgt
            · exact Finset.single_le_sum (f := fun m => (d + 1).choose m)
                (fun m _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
            · rw [Nat.choose_eq_zero_of_lt hgt]
              exact Nat.zero_le _
      _ = 2 ^ (d + 1) := Nat.sum_range_choose (d + 1)
    have h2 : ((d + 1).choose (i + 1) : ℝ) ≤ (2 : ℝ) ^ (d + 1) := by
      exact_mod_cast h1
    calc (((d + 1).choose (i + 1) : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ (d + 1)) ^ 2 := by
          have h0 : (0 : ℝ) ≤ ((d + 1).choose (i + 1) : ℝ) := by positivity
          gcongr
    _ = (4 : ℝ) ^ (d + 1) := by
          rw [← pow_mul, mul_comm (d + 1) 2, pow_mul]
          norm_num
  have hcsum : (∑ i ∈ range (d + 1), ((d + 1).choose (i + 1) : ℝ) ^ 2)
      ≤ (d + 1 : ℝ) * 4 ^ (d + 1) := by
    calc (∑ i ∈ range (d + 1), ((d + 1).choose (i + 1) : ℝ) ^ 2)
        ≤ ∑ _i ∈ range (d + 1), (4 : ℝ) ^ (d + 1) :=
          Finset.sum_le_sum hchoose
    _ = (d + 1 : ℝ) * 4 ^ (d + 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  refine hsq.trans ?_
  have hE : (0 : ℝ) ≤ ∑ i ∈ range (d + 1), ‖q.eval (((i + 1) * h : ℕ) : ℂ)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  exact mul_le_mul_of_nonneg_right hcsum hE

/-- **Multiplicity count**: summing `F((i+1)·h)` over strides `h ∈ [1, H]` and
offsets `i < d+1` hits each sample point below `T` at most `d+1` times. -/
private lemma double_sum_le (d H T : ℕ) (F : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k)
    (hHT : (d + 1) * H ≤ T - 1) (hT : 1 ≤ T) :
    ∑ h ∈ Icc 1 H, ∑ i ∈ range (d + 1), F ((i + 1) * h)
      ≤ (d + 1 : ℝ) * ∑ k ∈ range T, F k := by
  rw [Finset.sum_comm]
  have hinner : ∀ i ∈ range (d + 1),
      ∑ h ∈ Icc 1 H, F ((i + 1) * h) ≤ ∑ k ∈ range T, F k := by
    intro i hi
    rw [Finset.mem_range] at hi
    have himg : ∑ k ∈ (Icc 1 H).image (fun h => (i + 1) * h), F k
        = ∑ h ∈ Icc 1 H, F ((i + 1) * h) := by
      refine Finset.sum_image fun x _ y _ hxy => ?_
      exact Nat.eq_of_mul_eq_mul_left (by omega) hxy
    rw [← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hF k)
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨h, hh, rfl⟩ := hk
    rw [Finset.mem_Icc] at hh
    rw [Finset.mem_range]
    have h1 : (i + 1) * h ≤ (d + 1) * H :=
      Nat.mul_le_mul (by omega) hh.2
    exact Nat.lt_of_le_of_lt (le_trans h1 hHT) (Nat.sub_lt hT one_pos)
  calc ∑ i ∈ range (d + 1), ∑ h ∈ Icc 1 H, F ((i + 1) * h)
      ≤ ∑ _i ∈ range (d + 1), ∑ k ∈ range T, F k := Finset.sum_le_sum hinner
  _ = (d + 1 : ℝ) * ∑ k ∈ range T, F k := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring

/-- **Sampled lower bound for polynomials** (`eq:polysample`): a complex
polynomial of degree at most `d` satisfies
`∑_{k<T} ‖q(k)‖² ≥ γ_d · T · ‖q(0)‖²` for every horizon `T ≥ 1`, with
`γ_d = samplingConst d` depending only on the degree bound. -/
@[blueprint "fact:polysample"
  (statement := /-- Let $q$ be a complex polynomial of degree at most $d$.
    Then for every $T \ge 1$,
    \[
      \sum_{k=0}^{T-1} |q(k)|^{2} \;\ge\; \gamma_d\, T\, |q(0)|^{2},
      \qquad \gamma_d := \frac{1}{2\,(d+1)^{3}\,4^{d+1}} .
    \] -/)
  (proof := /-- For every stride $h \ge 1$ the $(d{+}1)$-st forward
    difference of $x \mapsto q(hx)$ vanishes, expressing $q(0)$ as a signed
    binomial combination of $q(h), \dots, q((d{+}1)h)$; Cauchy--Schwarz gives
    $|q(0)|^{2} \le (d{+}1)4^{d+1} \sum_{r=1}^{d+1} |q(rh)|^{2}$. Summing
    over strides $h \le H := \lfloor (T-1)/(d+1)\rfloor$ counts each sample
    at most $d{+}1$ times, and $H \gtrsim T/(d+1)$ for
    $T \ge 2(d+1)$; smaller $T$ are absorbed by the $k = 0$ term. -/)]
theorem sum_sq_norm_eval_ge (d : ℕ) (q : Polynomial ℂ) (hq : q.natDegree ≤ d)
    (T : ℕ) (hT : 1 ≤ T) :
    samplingConst d * T * ‖q.eval 0‖ ^ 2
      ≤ ∑ k ∈ range T, ‖q.eval (k : ℂ)‖ ^ 2 := by
  have hFnonneg : ∀ k : ℕ, (0 : ℝ) ≤ ‖q.eval (k : ℂ)‖ ^ 2 := fun k => by positivity
  rcases lt_or_ge T (2 * (d + 1)) with hsmall | hlarge
  · -- Small horizons: the `k = 0` term alone suffices.
    have h0 : ‖q.eval ((0 : ℕ) : ℂ)‖ ^ 2 ≤ ∑ k ∈ range T, ‖q.eval (k : ℂ)‖ ^ 2 :=
      Finset.single_le_sum (fun k _ => hFnonneg k) (Finset.mem_range.mpr (by omega))
    have hγT : samplingConst d * T ≤ 1 := by
      unfold samplingConst
      rw [inv_mul_le_iff₀ (by positivity), mul_one]
      have h1 : (T : ℝ) ≤ 2 * (d + 1) := by exact_mod_cast hsmall.le
      have h3 : (1 : ℝ) ≤ (d + 1 : ℝ) := by
        have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
        linarith
      have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ (d + 1) := one_le_pow₀ (by norm_num)
      have h5 : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 := one_le_pow₀ h3
      have h6 : (1 : ℝ) ≤ (d + 1 : ℝ) ^ 2 * 4 ^ (d + 1) := by nlinarith
      calc (T : ℝ) ≤ 2 * (d + 1) := h1
      _ ≤ 2 * (d + 1) * ((d + 1 : ℝ) ^ 2 * 4 ^ (d + 1)) :=
          le_mul_of_one_le_right (by positivity) h6
      _ = 2 * (d + 1 : ℝ) ^ 3 * 4 ^ (d + 1) := by ring
    calc samplingConst d * T * ‖q.eval 0‖ ^ 2 ≤ 1 * ‖q.eval 0‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hγT (by positivity)
    _ = ‖q.eval 0‖ ^ 2 := one_mul _
    _ ≤ ∑ k ∈ range T, ‖q.eval (k : ℂ)‖ ^ 2 := by
          simpa using h0
  · -- Large horizons: strides.
    set H : ℕ := (T - 1) / (d + 1) with hH
    have hHle : (d + 1) * H ≤ T - 1 := by
      rw [hH, mul_comm]
      exact Nat.div_mul_le_self (T - 1) (d + 1)
    have hTH : T ≤ 2 * ((d + 1) * H) := by
      have hmod := Nat.div_add_mod (T - 1) (d + 1)
      rw [← hH] at hmod
      have hmodlt : (T - 1) % (d + 1) < d + 1 := Nat.mod_lt _ (by omega)
      obtain ⟨P, hP⟩ : ∃ P, (d + 1) * H = P := ⟨_, rfl⟩
      obtain ⟨m, hm⟩ : ∃ m, (T - 1) % (d + 1) = m := ⟨_, rfl⟩
      rw [hP, hm] at hmod
      rw [hm] at hmodlt
      rw [hP]
      omega
    -- Sum the stride bound over `h ∈ [1, H]`.
    have hsumstride : (H : ℝ) * ‖q.eval 0‖ ^ 2
        ≤ ((d + 1 : ℝ) * 4 ^ (d + 1)) *
          ∑ h ∈ Icc 1 H, ∑ i ∈ range (d + 1), ‖q.eval (((i + 1) * h : ℕ) : ℂ)‖ ^ 2 := by
      have h1 : ∑ _h ∈ Icc 1 H, ‖q.eval 0‖ ^ 2
          ≤ ∑ h ∈ Icc 1 H, ((d + 1 : ℝ) * 4 ^ (d + 1)) *
              ∑ i ∈ range (d + 1), ‖q.eval (((i + 1) * h : ℕ) : ℂ)‖ ^ 2 :=
        Finset.sum_le_sum fun h _ => stride_bound d q hq h
      rw [Finset.sum_const, Nat.card_Icc, ← Finset.mul_sum, nsmul_eq_mul] at h1
      simpa [Nat.add_sub_cancel] using h1
    have hdouble := double_sum_le d H T (fun k => ‖q.eval (k : ℂ)‖ ^ 2)
      hFnonneg hHle hT
    -- Chain the two bounds.
    have hchain : (H : ℝ) * ‖q.eval 0‖ ^ 2
        ≤ ((d + 1 : ℝ) * 4 ^ (d + 1)) * ((d + 1 : ℝ) *
            ∑ k ∈ range T, ‖q.eval (k : ℂ)‖ ^ 2) :=
      le_trans hsumstride (mul_le_mul_of_nonneg_left hdouble (by positivity))
    -- Convert `T ≤ 2(d+1)H` into the target inequality.
    have hTr : (T : ℝ) ≤ 2 * ((d + 1 : ℝ) * H) := by exact_mod_cast hTH
    unfold samplingConst
    rw [inv_mul_eq_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc (T : ℝ) * ‖q.eval 0‖ ^ 2
        ≤ (2 * ((d + 1 : ℝ) * H)) * ‖q.eval 0‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hTr (by positivity)
    _ = (2 * (d + 1 : ℝ)) * ((H : ℝ) * ‖q.eval 0‖ ^ 2) := by ring
    _ ≤ (2 * (d + 1 : ℝ)) * (((d + 1 : ℝ) * 4 ^ (d + 1)) * ((d + 1 : ℝ) *
            ∑ k ∈ range T, ‖q.eval (k : ℂ)‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hchain (by positivity)
    _ = (∑ k ∈ range T, ‖q.eval (k : ℂ)‖ ^ 2) * (2 * (d + 1 : ℝ) ^ 3 * 4 ^ (d + 1)) := by
          ring

end LinearSystems
