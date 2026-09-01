import LeanForControl.LinearSystems.Schur
import Architect

/-!
# Uniform exponential stability of convergent time-varying systems

`fact:uniexp` of `costogo.tex` (Zhou–Zhao 2017), in the direction the paper
consumes: if `F k → L` with `L` Schur stable, then the linear time-varying
system `z (k+1) = F k * z k` is uniformly exponentially stable — the state
transition products decay geometrically, uniformly in the start time.

* `LinearSystems.transitionProd F i l = F (i+l-1) * ⋯ * F (i+1) * F i` —
  the `l`-step transition product starting at time `i`.
* `LinearSystems.transitionProd_norm_le_of_tendsto` — the main estimate
  `‖transitionProd F i l‖ ≤ c ρ^l` with `ρ < 1`, uniform in `i`.

Matrix norms are the `L∞` operator norm (`Matrix.Norms.Operator`).

The proof is the standard block argument: fix `m` with `‖L^m‖ < 1/4`; for
large times every `m`-fold product is within `1/4` of `L^m`, hence has norm
`≤ 1/2`, so products decay by a factor `2` every `m` steps; the finitely
many early times are absorbed into the constant.
-/

namespace LinearSystems

open Matrix Filter

open scoped Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `l`-step state transition product of the time-varying system
`z (k+1) = F k * z k`, started at time `i`:
`transitionProd F i l = F (i+l-1) * ⋯ * F (i+1) * F i`. -/
def transitionProd (F : ℕ → Matrix n n ℝ) (i : ℕ) :
    ℕ → Matrix n n ℝ
  | 0 => 1
  | l + 1 => F (i + l) * transitionProd F i l

@[simp]
lemma transitionProd_zero (F : ℕ → Matrix n n ℝ) (i : ℕ) :
    transitionProd F i 0 = 1 :=
  rfl

lemma transitionProd_succ (F : ℕ → Matrix n n ℝ) (i l : ℕ) :
    transitionProd F i (l + 1) = F (i + l) * transitionProd F i l :=
  rfl

/-- Transition products compose: an `(a+b)`-step product splits as an
`a`-step product after time `i+b` times a `b`-step product from `i`. -/
lemma transitionProd_add (F : ℕ → Matrix n n ℝ) (i a b : ℕ) :
    transitionProd F i (a + b)
      = transitionProd F (i + b) a * transitionProd F i b := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h1 : a + 1 + b = (a + b) + 1 := by omega
    rw [h1, transitionProd_succ, ih, transitionProd_succ, mul_assoc]
    congr 2
    omega

/-- Shifting the coefficient sequence shifts the start time. -/
lemma transitionProd_shift (F : ℕ → Matrix n n ℝ) (K i l : ℕ) :
    transitionProd (fun k => F (k + K)) i l = transitionProd F (i + K) l := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [transitionProd_succ, transitionProd_succ, ih]
    congr 2
    omega

/-- A uniform bound on the factors gives a geometric bound on the products. -/
lemma norm_transitionProd_le (F : ℕ → Matrix n n ℝ) {b : ℝ}
    (hb1 : 1 ≤ b) (hb : ∀ k, ‖F k‖ ≤ b) (i l : ℕ) :
    ‖transitionProd F i l‖ ≤ b ^ l := by
  induction l with
  | zero =>
    rw [transitionProd_zero, pow_zero, ← Matrix.diagonal_one,
      Matrix.linfty_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp
  | succ l ih =>
    rw [transitionProd_succ]
    calc ‖F (i + l) * transitionProd F i l‖
        ≤ ‖F (i + l)‖ * ‖transitionProd F i l‖ := Matrix.linfty_opNorm_mul _ _
    _ ≤ b * b ^ l := by
        have h0 : (0 : ℝ) ≤ ‖transitionProd F i l‖ := norm_nonneg _
        exact mul_le_mul (hb _) ih h0 (by linarith)
    _ = b ^ (l + 1) := by ring

/-- **Perturbation of products**: if every factor is within `ε` of `L` and
everything is bounded by `b ≥ 1`, an `l`-fold product is within
`l·ε·b^l` of `L^l`. -/
lemma norm_transitionProd_sub_pow_le (F : ℕ → Matrix n n ℝ)
    (L : Matrix n n ℝ) {b ε : ℝ} (hb1 : 1 ≤ b)
    (hLb : ‖L‖ ≤ b) (hFb : ∀ k, ‖F k‖ ≤ b) (hε : 0 ≤ ε)
    (hFL : ∀ k, ‖F k - L‖ ≤ ε) (i l : ℕ) :
    ‖transitionProd F i l - L ^ l‖ ≤ l * ε * b ^ l := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hkey : transitionProd F i (l + 1) - L ^ (l + 1)
        = (F (i + l) - L) * transitionProd F i l +
          L * (transitionProd F i l - L ^ l) := by
      rw [transitionProd_succ, pow_succ']
      noncomm_ring
    rw [hkey]
    have h1 : ‖(F (i + l) - L) * transitionProd F i l‖ ≤ ε * b ^ l := by
      calc ‖(F (i + l) - L) * transitionProd F i l‖
          ≤ ‖F (i + l) - L‖ * ‖transitionProd F i l‖ :=
            Matrix.linfty_opNorm_mul _ _
      _ ≤ ε * b ^ l := by
          have h0 : (0 : ℝ) ≤ ‖transitionProd F i l‖ := norm_nonneg _
          exact mul_le_mul (hFL _) (norm_transitionProd_le F hb1 hFb i l) h0 hε
    have h2 : ‖L * (transitionProd F i l - L ^ l)‖ ≤ b * (l * ε * b ^ l) := by
      calc ‖L * (transitionProd F i l - L ^ l)‖
          ≤ ‖L‖ * ‖transitionProd F i l - L ^ l‖ := Matrix.linfty_opNorm_mul _ _
      _ ≤ b * (l * ε * b ^ l) := by
          have h0 : (0 : ℝ) ≤ ‖transitionProd F i l - L ^ l‖ := norm_nonneg _
          exact mul_le_mul hLb ih h0 (by linarith)
    calc ‖(F (i + l) - L) * transitionProd F i l +
          L * (transitionProd F i l - L ^ l)‖
        ≤ ‖(F (i + l) - L) * transitionProd F i l‖ +
          ‖L * (transitionProd F i l - L ^ l)‖ := norm_add_le _ _
    _ ≤ ε * b ^ l + b * (l * ε * b ^ l) := add_le_add h1 h2
    _ ≤ ((l + 1 : ℕ) : ℝ) * ε * b ^ (l + 1) := by
        rw [pow_succ]
        push_cast
        have hbl : (0 : ℝ) ≤ b ^ l := by positivity
        have hl0 : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
        nlinarith [mul_nonneg (mul_nonneg hε hbl) (sub_nonneg.mpr hb1),
          mul_nonneg (mul_nonneg (mul_nonneg hl0 hε) hbl) (sub_nonneg.mpr hb1)]

/-- **Geometric decay from a contracting block**: if all factors are bounded
by `b ≥ 1` and every `m`-fold product (any start) has norm at most `1/2`,
then products decay geometrically at rate `ρ = (1/2)^(1/m)`. -/
lemma norm_transitionProd_le_of_block (F : ℕ → Matrix n n ℝ)
    {b : ℝ} {m : ℕ} (hm : 1 ≤ m) (hb1 : 1 ≤ b) (hFb : ∀ k, ‖F k‖ ≤ b)
    (hblock : ∀ i, ‖transitionProd F i m‖ ≤ 1 / 2) (i l : ℕ) :
    ‖transitionProd F i l‖
      ≤ 2 * b ^ m * ((1 / 2 : ℝ) ^ ((m : ℝ)⁻¹)) ^ l := by
  set ρ : ℝ := (1 / 2 : ℝ) ^ ((m : ℝ)⁻¹) with hρ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  -- Step 1: `‖transitionProd F i (q*m + r)‖ ≤ b^r · (1/2)^q`.
  have hqr : ∀ (q r i' : ℕ), ‖transitionProd F i' (q * m + r)‖
      ≤ b ^ r * (1 / 2 : ℝ) ^ q := by
    intro q
    induction q with
    | zero =>
      intro r i'
      simpa using norm_transitionProd_le F hb1 hFb i' r
    | succ q ih =>
      intro r i'
      have h1 : (q + 1) * m + r = (q * m + r) + m := by ring
      rw [h1, transitionProd_add]
      calc ‖transitionProd F (i' + m) (q * m + r) * transitionProd F i' m‖
          ≤ ‖transitionProd F (i' + m) (q * m + r)‖ * ‖transitionProd F i' m‖ :=
            Matrix.linfty_opNorm_mul _ _
      _ ≤ (b ^ r * (1 / 2 : ℝ) ^ q) * (1 / 2) := by
          have h2 := ih r (i' + m)
          have h3 := hblock i'
          have h0 : (0 : ℝ) ≤ ‖transitionProd F i' m‖ := norm_nonneg _
          have h4 : (0 : ℝ) ≤ b ^ r * (1 / 2 : ℝ) ^ q := by positivity
          exact mul_le_mul h2 h3 h0 h4
      _ = b ^ r * (1 / 2 : ℝ) ^ (q + 1) := by ring
  -- Step 2: convert the block count into the geometric rate `ρ`.
  have hdecomp : l = (l / m) * m + l % m := (Nat.div_add_mod' l m).symm
  have hmain := hqr (l / m) (l % m) i
  rw [← hdecomp] at hmain
  refine le_trans hmain ?_
  have hr : b ^ (l % m) ≤ b ^ m :=
    pow_le_pow_right₀ hb1 (le_of_lt (Nat.mod_lt l (by omega)))
  have hq : ((1 : ℝ) / 2) ^ (l / m) ≤ 2 * ρ ^ l := by
    -- `(1/2)^⌊l/m⌋ ≤ (1/2)^(l/m - 1) = 2 ρ^l` since `⌊l/m⌋ ≥ l/m - 1`.
    have h1 : ρ ^ l = (1 / 2 : ℝ) ^ ((l : ℝ) / m) := by
      rw [hρ, ← Real.rpow_natCast ((1 / 2 : ℝ) ^ ((m : ℝ)⁻¹)) l,
        ← Real.rpow_mul (by norm_num)]
      congr 1
      field_simp
    have h2 : ((1 : ℝ) / 2) ^ (l / m) = (1 / 2 : ℝ) ^ ((l / m : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    have h3 : ((l : ℝ) / m) - 1 ≤ ((l / m : ℕ) : ℝ) := by
      have h4 : (l : ℝ) / m < ((l / m : ℕ) : ℝ) + 1 := by
        rw [div_lt_iff₀ hm0]
        have hq0 := Nat.div_add_mod l m
        have hr0 := Nat.mod_lt l (show 0 < m by omega)
        have hq0' : (m : ℝ) * ((l / m : ℕ) : ℝ) + ((l % m : ℕ) : ℝ) = l := by
          exact_mod_cast hq0
        have hr0' : ((l % m : ℕ) : ℝ) < m := by exact_mod_cast hr0
        nlinarith
      linarith
    have h6 : (1 / 2 : ℝ) ^ ((l / m : ℕ) : ℝ)
        ≤ (1 / 2 : ℝ) ^ (((l : ℝ) / m) - 1) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) h3
    have h7 : (1 / 2 : ℝ) ^ (((l : ℝ) / m) - 1)
        = 2 * (1 / 2 : ℝ) ^ ((l : ℝ) / m) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one]
      ring
    rw [h2, h1]
    rw [h7] at h6
    exact h6
  calc b ^ (l % m) * ((1 : ℝ) / 2) ^ (l / m)
      ≤ b ^ m * (2 * ρ ^ l) := by
        have h0 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (l / m) := by positivity
        have h0' : (0 : ℝ) ≤ b ^ m := by positivity
        exact mul_le_mul hr hq h0 h0'
  _ = 2 * b ^ m * ρ ^ l := by ring

/-- **Uniform exponential stability of a convergent time-varying system**
(`fact:uniexp`, Zhou–Zhao 2017, sufficiency direction): if `F k → L` and `L`
is Schur stable, the transition products of `z⁺ = F k z` decay geometrically,
uniformly in the start time. -/
@[blueprint "fact:uniexp"
  (statement := /-- Let $F(k) \to L$ with $L$ Schur. Then the transition
    matrices of $z^{+} = F(k) z$ satisfy
    $\|\Phi(i+l, i)\| \le c\,\rho^{l}$ for all start times $i$ and lengths
    $l$, for some $c > 0$ and $\rho \in (0,1)$. -/)
  (proof := /-- Fix $m$ with $\|L^{m}\| < 1/4$. For $k \ge K$ all factors
    are within $\varepsilon$ of $L$, so every $m$-fold product beyond $K$ is
    within $m \varepsilon b^{m} \le 1/4$ of $L^{m}$, hence contracts by
    $1/2$; blocks give geometric decay past $K$, and the finitely many
    early products are absorbed into the constant. -/)]
theorem transitionProd_norm_le_of_tendsto (F : ℕ → Matrix n n ℝ)
    (L : Matrix n n ℝ) (hFL : Tendsto F atTop (nhds L))
    (hL : IsSchurStable L) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ i l : ℕ,
      ‖transitionProd F i l‖ ≤ c * ρ ^ l := by
  classical
  -- Fix a contraction horizon `m` for the limit matrix.
  obtain ⟨c₀, ρ₀, hc₀, hρ₀, hρ₀1, hb₀⟩ := hL.exists_pow_norm_le
  have htend : Tendsto (fun m : ℕ => c₀ * ρ₀ ^ m) atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀.le hρ₀1).const_mul c₀
  obtain ⟨m, hm4, hm1⟩ :=
    ((htend.eventually_lt_const (show (0:ℝ) < 1/4 by norm_num)).and
      (eventually_ge_atTop 1)).exists
  have hLm : ‖L ^ m‖ < 1 / 4 := lt_of_le_of_lt (hb₀ m) hm4
  -- Choose the closeness threshold `ε` and the time `K` beyond which it holds.
  set b : ℝ := ‖L‖ + 1 with hb
  have hb1 : (1 : ℝ) ≤ b := by
    have := norm_nonneg L
    rw [hb]
    linarith
  set ε : ℝ := min 1 (1 / (4 * (m * b ^ m))) with hε
  have hε0 : 0 < ε := by
    rw [hε]
    have hmb : (0 : ℝ) < 4 * (m * b ^ m) := by
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      positivity
    exact lt_min one_pos (by positivity)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hFL ε hε0
  have hKdist : ∀ k, K ≤ k → ‖F k - L‖ ≤ ε := fun k hk => by
    have := hK k hk
    rw [dist_eq_norm] at this
    exact this.le
  -- The shifted sequence is uniformly `ε`-close to `L`.
  set G : ℕ → Matrix n n ℝ := fun k => F (k + K) with hG
  have hGL : ∀ k, ‖G k - L‖ ≤ ε := fun k => hKdist (k + K) (by omega)
  have hGb : ∀ k, ‖G k‖ ≤ b := by
    intro k
    have h1 : ‖G k‖ ≤ ‖G k - L‖ + ‖L‖ := by
      calc ‖G k‖ = ‖G k - L + L‖ := by rw [sub_add_cancel]
      _ ≤ ‖G k - L‖ + ‖L‖ := norm_add_le _ _
    have h2 : ε ≤ 1 := by rw [hε]; exact min_le_left _ _
    calc ‖G k‖ ≤ ‖G k - L‖ + ‖L‖ := h1
    _ ≤ ε + ‖L‖ := by linarith [hGL k]
    _ ≤ b := by rw [hb]; linarith
  have hLb : ‖L‖ ≤ b := by rw [hb]; linarith
  -- Every `m`-block of the shifted system contracts by `1/2`.
  have hblock : ∀ i, ‖transitionProd G i m‖ ≤ 1 / 2 := by
    intro i
    have h1 := norm_transitionProd_sub_pow_le G L hb1 hLb hGb hε0.le hGL i m
    have h2 : (m : ℝ) * ε * b ^ m ≤ 1 / 4 := by
      have h3 : ε ≤ 1 / (4 * (m * b ^ m)) := by rw [hε]; exact min_le_right _ _
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hbm : (0 : ℝ) < b ^ m := by positivity
      calc (m : ℝ) * ε * b ^ m ≤ (m : ℝ) * (1 / (4 * (m * b ^ m))) * b ^ m := by
            have h0 : (0 : ℝ) ≤ (m : ℝ) := hm0.le
            have h0' : (0 : ℝ) ≤ b ^ m := hbm.le
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left h3 h0) h0'
      _ = 1 / 4 := by field_simp
    calc ‖transitionProd G i m‖
        = ‖transitionProd G i m - L ^ m + L ^ m‖ := by rw [sub_add_cancel]
    _ ≤ ‖transitionProd G i m - L ^ m‖ + ‖L ^ m‖ := norm_add_le _ _
    _ ≤ (m : ℝ) * ε * b ^ m + ‖L ^ m‖ := by linarith
    _ ≤ 1 / 4 + 1 / 4 := by linarith
    _ = 1 / 2 := by norm_num
  -- Geometric decay past `K`.
  set ρ : ℝ := (1 / 2 : ℝ) ^ ((m : ℝ)⁻¹) with hρ
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity)
  have hGdecay := norm_transitionProd_le_of_block G hm1 hb1 hGb hblock
  -- A crude global bound on all factors, to absorb the times before `K`.
  set Mb : ℝ := b + ∑ k ∈ Finset.range K, ‖F k‖ with hMb
  have hMb1 : (1 : ℝ) ≤ Mb := by
    have h1 : (0 : ℝ) ≤ ∑ k ∈ Finset.range K, ‖F k‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    rw [hMb]
    linarith
  have hMbF : ∀ k, ‖F k‖ ≤ Mb := by
    intro k
    rcases lt_or_ge k K with hk | hk
    · have h1 : ‖F k‖ ≤ ∑ k' ∈ Finset.range K, ‖F k'‖ :=
        Finset.single_le_sum (f := fun k' => ‖F k'‖)
          (fun k' _ => norm_nonneg _) (Finset.mem_range.mpr hk)
      rw [hMb]
      linarith
    · have h1 : ‖F k‖ ≤ b := by
        have h2 : ‖F k‖ ≤ ‖F k - L‖ + ‖L‖ := by
          calc ‖F k‖ = ‖F k - L + L‖ := by rw [sub_add_cancel]
          _ ≤ ‖F k - L‖ + ‖L‖ := norm_add_le _ _
        have h3 : ε ≤ 1 := by rw [hε]; exact min_le_left _ _
        have h4 := hKdist k hk
        rw [hb]
        linarith
      rw [hMb]
      have h5 : (0 : ℝ) ≤ ∑ k' ∈ Finset.range K, ‖F k'‖ :=
        Finset.sum_nonneg fun k' _ => norm_nonneg _
      linarith
  -- Final constant.
  refine ⟨2 * b ^ m * (Mb / ρ) ^ K + (Mb / ρ) ^ K, ρ, ?_, hρ0, hρ1, ?_⟩
  · have h1 : (0 : ℝ) < (Mb / ρ) ^ K := by positivity
    have h2 : (0 : ℝ) < b ^ m := by positivity
    positivity
  · intro i l
    have hMρ1 : (1 : ℝ) ≤ Mb / ρ := by
      rw [le_div_iff₀ hρ0, one_mul]
      exact le_trans hρ1.le hMb1
    rcases le_or_gt K i with hi | hi
    · -- Start past `K`: pure geometric decay, absorb constants.
      have h1 : transitionProd F i l = transitionProd G (i - K) l := by
        rw [hG, transitionProd_shift, show i - K + K = i from by omega]
      rw [h1]
      refine le_trans (hGdecay (i - K) l) ?_
      have h2 : (1 : ℝ) ≤ (Mb / ρ) ^ K := one_le_pow₀ hMρ1
      have h3 : (0 : ℝ) ≤ ρ ^ l := by positivity
      have h5 : 2 * b ^ m ≤ 2 * b ^ m * (Mb / ρ) ^ K + (Mb / ρ) ^ K := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 * b ^ m by positivity)
          (sub_nonneg.mpr h2)]
      exact mul_le_mul_of_nonneg_right h5 h3
    · rcases le_or_gt l (K - i) with hl | hl
      · -- Entirely before `K`: crude bound, absorbed by the constant.
        have h1 := norm_transitionProd_le F hMb1 hMbF i l
        have h2 : Mb ^ l ≤ (Mb / ρ) ^ K * ρ ^ l := by
          have heq : Mb ^ l = (Mb / ρ) ^ l * ρ ^ l := by
            rw [div_pow, div_mul_cancel₀]
            exact pow_ne_zero l (ne_of_gt hρ0)
          rw [heq]
          have h4 : (Mb / ρ) ^ l ≤ (Mb / ρ) ^ K :=
            pow_le_pow_right₀ hMρ1 (by omega)
          exact mul_le_mul_of_nonneg_right h4 (by positivity)
        calc ‖transitionProd F i l‖ ≤ Mb ^ l := h1
        _ ≤ (Mb / ρ) ^ K * ρ ^ l := h2
        _ ≤ (2 * b ^ m * (Mb / ρ) ^ K + (Mb / ρ) ^ K) * ρ ^ l := by
            have h5 : (0 : ℝ) ≤ ρ ^ l := by positivity
            have h6 : (0 : ℝ) ≤ 2 * b ^ m * (Mb / ρ) ^ K := by positivity
            nlinarith
      · -- Crosses `K`: pre-`K` prefix times geometric tail.
        set d : ℕ := K - i with hd
        have hdl : d ≤ l := by omega
        have hTP : transitionProd F i l
            = transitionProd F (i + d) (l - d) * transitionProd F i d := by
          have h := transitionProd_add F i (l - d) d
          have hsplit : (l - d) + d = l := by omega
          rw [hsplit] at h
          exact h
        rw [hTP]
        have hpre : ‖transitionProd F i d‖ ≤ Mb ^ d :=
          norm_transitionProd_le F hMb1 hMbF i d
        have htail : ‖transitionProd F (i + d) (l - d)‖
            ≤ 2 * b ^ m * ρ ^ (l - d) := by
          have h1 : transitionProd F (i + d) (l - d)
              = transitionProd G ((i + d) - K) (l - d) := by
            rw [hG, transitionProd_shift, show i + d - K + K = i + d from by omega]
          rw [h1]
          exact hGdecay _ _
        have heq : ρ ^ (l - d) * Mb ^ d = (Mb / ρ) ^ d * ρ ^ l := by
          have hMbd : Mb ^ d = (Mb / ρ) ^ d * ρ ^ d := by
            rw [div_pow, div_mul_cancel₀]
            exact pow_ne_zero d (ne_of_gt hρ0)
          calc ρ ^ (l - d) * Mb ^ d
              = (Mb / ρ) ^ d * (ρ ^ (l - d) * ρ ^ d) := by rw [hMbd]; ring
          _ = (Mb / ρ) ^ d * ρ ^ l := by
              rw [← pow_add, show l - d + d = l from by omega]
        calc ‖transitionProd F (i + d) (l - d) * transitionProd F i d‖
            ≤ ‖transitionProd F (i + d) (l - d)‖ * ‖transitionProd F i d‖ :=
              Matrix.linfty_opNorm_mul _ _
        _ ≤ (2 * b ^ m * ρ ^ (l - d)) * Mb ^ d := by
            have h0 : (0 : ℝ) ≤ ‖transitionProd F i d‖ := norm_nonneg _
            have h0' : (0 : ℝ) ≤ 2 * b ^ m * ρ ^ (l - d) := by positivity
            exact mul_le_mul htail hpre h0 h0'
        _ = 2 * b ^ m * ((Mb / ρ) ^ d * ρ ^ l) := by
            rw [mul_assoc, heq]
        _ ≤ 2 * b ^ m * ((Mb / ρ) ^ K * ρ ^ l) := by
            have h4 : (Mb / ρ) ^ d ≤ (Mb / ρ) ^ K :=
              pow_le_pow_right₀ hMρ1 (by omega)
            have h5 : (0 : ℝ) ≤ ρ ^ l := by positivity
            have h6 : (0 : ℝ) ≤ 2 * b ^ m := by positivity
            have h7 : (Mb / ρ) ^ d * ρ ^ l ≤ (Mb / ρ) ^ K * ρ ^ l :=
              mul_le_mul_of_nonneg_right h4 h5
            exact mul_le_mul_of_nonneg_left h7 h6
        _ ≤ (2 * b ^ m * (Mb / ρ) ^ K + (Mb / ρ) ^ K) * ρ ^ l := by
            have h5 : (0 : ℝ) ≤ ρ ^ l := by positivity
            have h8 : (0 : ℝ) ≤ (Mb / ρ) ^ K := by positivity
            nlinarith

section RevProd

/-- Reverse-ordered product `F i * F (i+1) * ⋯ * F (i+l-1)`: the form the
horizon-indexed closed-loop propagators of `lem:prelim`(4) take. -/
def revProd (F : ℕ → Matrix n n ℝ) : ℕ → ℕ → Matrix n n ℝ
  | _, 0 => 1
  | i, l + 1 => F i * revProd F (i + 1) l

@[simp]
lemma revProd_zero (F : ℕ → Matrix n n ℝ) (i : ℕ) :
    revProd F i 0 = 1 := rfl

lemma revProd_succ (F : ℕ → Matrix n n ℝ) (i l : ℕ) :
    revProd F i (l + 1) = F i * revProd F (i + 1) l := rfl

/-- Appending one factor on the right. -/
lemma revProd_succ_right (F : ℕ → Matrix n n ℝ) (l : ℕ) :
    ∀ i, revProd F i (l + 1) = revProd F i l * F (i + l) := by
  induction l with
  | zero =>
    intro i
    simp [revProd_succ]
  | succ l ih =>
    intro i
    rw [revProd_succ, ih (i + 1), revProd_succ, Matrix.mul_assoc,
      show i + 1 + l = i + (l + 1) from by omega]

/-- The reverse product is the transpose of the transition product of the
transposed factors. -/
lemma revProd_eq_transpose (F : ℕ → Matrix n n ℝ) (i : ℕ) :
    ∀ l, revProd F i l = (transitionProd (fun r => (F r)ᵀ) i l)ᵀ
  | 0 => by simp
  | l + 1 => by
    rw [revProd_succ_right, transitionProd_succ, Matrix.transpose_mul,
      Matrix.transpose_transpose, revProd_eq_transpose F i l]

/-- The `L∞` operator norm of a transpose is controlled up to a dimension
factor. -/
lemma linfty_opNorm_transpose_le (M : Matrix n n ℝ) :
    ‖Mᵀ‖ ≤ (Fintype.card n : ℝ) * ‖M‖ := by
  have hnn : ‖Mᵀ‖₊ ≤ (Fintype.card n : ℕ) • ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun j _ => ?_
    have h1 : ∀ i : n, ‖Mᵀ j i‖₊ ≤ ‖M‖₊ := by
      intro i
      rw [Matrix.linfty_opNNNorm_def]
      calc ‖Mᵀ j i‖₊ = ‖M i j‖₊ := rfl
      _ ≤ ∑ j', ‖M i j'‖₊ :=
          Finset.single_le_sum (f := fun j' => ‖M i j'‖₊)
            (fun _ _ => zero_le _) (Finset.mem_univ j)
      _ ≤ Finset.univ.sup fun i' => ∑ j', ‖M i' j'‖₊ :=
          Finset.le_sup (f := fun i' => ∑ j', ‖M i' j'‖₊) (Finset.mem_univ i)
    calc ∑ i, ‖Mᵀ j i‖₊ ≤ ∑ _i : n, ‖M‖₊ := Finset.sum_le_sum fun i _ => h1 i
    _ = (Fintype.card n : ℕ) • ‖M‖₊ := by rw [Finset.sum_const, Finset.card_univ]
  calc ‖Mᵀ‖ = ((‖Mᵀ‖₊ : ℝ)) := rfl
  _ ≤ (((Fintype.card n : ℕ) • ‖M‖₊ : NNReal) : ℝ) := by exact_mod_cast hnn
  _ = (Fintype.card n : ℝ) * ‖M‖ := by
      push_cast
      ring

/-- **Uniform exponential decay of the reverse products** when the factors
converge to a Schur matrix — the form `lem:prelim`(4) consumes. -/
theorem revProd_norm_le_of_tendsto (F : ℕ → Matrix n n ℝ)
    (L : Matrix n n ℝ) (hFL : Tendsto F atTop (nhds L))
    (hL : IsSchurStable L) :
    ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ ρ < 1 ∧ ∀ i l : ℕ,
      ‖revProd F i l‖ ≤ c * ρ ^ l := by
  have hFT : Tendsto (fun r => (F r)ᵀ) atTop (nhds Lᵀ) :=
    ((Continuous.matrix_transpose continuous_id).tendsto L).comp hFL
  obtain ⟨c, ρ, hc, hρ0, hρ1, hb⟩ :=
    transitionProd_norm_le_of_tendsto _ Lᵀ hFT hL.transpose
  refine ⟨(Fintype.card n : ℝ) * c + c, ρ, by positivity, hρ0, hρ1, fun i l => ?_⟩
  calc ‖revProd F i l‖ = ‖(transitionProd (fun r => (F r)ᵀ) i l)ᵀ‖ := by
        rw [revProd_eq_transpose]
  _ ≤ (Fintype.card n : ℝ) * ‖transitionProd (fun r => (F r)ᵀ) i l‖ :=
      linfty_opNorm_transpose_le _
  _ ≤ (Fintype.card n : ℝ) * (c * ρ ^ l) := by
      have h0 : (0 : ℝ) ≤ (Fintype.card n : ℝ) := Nat.cast_nonneg (Fintype.card n)
      exact mul_le_mul_of_nonneg_left (hb i l) h0
  _ ≤ ((Fintype.card n : ℝ) * c + c) * ρ ^ l := by
      have h0 : (0 : ℝ) ≤ ρ ^ l := by positivity
      nlinarith [hc.le, h0]

end RevProd


end LinearSystems
