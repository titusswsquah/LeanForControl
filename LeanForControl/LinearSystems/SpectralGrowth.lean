import LeanForControl.LinearSystems.SpectralDynamics
import Architect

/-!
# Spectral growth facts

The three "spectral dynamics" facts of the `costogo` papers, derived from the
adapted-basis scalarization of `LinearSystems.SpectralDynamics`:

* `LinearSystems.gramian_growth` (`eq:gramian` of Rawlings–Quah–Müller
  2026a, quantitative form of costogo's `fact:gramian`): if every eigenvalue
  of `B` satisfies `|μ| ≥ 1`, the sampled state-energy Gramian grows
  linearly, `∑_{k<T} ‖Bᵏv‖² ≥ c T ‖v‖²`.
* `LinearSystems.no_decay` (`fact:no-decay`): with all eigenvalues on or
  outside the unit circle, `Bᵏv → 0` forces `v = 0`.
* `LinearSystems.pow_mulVec_le_poly` (`fact:poly-growth`): with all
  eigenvalues in the closed unit disc, `‖Bᵏv‖ ≤ c (1+k)^(n-1) ‖v‖`.

Each is proved first for endomorphisms of `ℂⁿ` (`end_*` versions) and then
transferred to real matrices through `complexify`. Vector norms are the sup
norm; the existence statements are norm-independent by finite-dimensional
norm equivalence.
-/

namespace LinearSystems

open Matrix Module Finset Filter

variable {n : ℕ}

section EndoVersions

variable (f : Module.End ℂ (Fin n → ℂ))

/-- Uniform bound for the adapted coordinate functionals: coordinates are
Lipschitz in the vector, with a constant depending only on `f`. -/
private lemma exists_coord_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : AdaptedIndex f) (w : Fin n → ℂ),
      ‖(adaptedBasis f).repr w j‖ ≤ C * ‖w‖ := by
  refine ⟨1 + ∑ j : AdaptedIndex f,
    ‖LinearMap.toContinuousLinearMap ((adaptedBasis f).coord j)‖, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ ∑ j : AdaptedIndex f,
        ‖LinearMap.toContinuousLinearMap ((adaptedBasis f).coord j)‖ :=
      Finset.sum_nonneg fun j _ => norm_nonneg _
    linarith
  · intro j w
    have h1 : ‖(adaptedBasis f).repr w j‖
        = ‖LinearMap.toContinuousLinearMap ((adaptedBasis f).coord j) w‖ := by
      rw [LinearMap.coe_toContinuousLinearMap', Basis.coord_apply]
    have h2 := (LinearMap.toContinuousLinearMap ((adaptedBasis f).coord j)).le_opNorm w
    have h3 : ‖LinearMap.toContinuousLinearMap ((adaptedBasis f).coord j)‖
        ≤ 1 + ∑ j' : AdaptedIndex f,
            ‖LinearMap.toContinuousLinearMap ((adaptedBasis f).coord j')‖ := by
      have hle : ‖LinearMap.toContinuousLinearMap ((adaptedBasis f).coord j)‖
          ≤ ∑ j' : AdaptedIndex f,
              ‖LinearMap.toContinuousLinearMap ((adaptedBasis f).coord j')‖ :=
        Finset.single_le_sum (f := fun j' =>
          ‖LinearMap.toContinuousLinearMap ((adaptedBasis f).coord j')‖)
          (fun j' _ => norm_nonneg _) (Finset.mem_univ j)
      linarith
    rw [h1]
    exact le_trans h2 (mul_le_mul_of_nonneg_right h3 (norm_nonneg w))

/-- The squared norm of a vector is controlled by the sum of squared adapted
coordinates. -/
private lemma exists_norm_sq_le_sum_coord_sq :
    ∃ CB : ℝ, 0 < CB ∧ ∀ v : Fin n → ℂ,
      ‖v‖ ^ 2 ≤ CB * ∑ j : AdaptedIndex f, ‖(adaptedBasis f).repr v j‖ ^ 2 := by
  refine ⟨1 + ∑ j : AdaptedIndex f, ‖adaptedBasis f j‖ ^ 2, ?_, ?_⟩
  · have h : (0 : ℝ) ≤ ∑ j : AdaptedIndex f, ‖adaptedBasis f j‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => by positivity
    linarith
  · intro v
    set b := adaptedBasis f
    have h1 : ‖v‖ ≤ ∑ j : AdaptedIndex f, ‖b j‖ * ‖b.repr v j‖ := by
      conv_lhs => rw [← b.sum_repr v]
      refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
      rw [norm_smul, mul_comm]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : AdaptedIndex f => ‖b j‖) (fun j => ‖b.repr v j‖)
    have h3 : ‖v‖ ^ 2 ≤ (∑ j : AdaptedIndex f, ‖b j‖ * ‖b.repr v j‖) ^ 2 := by
      have h0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg _
      gcongr
    have h4 : (∑ j : AdaptedIndex f, ‖b j‖ ^ 2)
        ≤ 1 + ∑ j : AdaptedIndex f, ‖b j‖ ^ 2 := by linarith
    have h5 : (0 : ℝ) ≤ ∑ j : AdaptedIndex f, ‖b.repr v j‖ ^ 2 :=
      Finset.sum_nonneg fun j _ => by positivity
    calc ‖v‖ ^ 2 ≤ (∑ j : AdaptedIndex f, ‖b j‖ * ‖b.repr v j‖) ^ 2 := h3
    _ ≤ (∑ j : AdaptedIndex f, ‖b j‖ ^ 2) *
          ∑ j : AdaptedIndex f, ‖b.repr v j‖ ^ 2 := h2
    _ ≤ (1 + ∑ j : AdaptedIndex f, ‖b j‖ ^ 2) *
          ∑ j : AdaptedIndex f, ‖b.repr v j‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h4 h5

/-- **Quantitative Gramian growth, endomorphism version**: if every
eigenvalue of `f` lies on or outside the unit circle, the sampled energy of
every orbit grows at least linearly. -/
theorem end_gramian_growth (hf : ∀ μ ∈ spectrum ℂ f, 1 ≤ ‖μ‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ (v : Fin n → ℂ) (T : ℕ), 1 ≤ T →
      c * T * ‖v‖ ^ 2 ≤ ∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2 := by
  rcases isEmpty_or_nonempty (AdaptedIndex f) with hemp | hne
  · -- The space is trivial: every vector is zero.
    refine ⟨1, one_pos, fun v T hT => ?_⟩
    have hv : v = 0 := by
      have h := (adaptedBasis f).sum_repr v
      rw [Finset.univ_eq_empty, Finset.sum_empty] at h
      exact h.symm
    subst hv
    have h1 : (1 : ℝ) * T * ‖(0 : Fin n → ℂ)‖ ^ 2 = 0 := by simp
    rw [h1]
    exact Finset.sum_nonneg fun k _ => by positivity
  · obtain ⟨Cf, hCf, hCfb⟩ := exists_coord_bound f
    obtain ⟨CB, hCB, hCBb⟩ := exists_norm_sq_le_sum_coord_sq f
    set s : ℕ := Fintype.card (AdaptedIndex f) with hs
    have hs0 : 0 < s := Fintype.card_pos
    set γ : ℝ := samplingConst (n - 1) with hγ
    have hγ0 : 0 < γ := samplingConst_pos (n - 1)
    refine ⟨γ / (CB * s * Cf ^ 2), by positivity, fun v T hT => ?_⟩
    set b := adaptedBasis f
    -- Per-coordinate lower bound via the sampled polynomial estimate.
    have hper : ∀ j : AdaptedIndex f,
        γ * T * ‖b.repr v j‖ ^ 2
          ≤ Cf ^ 2 * ∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2 := by
      intro j
      have hμ : 1 ≤ ‖j.1‖ := hf j.1 (adaptedBasis_label_mem_spectrum f j)
      have hμ0 : j.1 ≠ 0 := by
        intro h
        rw [h] at hμ
        norm_num at hμ
      have hps := sum_sq_norm_eval_ge (n - 1) (coordPoly f j v)
        (coordPoly_natDegree_le f j v) T hT
      rw [coordPoly_eval_zero] at hps
      have hterm : ∀ k ∈ range T,
          ‖(coordPoly f j v).eval (k : ℂ)‖ ^ 2
            ≤ Cf ^ 2 * ‖(f ^ k) v‖ ^ 2 := by
        intro k _
        have h1 : ‖b.repr ((f ^ k) v) j‖
            = ‖j.1‖ ^ k * ‖(coordPoly f j v).eval (k : ℂ)‖ := by
          rw [show b.repr ((f ^ k) v) j = (adaptedBasis f).repr ((f ^ k) v) j from rfl,
            repr_pow_apply_eq_pow_mul_eval f j hμ0 v k, norm_mul, norm_pow]
        have h2 : ‖(coordPoly f j v).eval (k : ℂ)‖ ≤ ‖b.repr ((f ^ k) v) j‖ := by
          rw [h1]
          nth_rewrite 1 [← one_mul ‖(coordPoly f j v).eval (k : ℂ)‖]
          exact mul_le_mul_of_nonneg_right (one_le_pow₀ hμ) (norm_nonneg _)
        have h3 : ‖b.repr ((f ^ k) v) j‖ ≤ Cf * ‖(f ^ k) v‖ := hCfb j _
        calc ‖(coordPoly f j v).eval (k : ℂ)‖ ^ 2
            ≤ (Cf * ‖(f ^ k) v‖) ^ 2 := by
              have h0 : (0 : ℝ) ≤ ‖(coordPoly f j v).eval (k : ℂ)‖ := norm_nonneg _
              gcongr
              exact le_trans h2 h3
        _ = Cf ^ 2 * ‖(f ^ k) v‖ ^ 2 := by ring
      calc γ * T * ‖b.repr v j‖ ^ 2
          ≤ ∑ k ∈ range T, ‖(coordPoly f j v).eval (k : ℂ)‖ ^ 2 := hps
      _ ≤ ∑ k ∈ range T, Cf ^ 2 * ‖(f ^ k) v‖ ^ 2 := Finset.sum_le_sum hterm
      _ = Cf ^ 2 * ∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2 := by rw [← Finset.mul_sum]
    -- Sum over coordinates and assemble.
    have hsum : γ * T * ∑ j : AdaptedIndex f, ‖b.repr v j‖ ^ 2
        ≤ s * (Cf ^ 2 * ∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2) := by
      calc γ * T * ∑ j : AdaptedIndex f, ‖b.repr v j‖ ^ 2
          = ∑ j : AdaptedIndex f, γ * T * ‖b.repr v j‖ ^ 2 := by
            rw [Finset.mul_sum]
      _ ≤ ∑ _j : AdaptedIndex f, Cf ^ 2 * ∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2 :=
            Finset.sum_le_sum fun j _ => hper j
      _ = s * (Cf ^ 2 * ∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc γ * T * ‖v‖ ^ 2
        ≤ γ * T * (CB * ∑ j : AdaptedIndex f, ‖b.repr v j‖ ^ 2) := by
          have hγT : (0 : ℝ) ≤ γ * T := by positivity
          exact mul_le_mul_of_nonneg_left (hCBb v) hγT
    _ = CB * (γ * T * ∑ j : AdaptedIndex f, ‖b.repr v j‖ ^ 2) := by ring
    _ ≤ CB * (s * (Cf ^ 2 * ∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hsum hCB.le
    _ = (∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2) * (CB * s * Cf ^ 2) := by ring

/-- **No decay, endomorphism version**: with all eigenvalues on or outside
the unit circle, an orbit converging to zero must start at zero. -/
theorem end_eq_zero_of_tendsto_zero (hf : ∀ μ ∈ spectrum ℂ f, 1 ≤ ‖μ‖)
    {v : Fin n → ℂ}
    (hv : Tendsto (fun k => (f ^ k) v) atTop (nhds 0)) : v = 0 := by
  obtain ⟨c, hc, hgr⟩ := end_gramian_growth f hf
  by_contra hvne
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
  -- The squared norms tend to zero, hence so do their Cesàro averages.
  have h0 : Tendsto (fun k : ℕ => ‖(f ^ k) v‖ ^ 2) atTop (nhds 0) := by
    have h1 : Tendsto (fun k : ℕ => ‖(f ^ k) v‖) atTop (nhds 0) := by
      simpa using hv.norm
    simpa using h1.pow 2
  have hces := h0.cesaro
  -- But the Cesàro averages are bounded below by `c ‖v‖² > 0`.
  have hlb : ∀ᶠ T : ℕ in atTop,
      c * ‖v‖ ^ 2 ≤ (T : ℝ)⁻¹ • ∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with T hT
    have hgrT := hgr v T hT
    have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
    rw [smul_eq_mul, le_inv_mul_iff₀ hTpos]
    calc (T : ℝ) * (c * ‖v‖ ^ 2) = c * T * ‖v‖ ^ 2 := by ring
    _ ≤ ∑ k ∈ range T, ‖(f ^ k) v‖ ^ 2 := hgrT
  have hle : c * ‖v‖ ^ 2 ≤ 0 := ge_of_tendsto hces hlb
  have hpos : 0 < c * ‖v‖ ^ 2 := by positivity
  linarith

/-- **Polynomial growth, endomorphism version**: with all eigenvalues in the
closed unit disc, orbits grow at most like `(1+k)^(n-1)`. -/
theorem end_pow_apply_le_poly (hf : ∀ μ ∈ spectrum ℂ f, ‖μ‖ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (v : Fin n → ℂ),
      ‖(f ^ k) v‖ ≤ c * (1 + k : ℝ) ^ (n - 1) * ‖v‖ := by
  rcases isEmpty_or_nonempty (AdaptedIndex f) with hemp | hne
  · refine ⟨1, one_pos, fun k v => ?_⟩
    have hv : v = 0 := by
      have h := (adaptedBasis f).sum_repr v
      rw [Finset.univ_eq_empty, Finset.sum_empty] at h
      exact h.symm
    subst hv
    simp only [map_zero, norm_zero, mul_zero]
    exact le_refl 0
  · obtain ⟨Cf, hCf, hCfb⟩ := exists_coord_bound f
    set b := adaptedBasis f
    set D : AdaptedIndex f → ℝ :=
      fun j => ∑ r ∈ range n, ‖((f - j.1 • 1) ^ r) (b j)‖ with hD
    refine ⟨1 + Cf * ∑ j : AdaptedIndex f, D j, ?_, fun k v => ?_⟩
    · have h1 : (0 : ℝ) ≤ ∑ j : AdaptedIndex f, D j :=
        Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun r _ => norm_nonneg _
      nlinarith
    · -- Expand `v` in the adapted basis and bound each orbit term.
      have hbase : ∀ j : AdaptedIndex f,
          ‖(f ^ k) (b j)‖ ≤ (1 + k : ℝ) ^ (n - 1) * D j := by
        intro j
        have hμ : ‖j.1‖ ≤ 1 := hf j.1 (adaptedBasis_label_mem_spectrum f j)
        rw [pow_apply_eq_sum_of_mem f (adaptedBasis_mem f j) k]
        refine le_trans (norm_sum_le _ _) ?_
        rw [hD, Finset.mul_sum]
        refine Finset.sum_le_sum fun r hr => ?_
        rw [Finset.mem_range] at hr
        rw [norm_smul, norm_mul, norm_pow, Complex.norm_natCast]
        have hchoose : (k.choose r : ℝ) ≤ (1 + k : ℝ) ^ (n - 1) := by
          have h1 : (k.choose r) ≤ k ^ r := Nat.choose_le_pow k r
          have h2 : (k : ℝ) ^ r ≤ (1 + k : ℝ) ^ r := by
            gcongr
            linarith
          have h3 : (1 + k : ℝ) ^ r ≤ (1 + k : ℝ) ^ (n - 1) := by
            refine pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) k]) ?_
            omega
          calc (k.choose r : ℝ) ≤ (k : ℝ) ^ r := by exact_mod_cast h1
          _ ≤ (1 + k : ℝ) ^ r := h2
          _ ≤ (1 + k : ℝ) ^ (n - 1) := h3
        have hμpow : ‖j.1‖ ^ (k - r) ≤ 1 := pow_le_one₀ (norm_nonneg _) hμ
        calc (k.choose r : ℝ) * ‖j.1‖ ^ (k - r) * ‖((f - j.1 • 1) ^ r) (b j)‖
            ≤ (k.choose r : ℝ) * 1 * ‖((f - j.1 • 1) ^ r) (b j)‖ := by
              have h0 : (0 : ℝ) ≤ (k.choose r : ℝ) := by positivity
              have h0' : (0 : ℝ) ≤ ‖((f - j.1 • 1) ^ r) (b j)‖ := norm_nonneg _
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hμpow h0) h0'
        _ = (k.choose r : ℝ) * ‖((f - j.1 • 1) ^ r) (b j)‖ := by ring
        _ ≤ (1 + k : ℝ) ^ (n - 1) * ‖((f - j.1 • 1) ^ r) (b j)‖ :=
              mul_le_mul_of_nonneg_right hchoose (norm_nonneg _)
      calc ‖(f ^ k) v‖ = ‖(f ^ k) (∑ j : AdaptedIndex f, b.repr v j • b j)‖ := by
            rw [b.sum_repr v]
      _ = ‖∑ j : AdaptedIndex f, b.repr v j • (f ^ k) (b j)‖ := by
            rw [map_sum]
            congr 1
            exact Finset.sum_congr rfl fun j _ => by rw [map_smul]
      _ ≤ ∑ j : AdaptedIndex f, ‖b.repr v j‖ * ‖(f ^ k) (b j)‖ := by
            refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
            exact Finset.sum_congr rfl fun j _ => by rw [norm_smul]
      _ ≤ ∑ j : AdaptedIndex f, (Cf * ‖v‖) * ((1 + k : ℝ) ^ (n - 1) * D j) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 := hCfb j v
            have h2 := hbase j
            have h3 : (0 : ℝ) ≤ ‖b.repr v j‖ := norm_nonneg _
            have h4 : (0 : ℝ) ≤ Cf * ‖v‖ := by positivity
            exact mul_le_mul h1 h2 (norm_nonneg _) h4
      _ = ∑ j : AdaptedIndex f, (Cf * ‖v‖ * (1 + k : ℝ) ^ (n - 1)) * D j :=
            Finset.sum_congr rfl fun j _ => by ring
      _ = (Cf * ‖v‖ * (1 + k : ℝ) ^ (n - 1)) * ∑ j : AdaptedIndex f, D j := by
            rw [Finset.mul_sum]
      _ = (Cf * ∑ j : AdaptedIndex f, D j) * (1 + k : ℝ) ^ (n - 1) * ‖v‖ := by ring
      _ ≤ (1 + Cf * ∑ j : AdaptedIndex f, D j) * (1 + k : ℝ) ^ (n - 1) * ‖v‖ := by
            have h1 : Cf * ∑ j : AdaptedIndex f, D j
                ≤ 1 + Cf * ∑ j : AdaptedIndex f, D j := by linarith
            have h2 : (0 : ℝ) ≤ (1 + k : ℝ) ^ (n - 1) * ‖v‖ := by positivity
            calc (Cf * ∑ j : AdaptedIndex f, D j) * (1 + k : ℝ) ^ (n - 1) * ‖v‖
                = (Cf * ∑ j : AdaptedIndex f, D j) * ((1 + k : ℝ) ^ (n - 1) * ‖v‖) := by
                  ring
            _ ≤ (1 + Cf * ∑ j : AdaptedIndex f, D j) * ((1 + k : ℝ) ^ (n - 1) * ‖v‖) :=
                  mul_le_mul_of_nonneg_right h1 h2
            _ = (1 + Cf * ∑ j : AdaptedIndex f, D j) * (1 + k : ℝ) ^ (n - 1) * ‖v‖ := by
                  ring

end EndoVersions

section MatrixVersions

/-- Powers of `Matrix.toLin'` act as powers of the matrix. -/
private lemma toLin'_pow_apply (M : Matrix (Fin n) (Fin n) ℂ) (k : ℕ)
    (v : Fin n → ℂ) : ((Matrix.toLin' M) ^ k) v = (M ^ k) *ᵥ v := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, ← pow_succ']

/-- **Quantitative Gramian growth** (`eq:gramian`): if every eigenvalue of
the real matrix `B` satisfies `|μ| ≥ 1`, then
`∑_{k<T} ‖Bᵏv‖² ≥ c T ‖v‖²` with `c > 0` depending only on `B`. -/
@[blueprint "fact:gramian"
  (statement := /-- Let $B \in \mathbb{R}^{n\times n}$ have every eigenvalue
    with $|\mu| \ge 1$. Then there exists $c_B > 0$ such that for every
    $T \ge 1$ and $v$,
    \[
      \sum_{k=0}^{T-1} \|B^{k} v\|^{2} \;\ge\; c_B\, T\, \|v\|^{2}.
    \] -/)
  (proof := /-- Choose a basis adapted to the generalized eigenspaces of
    $B$ over $\mathbb{C}$. Each adapted coordinate of $B^{k}v$ equals
    $\mu^{k} q(k)$ with $q$ a polynomial of degree $< n$ and
    $q(0)$ the coordinate of $v$; since $|\mu| \ge 1$, the sampled
    polynomial bound \cref{fact:polysample} gives linear growth per
    coordinate, and the coordinates control $\|v\|$. -/)]
theorem gramian_growth (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ μ ∈ spectrum ℂ (complexify B), 1 ≤ ‖μ‖) :
    ∃ c : ℝ, 0 < c ∧ ∀ (v : Fin n → ℝ) (T : ℕ), 1 ≤ T →
      c * T * ‖v‖ ^ 2 ≤ ∑ k ∈ Finset.range T, ‖B ^ k *ᵥ v‖ ^ 2 := by
  have hspec : ∀ μ ∈ spectrum ℂ (Matrix.toLin' (complexify B)), 1 ≤ ‖μ‖ := by
    intro μ hμ
    rw [Matrix.spectrum_toLin'] at hμ
    exact hB μ hμ
  obtain ⟨c, hc, hgr⟩ := end_gramian_growth (Matrix.toLin' (complexify B)) hspec
  refine ⟨c, hc, fun v T hT => ?_⟩
  have h := hgr (complexifyVec v) T hT
  rw [norm_complexifyVec] at h
  refine le_trans h (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  rw [toLin'_pow_apply, ← complexify_pow, complexify_mulVec, norm_complexifyVec]

/-- **No decay for autonomous modes on or outside the unit circle**
(`fact:no-decay`): if every eigenvalue of `B` satisfies `|μ| ≥ 1` and
`Bᵏv → 0`, then `v = 0`. -/
@[blueprint "fact:no-decay"
  (statement := /-- If every eigenvalue of $B$ satisfies $|\mu| \ge 1$,
    then $B^{k} v \to 0$ implies $v = 0$. -/)
  (proof := /-- By \cref{fact:gramian} the running average of
    $\|B^{k}v\|^{2}$ is bounded below by $c_B \|v\|^{2}$, while convergence
    to zero forces the Cesàro average to vanish. -/)]
theorem no_decay (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ μ ∈ spectrum ℂ (complexify B), 1 ≤ ‖μ‖) {v : Fin n → ℝ}
    (hv : Tendsto (fun k => B ^ k *ᵥ v) atTop (nhds 0)) : v = 0 := by
  have hspec : ∀ μ ∈ spectrum ℂ (Matrix.toLin' (complexify B)), 1 ≤ ‖μ‖ := by
    intro μ hμ
    rw [Matrix.spectrum_toLin'] at hμ
    exact hB μ hμ
  have hv' : Tendsto (fun k => ((Matrix.toLin' (complexify B)) ^ k)
      (complexifyVec v)) atTop (nhds 0) := by
    have heq : (fun k => ((Matrix.toLin' (complexify B)) ^ k) (complexifyVec v))
        = fun k => complexifyVec (B ^ k *ᵥ v) := by
      funext k
      rw [toLin'_pow_apply, ← complexify_pow, complexify_mulVec]
    rw [heq]
    -- transfer convergence through the entrywise coercion
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_pi_nhds] at hv
    have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp (hv i)
    simpa using h
  have := end_eq_zero_of_tendsto_zero (Matrix.toLin' (complexify B)) hspec hv'
  exact complexifyVec_injective (by simpa using this)

/-- **Polynomial growth for spectra in the closed unit disc**
(`fact:poly-growth`): if every eigenvalue of `B` satisfies `|μ| ≤ 1`, then
`‖Bᵏv‖ ≤ c (1+k)^(n-1) ‖v‖`. -/
@[blueprint "fact:poly-growth"
  (statement := /-- Let $B \in \mathbb{R}^{n\times n}$ have every eigenvalue
    with $|\mu| \le 1$. Then there is $c$ with
    $\|B^{k} v\| \le c\,(1+k)^{n-1}\,\|v\|$ for all $k \ge 0$ and $v$. -/)
  (proof := /-- Expand $v$ in a basis adapted to the generalized
    eigenspaces; on each, the binomial expansion of
    $B = \mu + N$ truncates at order $n$ and every coefficient is bounded by
    $\binom{k}{r} \le (1+k)^{n-1}$. -/)]
theorem pow_mulVec_le_poly (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : ∀ μ ∈ spectrum ℂ (complexify B), ‖μ‖ ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (k : ℕ) (v : Fin n → ℝ),
      ‖B ^ k *ᵥ v‖ ≤ c * (1 + k : ℝ) ^ (n - 1) * ‖v‖ := by
  have hspec : ∀ μ ∈ spectrum ℂ (Matrix.toLin' (complexify B)), ‖μ‖ ≤ 1 := by
    intro μ hμ
    rw [Matrix.spectrum_toLin'] at hμ
    exact hB μ hμ
  obtain ⟨c, hc, hpg⟩ := end_pow_apply_le_poly (Matrix.toLin' (complexify B)) hspec
  refine ⟨c, hc, fun k v => ?_⟩
  have h := hpg k (complexifyVec v)
  rw [norm_complexifyVec, toLin'_pow_apply, ← complexify_pow, complexify_mulVec,
    norm_complexifyVec] at h
  exact h

end MatrixVersions

end LinearSystems
