import LeanForControl.Estimation.ChiProblem
import LeanForControl.LinearSystems.IOSS
import Architect

/-!
# The modified Q-function route (`prop:tvkfQuns`, `prop:modQgas`)

The paper's Lyapunov-like argument for GAS of the optimal estimator:
flip the partial optimal costs against the limiting value
(`Z(j|k) = V∞⁰ − V⁰(j|k)`), add the IOSS-Lyapunov energy of the running
error, and read off the three modified-Q-function properties with
quadratic bounds (`prop:tvkfQuns`). A modified Q-function forces the
error along the limit trajectory to die; `it:xTT` transfers this to the
terminal error, and linearity of the optimizer in the prior mismatch
upgrades pointwise attraction to the uniform `σ_T`-form of GAS
(`prop:modQgas`).
-/

namespace Estimation

open Matrix LinearSystems Filter

open scoped Matrix.Norms.Operator

namespace GeneralSystem

variable {n m p : ℕ} (S : GeneralSystem n m p)

/-! ### Linearity of the optimizer in the prior mismatch -/

lemma isStationary_add {a a' e₀ e₀' : Fin n → ℝ} {T : ℕ}
    (h : S.IsStationary a e₀ T) (h' : S.IsStationary a' e₀' T) :
    S.IsStationary (a + a') (e₀ + e₀') T := by
  obtain ⟨⟨z, hz⟩, hstat⟩ := h
  obtain ⟨⟨z', hz'⟩, hstat'⟩ := h'
  refine ⟨⟨z + z', ?_⟩, ?_⟩
  · rw [Matrix.mulVec_add, ← hz, ← hz']
    module
  · intro d hd
    have h1 := hstat d hd
    have h2 := hstat' d hd
    have h3 : e₀ + e₀' - (a + a') = (e₀ - a) + (e₀' - a') := by
      module
    rw [h3, Matrix.mulVec_add, Matrix.mulVec_add, add_dotProduct,
      add_dotProduct]
    linarith

lemma isStationary_smul {a e₀ : Fin n → ℝ} {T : ℕ} (c : ℝ)
    (h : S.IsStationary a e₀ T) :
    S.IsStationary (c • a) (c • e₀) T := by
  obtain ⟨⟨z, hz⟩, hstat⟩ := h
  refine ⟨⟨c • z, ?_⟩, ?_⟩
  · rw [Matrix.mulVec_smul, ← hz]
    module
  · intro d hd
    have h1 := hstat d hd
    have h3 : c • e₀ - c • a = c • (e₀ - a) := by
      module
    rw [h3, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_dotProduct,
      smul_dotProduct]
    have h4 : c • ((symmPinv S.hSig0.1 *ᵥ (e₀ - a)) ⬝ᵥ d)
        + c • ((S.glq.ric T *ᵥ e₀) ⬝ᵥ d)
        = c * ((symmPinv S.hSig0.1 *ᵥ (e₀ - a)) ⬝ᵥ d
          + (S.glq.ric T *ᵥ e₀) ⬝ᵥ d) := by
      simp [smul_eq_mul]
      ring
    rw [h4, h1, mul_zero]

/-- The optimal initial error is additive in the prior mismatch. -/
lemma optInit_add (a a' : Fin n → ℝ) (T : ℕ) :
    S.optInit (a + a') T = S.optInit a T + S.optInit a' T :=
  (S.isStationary_unique (S.optInit_isStationary (a + a') T)
    (S.isStationary_add (S.optInit_isStationary a T)
      (S.optInit_isStationary a' T)))

/-- The optimal initial error is homogeneous in the prior mismatch. -/
lemma optInit_smul (c : ℝ) (a : Fin n → ℝ) (T : ℕ) :
    S.optInit (c • a) T = c • S.optInit a T :=
  (S.isStationary_unique (S.optInit_isStationary (c • a) T)
    (S.isStationary_smul c (S.optInit_isStationary a T)))

/-- The optimal closed-loop trajectory is additive in the initial
state. -/
lemma optTraj_add (x x' : Fin n → ℝ) (T : ℕ) : ∀ k,
    S.glq.optTraj (x + x') T k
      = S.glq.optTraj x T k + S.glq.optTraj x' T k
  | 0 => rfl
  | k + 1 => by
    show S.glq.Acl (S.glq.ric (T - 1 - k)) *ᵥ S.glq.optTraj (x + x') T k
      = _
    rw [optTraj_add x x' T k, Matrix.mulVec_add]
    rfl

lemma optTraj_smul (c : ℝ) (x : Fin n → ℝ) (T : ℕ) : ∀ k,
    S.glq.optTraj (c • x) T k = c • S.glq.optTraj x T k
  | 0 => rfl
  | k + 1 => by
    show S.glq.Acl (S.glq.ric (T - 1 - k)) *ᵥ S.glq.optTraj (c • x) T k
      = _
    rw [optTraj_smul c x T k, Matrix.mulVec_smul]
    rfl

/-- The optimal terminal error is additive in the prior mismatch. -/
lemma optTerm_add (a a' : Fin n → ℝ) (T : ℕ) :
    S.optTerm (a + a') T = S.optTerm a T + S.optTerm a' T := by
  unfold optTerm
  rw [S.optInit_add, S.optTraj_add]

lemma optTerm_smul (c : ℝ) (a : Fin n → ℝ) (T : ℕ) :
    S.optTerm (c • a) T = c • S.optTerm a T := by
  unfold optTerm
  rw [S.optInit_smul, S.optTraj_smul]

/-- **Pointwise attraction is uniform for a linear estimator**: if every
terminal error dies, they die at a mismatch-free rate. -/
theorem isGAS_of_pointwise
    (h : ∀ a : Fin n → ℝ, Tendsto (fun T => ‖S.optTerm a T‖) atTop
      (nhds 0)) : S.IsGAS := by
  classical
  refine ⟨fun T => ∑ i : Fin n, ‖S.optTerm (Pi.single i 1) T‖, ?_, ?_⟩
  · have h1 := tendsto_finset_sum (Finset.univ : Finset (Fin n))
      (fun i _ => h (Pi.single i 1))
    simpa using h1
  · intro T a
    -- decompose `a` over the standard basis
    have hdec : a = ∑ i : Fin n, a i • (Pi.single i 1 : Fin n → ℝ) := by
      funext j
      rw [Finset.sum_apply]
      simp [Pi.single_apply]
    have hlin : S.optTerm a T
        = ∑ i : Fin n, a i • S.optTerm (Pi.single i 1) T := by
      conv_lhs => rw [hdec]
      -- push optTerm through the finite sum
      have hsum : ∀ (s : Finset (Fin n)),
          S.optTerm (∑ i ∈ s, a i • (Pi.single i 1 : Fin n → ℝ)) T
            = ∑ i ∈ s, a i • S.optTerm (Pi.single i 1) T := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          simp only [Finset.sum_empty]
          have h0 : S.optTerm (0 : Fin n → ℝ) T = 0 := by
            have h2 := S.optTerm_smul 0 0 T
            simpa using h2
          exact h0
        | insert i s hi ih =>
          rw [Finset.sum_insert hi, Finset.sum_insert hi,
            S.optTerm_add, ih, S.optTerm_smul]
      exact hsum Finset.univ
    rw [hlin]
    calc ‖∑ i : Fin n, a i • S.optTerm (Pi.single i 1) T‖
        ≤ ∑ i : Fin n, ‖a i • S.optTerm (Pi.single i 1) T‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i : Fin n, ‖a‖ * ‖S.optTerm (Pi.single i 1) T‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [norm_smul]
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
          exact norm_le_pi_norm a i
      _ = (∑ i : Fin n, ‖S.optTerm (Pi.single i 1) T‖) * ‖a‖ := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GeneralSystem

end Estimation
