import LeanForControl.LinearSystems.LQ
import LeanForControl.LinearSystems.Schur
import LeanForControl.LinearSystems.Detectability
import LeanForControl.LinearSystems.LQStability
import LeanForControl.LinearSystems.RiccatiConvergence
import LeanForControl.LinearSystems.StabilizableBound
import Mathlib.Topology.Instances.Matrix
import Architect

/-!
# The classical pillars, discharged (`fact:lqr`, `fact:detect-inj`)

The two classical facts of the `costogo` development, formerly staged as
`sorry` and now **fully proven** (milestone M2):

* `LinearSystems.lqr_convergence` (`fact:lqr`): under stabilizability and
  detectability, the Riccati value iteration converges to a positive
  semidefinite fixed point of the algebraic Riccati equation, with Schur
  closed loop and convergent gains. Assembled from the uniform value
  bound (`StabilizableBound`), monotone-bounded convergence, step
  continuity, and the Joseph-form eigenvector argument
  (`RiccatiConvergence`).
* `LinearSystems.detect_inj` (`fact:detect-inj`): a detectable pair
  admits a Schur-stabilizing output injection — from `fact:lqr` by
  duality with identity weights, transported to arbitrary finite index
  types along a reindexing.

Detectability of `(A, Qs^{1/2})` is phrased kernel-wise
(`∀ unstable eigenvector v, Qs v ≠ 0`), which for `Qs = CᵀRC` with `R ≻ 0`
agrees with detectability of `(A, C)`.
-/

namespace LinearSystems

open Matrix Filter

namespace LQSystem

variable {d m' : ℕ} (S : LQSystem (Fin d) (Fin m'))

/-- **`fact:lqr`** — discrete-time infinite-horizon LQR: under
stabilizability and detectability the Riccati value iteration converges to
a positive semidefinite fixed point with Schur closed loop, and the gains
converge along with it. -/
@[blueprint "fact:lqr"
  (statement := /-- Let $x^{+} = Ax + Bu$ with stage cost
    $x'Q_s x + u'R_u u$, $R_u \succ 0$, $Q_s \succeq 0$, $(A,B)$
    stabilizable and $(A, Q_s^{1/2})$ detectable. Then the Riccati value
    iterates $P_T$ (from $P_0 = 0$) converge to a positive semidefinite
    solution $P$ of the algebraic Riccati equation, the closed loop
    $A - BK(P)$ is Schur, and the gains converge:
    $K(P_T) \to K(P)$, $\Gamma(P_T) \to \Gamma(P)$. -/)
  (proof := /-- Monotone bounded convergence of the value iterates under
    stabilizability (the Bezout spectral split gives the uniform bound),
    fixed point by continuity, stability of the limit closed loop by the
    Joseph-form eigenvector argument under detectability. -/)]
theorem lqr_convergence (hstab : S.Stabilizable) (hdet : S.QsDetectable) :
    ∃ P : Matrix (Fin d) (Fin d) ℝ, P.PosSemidef ∧ S.step P = P ∧
      IsSchurStable (S.Acl P) ∧
      Tendsto (fun T => S.ric T) atTop (nhds P) ∧
      Tendsto (fun T => S.gainK (S.ric T)) atTop (nhds (S.gainK P)) := by
  obtain ⟨c, hc, hb⟩ := exists_ric_bound_of_stabilizable S hstab
  obtain ⟨P, hPpsd, htend⟩ := S.exists_ric_limit_of_bounded hb
  have hfix := S.step_fixed_of_tendsto hPpsd htend
  exact ⟨P, hPpsd, hfix, S.acl_schur_of_fixed hPpsd hfix hdet, htend,
    S.gainK_tendsto_of_tendsto hPpsd htend⟩

end LQSystem

/-- Stabilizing output injection under detectability (`Fin`-indexed
core). -/
private theorem detect_inj_fin {d p' : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (C : Matrix (Fin p') (Fin d) ℝ)
    (hdet : IsDetectable (complexify A) (complexify C)) :
    ∃ L : Matrix (Fin d) (Fin p') ℝ, IsSchurStable (A - L * C) := by
  classical
  -- the dual LQ problem with identity weights
  set S' : LQSystem (Fin d) (Fin p') :=
    { A := Aᵀ
      B := Cᵀ
      Qs := 1
      Ru := 1
      hQs := Matrix.PosSemidef.one
      hRu := Matrix.PosDef.one } with hS'
  have hstab : S'.Stabilizable := by
    show IsStabilizable (complexify Aᵀ) (complexify Cᵀ)
    rw [IsStabilizable, complexify_transpose, complexify_transpose,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
    exact hdet
  have hdet' : S'.QsDetectable := by
    intro μ v _ _ hQv
    have h1 : complexify (1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ v = v := by
      rw [complexify_one, Matrix.one_mulVec]
    rw [show complexify S'.Qs = complexify (1 : Matrix (Fin d) (Fin d) ℝ)
      from rfl, h1] at hQv
    exact hQv
  obtain ⟨P, _, _, hschur, _, _⟩ := S'.lqr_convergence hstab hdet'
  refine ⟨(S'.gainK P)ᵀ, ?_⟩
  have h1 : (S'.Acl P)ᵀ = A - (S'.gainK P)ᵀ * C := by
    show (Aᵀ - Cᵀ * S'.gainK P)ᵀ = _
    rw [Matrix.transpose_sub, Matrix.transpose_transpose,
      Matrix.transpose_mul, Matrix.transpose_transpose]
  have h2 := hschur.transpose
  rwa [h1] at h2

/-- **`fact:detect-inj`** — stabilizing output injection under
detectability, for arbitrary finite index types. -/
@[blueprint "fact:detect-inj"
  (statement := /-- If $(A, C)$ is detectable, there exists $L$ such that
    $A - LC$ is Schur. -/)
  (proof := /-- From \cref{fact:lqr} by duality, applied to the pair
    $(A^{T}, C^{T})$ with identity weights; transported along a
    reindexing of the state space. -/)]
theorem detect_inj {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hdet : IsDetectable (complexify A) (complexify C)) :
    ∃ L : Matrix ι κ ℝ, IsSchurStable (A - L * C) := by
  classical
  set e := Fintype.equivFin ι with he
  set f := Fintype.equivFin κ with hf
  set A' : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℝ :=
    (Matrix.reindex e e) A with hA'
  set C' : Matrix (Fin (Fintype.card κ)) (Fin (Fintype.card ι)) ℝ :=
    (Matrix.reindex f e) C with hC'
  have hcA : complexify A' = (Matrix.reindex e e) (complexify A) := rfl
  have hcC : complexify C' = (Matrix.reindex f e) (complexify C) := rfl
  have hdet' : IsDetectable (complexify A') (complexify C') := by
    intro μ v hμ hAv hCv
    have hw : complexify A *ᵥ (v ∘ e) = μ • (v ∘ e) := by
      funext i
      have h1 := congrFun hAv (e i)
      rw [hcA] at h1
      have h2 : ((Matrix.reindex e e) (complexify A) *ᵥ v) (e i)
          = (complexify A *ᵥ (v ∘ e.symm.symm)) i := by
        show ((complexify A).submatrix e.symm e.symm *ᵥ v) (e i) = _
        rw [Matrix.submatrix_mulVec_equiv]
        show (complexify A *ᵥ (v ∘ e.symm.symm)) (e.symm (e i)) = _
        rw [Equiv.symm_apply_apply]
      rw [h2] at h1
      have h3 : (v ∘ e.symm.symm) = v ∘ e := rfl
      rw [h3] at h1
      exact h1
    have hwC : complexify C *ᵥ (v ∘ e) = 0 := by
      funext i
      have h1 := congrFun hCv (f i)
      rw [hcC] at h1
      have h2 : ((Matrix.reindex f e) (complexify C) *ᵥ v) (f i)
          = (complexify C *ᵥ (v ∘ e.symm.symm)) i := by
        show ((complexify C).submatrix f.symm e.symm *ᵥ v) (f i) = _
        rw [Matrix.submatrix_mulVec_equiv]
        show (complexify C *ᵥ (v ∘ e.symm.symm)) (f.symm (f i)) = _
        rw [Equiv.symm_apply_apply]
      rw [h2] at h1
      exact h1
    have h4 := hdet μ (v ∘ e) hμ hw hwC
    funext j
    have h5 := congrFun h4 (e.symm j)
    simpa using h5
  obtain ⟨L', hL'⟩ := detect_inj_fin A' C' hdet'
  refine ⟨(Matrix.reindex e.symm f.symm) L', ?_⟩
  -- transport the Schur property back through the algebra equivalence
  have halg : A - (Matrix.reindex e.symm f.symm) L' * C
      = (Matrix.reindex e.symm e.symm) (A' - L' * C') := by
    have h1 : (Matrix.reindex e.symm e.symm) (A' - L' * C')
        = (Matrix.reindex e.symm e.symm) A'
          - (Matrix.reindex e.symm e.symm) (L' * C') := by
      funext i j
      rfl
    have h2 : (Matrix.reindex e.symm e.symm) A' = A := by
      funext i j
      show A (e.symm (e.symm.symm i)) (e.symm (e.symm.symm j)) = A i j
      simp
    have h3 : (Matrix.reindex e.symm e.symm) (L' * C')
        = (Matrix.reindex e.symm f.symm) L' * C := by
      have h4 : C = C'.submatrix (f.symm.symm) (e.symm.symm) := by
        funext i j
        show C i j
          = C (f.symm (f.symm.symm i)) (e.symm (e.symm.symm j))
        simp
      show (L' * C').submatrix e.symm.symm e.symm.symm
        = L'.submatrix e.symm.symm f.symm.symm * C
      conv_rhs => rw [h4]
      rw [Matrix.submatrix_mul_equiv]
    rw [h1, h2, h3]
  have hschur2 : IsSchurStable
      ((Matrix.reindex e.symm e.symm) (A' - L' * C')) := by
    intro μ hμ
    refine hL' μ ?_
    have h1 : complexify ((Matrix.reindex e.symm e.symm) (A' - L' * C'))
        = (Matrix.reindexAlgEquiv ℂ ℂ e.symm)
          (complexify (A' - L' * C')) := by
      rw [Matrix.reindexAlgEquiv_apply]
      rfl
    rw [h1, AlgEquiv.spectrum_eq] at hμ
    exact hμ
  rwa [halg]

end LinearSystems
