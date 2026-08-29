import LeanForControl.LinearSystems.LQ
import LeanForControl.LinearSystems.Schur
import LeanForControl.LinearSystems.Detectability
import Mathlib.Topology.Instances.Matrix
import Architect

/-!
# Staged classical facts (`fact:lqr`, `fact:detect-inj`)

The two classical pillars of the `costogo` development, **stated precisely
and deliberately left as `sorry`** per the blueprint-staging decision of
`notes/costogo-scope.md` (milestone M2 discharges them):

* `LinearSystems.lqr_convergence` (`fact:lqr`): under stabilizability and
  detectability, the Riccati value iteration converges to the unique
  stabilizing solution of the algebraic Riccati equation, with Schur
  closed loop and convergent gains.
* `LinearSystems.detect_inj` (`fact:detect-inj`): a detectable pair admits
  a Schur-stabilizing output injection.

Every theorem in the `Estimation` track that consumes these carries their
`sorryAx` until M2 lands; nothing else in the repository does. Statements
are chosen to be exactly what `lem:prelim`(3)–(4) of the paper consume:
convergence of the iterates *and* of the gains (the latter is derivable
from the former, but staging it avoids an inverse-continuity detour in M1).

Detectability of `(A, Qs^{1/2})` is phrased kernel-wise
(`∀ unstable eigenvector v, Qs v ≠ 0`), which for `Qs = CᵀRC` with `R ≻ 0`
agrees with detectability of `(A, C)`.
-/

namespace LinearSystems

open Matrix Filter

namespace LQSystem

variable {d m' : ℕ} (S : LQSystem (Fin d) (Fin m'))

/-- Stabilizability of the LQ dynamics. -/
def Stabilizable : Prop :=
  IsStabilizable (complexify S.A) (complexify S.B)

/-- Detectability of the LQ state penalty: no unstable mode of `A` is
invisible to `Qs`. For `Qs = CᵀRC` with `R ≻ 0` this is detectability of
`(A, C)`. -/
def QsDetectable : Prop :=
  ∀ (μ : ℂ) (v : Fin d → ℂ), 1 ≤ ‖μ‖ → complexify S.A *ᵥ v = μ • v →
    complexify S.Qs *ᵥ v = 0 → v = 0

/-- **`fact:lqr` (STAGED, M2)** — discrete-time infinite-horizon LQR: under
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
  (proof := /-- Deferred to milestone M2 (see the scope note): monotone
    bounded convergence of the value iterates under stabilizability,
    stability of the limit closed loop under detectability. -/)]
theorem lqr_convergence (hstab : S.Stabilizable) (hdet : S.QsDetectable) :
    ∃ P : Matrix (Fin d) (Fin d) ℝ, P.PosSemidef ∧ S.step P = P ∧
      IsSchurStable (S.Acl P) ∧
      Tendsto (fun T => S.ric T) atTop (nhds P) ∧
      Tendsto (fun T => S.gainK (S.ric T)) atTop (nhds (S.gainK P)) := by
  sorry -- STAGED (M2): fact:lqr

end LQSystem

/-- **`fact:detect-inj` (STAGED, M2)** — stabilizing output injection under
detectability. -/
@[blueprint "fact:detect-inj"
  (statement := /-- If $(A, C)$ is detectable, there exists $L$ such that
    $A - LC$ is Schur. -/)
  (proof := /-- Deferred to milestone M2 (see the scope note); follows from
    \cref{fact:lqr} by duality. -/)]
theorem detect_inj {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] (A : Matrix ι ι ℝ)
    (C : Matrix κ ι ℝ)
    (hdet : IsDetectable (complexify A) (complexify C)) :
    ∃ L : Matrix ι κ ℝ, IsSchurStable (A - L * C) := by
  sorry -- STAGED (M2): fact:detect-inj

end LinearSystems
