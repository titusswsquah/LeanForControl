import LeanForControl.LinearSystems.LQ
import LeanForControl.LinearSystems.Schur
import LeanForControl.LinearSystems.Detectability
import Architect

/-!
# Stabilizability and detectability of an LQ problem

The two standing hypotheses of the classical LQR convergence theory,
phrased on `LQSystem` (moved here from the staging file so that the M2
discharge layer can consume them without a cycle).
-/

namespace LinearSystems

open Matrix

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

end LQSystem

end LinearSystems
