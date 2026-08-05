import LeanCondensedMatter.Analysis.Operator.TraceClass.Unitary
import LeanCondensedMatter.QuantumTheory.LinearResponse.PureStateDynamics

set_option linter.style.header false

/-!
# Schrödinger and Heisenberg picture equivalence

This module connects normalized Schrödinger-picture state evolution with the existing bounded
Heisenberg evolution.  The pure-state layer remains dimension-independent and uses vector
representatives; no quotient by global phase is introduced.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- Heisenberg evolution of an observable, bundled with the preserved self-adjointness proof. -/
noncomputable def heisenbergObservable (A : Observable H) (t : ℝ) : Observable H :=
  ⟨heisenbergEvolution system A.1 t,
    isSelfAdjoint_heisenbergEvolution system A.1 A.2 t⟩

@[simp]
theorem coe_heisenbergObservable (A : Observable H) (t : ℝ) :
    (heisenbergObservable system A t).1 = heisenbergEvolution system A.1 t :=
  rfl

/-- The complex pure-state expectation is identical in the Schrödinger and Heisenberg pictures. -/
theorem expValue_evolveState_eq_heisenberg
    (A : Observable H) (ψ : State H) (t : ℝ) :
    expValue A (evolveState system ψ t) =
      expValue (heisenbergObservable system A t) ψ := by
  rw [expValue, expValue]
  change inner ℂ (freePropagator system t ψ.1)
      (A.1 (freePropagator system t ψ.1)) =
    inner ℂ ψ.1
      (freePropagator system (-t) (A.1 (freePropagator system t ψ.1)))
  rw [← star_freePropagator system t]
  change inner ℂ (freePropagator system t ψ.1)
      (A.1 (freePropagator system t ψ.1)) =
    inner ℂ ψ.1
      ((ContinuousLinearMap.adjoint (freePropagator system t))
        (A.1 (freePropagator system t ψ.1)))
  exact (ContinuousLinearMap.adjoint_inner_right
    (freePropagator system t) ψ.1 (A.1 (freePropagator system t ψ.1))).symm

/-- The lossless real observable expectation is identical in the Schrödinger and Heisenberg
pictures. -/
theorem observableExpValue_evolveState_eq_heisenberg
    (A : Observable H) (ψ : State H) (t : ℝ) :
    observableExpValue A (evolveState system ψ t) =
      observableExpValue (heisenbergObservable system A t) ψ := by
  apply Complex.ofReal_injective
  rw [coe_observableExpValue, coe_observableExpValue,
    expValue_evolveState_eq_heisenberg system]

end
end LinearResponse
end QuantumTheory
