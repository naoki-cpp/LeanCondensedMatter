import LeanCondensedMatter.Analysis.Operator.TraceClass.Unitary
import LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation
import LeanCondensedMatter.QuantumTheory.LinearResponse.PureStateDynamics

set_option linter.style.header false

/-!
# Schrödinger and Heisenberg picture equivalence

This module connects normalized Schrödinger-picture state evolution with the existing bounded
Heisenberg evolution.  Pure states remain vector representatives rather than rays.  Mixed states
are transported by the unitary conjugation `ρ(t) = U(t) ρ U(t)†`, with positivity and spectral
normalization preserved by construction.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

open ContinuousLinearMap

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

/-- Schrödinger-picture evolution of a density operator by unitary conjugation. -/
noncomputable def evolveDensityOperator (ρ : DensityOperator H) (t : ℝ) :
    DensityOperator H where
  op := unitaryConjugate (freePropagator system t) ρ.op
  pos := ρ.pos.unitaryConjugate (freePropagator system t)
  spectralTraceClass :=
    ρ.spectralTraceClass.unitaryConjugate
      (freePropagator system t)
      (star_mul_freePropagator system t)
      (freePropagator_mul_star system t)
  spectralTrace_eq_one := by
    calc
      (ρ.spectralTraceClass.unitaryConjugate
        (freePropagator system t)
        (star_mul_freePropagator system t)
        (freePropagator_mul_star system t)).trace =
          ρ.spectralTraceClass.trace :=
        SpectralTraceClass.trace_unitaryConjugate
          ρ.spectralTraceClass (freePropagator system t)
          (star_mul_freePropagator system t)
          (freePropagator_mul_star system t)
      _ = 1 := ρ.spectralTrace_eq_one

@[simp]
theorem evolveDensityOperator_op (ρ : DensityOperator H) (t : ℝ) :
    (evolveDensityOperator system ρ t).op =
      unitaryConjugate (freePropagator system t) ρ.op :=
  rfl

/-- Evolved density operators remain positive. -/
theorem evolveDensityOperator_isPositive (ρ : DensityOperator H) (t : ℝ) :
    (evolveDensityOperator system ρ t).op.IsPositive :=
  (evolveDensityOperator system ρ t).pos

/-- Evolved density operators retain spectral trace one. -/
@[simp]
theorem evolveDensityOperator_trace_eq_one (ρ : DensityOperator H) (t : ℝ) :
    (evolveDensityOperator system ρ t).spectralTraceClass.trace = 1 :=
  (evolveDensityOperator system ρ t).spectralTrace_eq_one

end
end LinearResponse
end QuantumTheory
