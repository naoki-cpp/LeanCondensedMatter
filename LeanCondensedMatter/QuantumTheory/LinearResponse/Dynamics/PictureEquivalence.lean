import LeanCondensedMatter.Analysis.Operator.TraceClass.AdjointConjugation
import LeanCondensedMatter.Analysis.Operator.Unitary
import LeanCondensedMatter.QuantumTheory.DensityOperator.PureState
import LeanCondensedMatter.QuantumTheory.DensityOperator.ObservableExpectation
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.PureState

set_option linter.style.header false

/-!
# Schrödinger and Heisenberg picture equivalence

This module connects normalized Schrödinger-picture state-vector evolution with the existing bounded
Heisenberg evolution. Physical pure states are the density-backed `PureState` subtype and are
preserved by the same unitary conjugation used for arbitrary density operators. Mixed states are
transported by `ρ(t) = U(t) ρ U(t)†`, with positivity and spectral normalization preserved by
construction.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- Heisenberg evolution of an observable, bundled with the preserved self-adjointness proof. -/
noncomputable def heisenbergObservable (A : Observable H) (t : ℝ) : Observable H :=
  ⟨heisenbergEvolution system t A.1, by
    rw [isSelfAdjoint_iff, ← map_star, A.2.star_eq]⟩

@[simp]
theorem coe_heisenbergObservable (A : Observable H) (t : ℝ) :
    (heisenbergObservable system A t).1 = heisenbergEvolution system t A.1 :=
  rfl

/-- Schrödinger-picture evolution of a density operator by unitary conjugation. -/
noncomputable def evolveDensityOperator (ρ : DensityOperator H) (t : ℝ) :
    DensityOperator H where
  op := adjointConjugate (freePropagator system t) ρ.op
  pos := by
    change ((freePropagator system t) ∘SL ρ.op ∘SL
      ContinuousLinearMap.adjoint (freePropagator system t)).IsPositive
    exact ρ.pos.conj_adjoint (freePropagator system t)
  isTraceClass :=
    ρ.isTraceClass.adjointConjugate (freePropagator system t)
  trace_eq_one := by
    calc
      (ρ.isTraceClass.adjointConjugate (freePropagator system t)).trace =
          ρ.isTraceClass.trace :=
        ρ.isTraceClass.trace_adjointConjugate
          (freePropagator system t) (star_mul_freePropagator system t)
      _ = 1 := ρ.trace_eq_one

@[simp]
theorem evolveDensityOperator_op (ρ : DensityOperator H) (t : ℝ) :
    (evolveDensityOperator system ρ t).op =
      adjointConjugate (freePropagator system t) ρ.op :=
  rfl

/-- Density-operator evolution of a rank-one state agrees exactly with evolution of its normalized
state-vector representative. -/
@[simp]
theorem evolveDensityOperator_pure (ψ : StateVector H) (t : ℝ) :
    evolveDensityOperator system (pure ψ) t =
      pure (evolveState system ψ t) := by
  apply DensityOperator.ext
  change adjointConjugate (freePropagator system t)
      (InnerProductSpace.rankOne ℂ ψ.1 ψ.1) =
    InnerProductSpace.rankOne ℂ
      (freePropagator system t ψ.1) (freePropagator system t ψ.1)
  exact ContinuousLinearMap.adjointConjugate_rankOne
    (freePropagator system t) ψ.1 ψ.1

/-- Bounded unitary density evolution preserves the physical pure-density predicate. -/
theorem isPureDensity_evolveDensityOperator (ρ : PureState H) (t : ℝ) :
    IsPureDensity (evolveDensityOperator system ρ.1 t) := by
  obtain ⟨ψ, hψ⟩ := ρ.exists_stateVector
  refine ⟨evolveState system ψ t, ?_⟩
  rw [hψ]
  exact evolveDensityOperator_pure system ψ t

/-- Schrödinger-picture evolution restricted to physical pure states. The underlying density operator
is evolved by the canonical density-state evolution. -/
noncomputable def evolvePureState (ρ : PureState H) (t : ℝ) : PureState H :=
  ⟨evolveDensityOperator system ρ.1 t,
    isPureDensity_evolveDensityOperator system ρ t⟩

@[simp]
theorem evolvePureState_val (ρ : PureState H) (t : ℝ) :
    (evolvePureState system ρ t).1 = evolveDensityOperator system ρ.1 t :=
  rfl

/-- Restricting density evolution to physical pure states agrees with evolving a chosen normalized
representative first. -/
@[simp]
theorem evolvePureState_ofStateVector (ψ : StateVector H) (t : ℝ) :
    evolvePureState system (PureState.ofStateVector ψ) t =
      PureState.ofStateVector (evolveState system ψ t) := by
  apply Subtype.ext
  exact evolveDensityOperator_pure system ψ t

/-- The complex density-state expectation is identical in the Schrödinger and Heisenberg
pictures for every bounded operator. -/
theorem expectation_evolveDensityOperator_eq_heisenberg
    (ρ : DensityOperator H) (A : H →L[ℂ] H) (t : ℝ) :
    (evolveDensityOperator system ρ t).expectation A =
      ρ.expectation (heisenbergEvolution system t A) := by
  rw [DensityOperator.expectation_apply, DensityOperator.expectation_apply]
  simpa only [evolveDensityOperator, ContinuousLinearMap.adjointConjugate,
    heisenbergEvolution_apply, ← star_freePropagator system t, mul_assoc] using
    (((ρ.isTraceClass.comp_right (star (freePropagator system t))).comp_right A).trace_comp_comm
      (freePropagator system t)).symm

/-- The complex pure-state expectation is identical in the Schrödinger and Heisenberg pictures. -/
theorem expValue_evolveState_eq_heisenberg
    (A : Observable H) (ψ : StateVector H) (t : ℝ) :
    expValue A (evolveState system ψ t) =
      expValue (heisenbergObservable system A t) ψ := by
  rw [← DensityOperator.expectation_pure_observable (evolveState system ψ t) A,
    ← evolveDensityOperator_pure, expectation_evolveDensityOperator_eq_heisenberg]
  exact DensityOperator.expectation_pure_observable ψ (heisenbergObservable system A t)

/-- The lossless real observable expectation is identical in the Schrödinger and Heisenberg
pictures. -/
theorem observableExpValue_evolveState_eq_heisenberg
    (A : Observable H) (ψ : StateVector H) (t : ℝ) :
    observableExpValue A (evolveState system ψ t) =
      observableExpValue (heisenbergObservable system A t) ψ := by
  apply Complex.ofReal_injective
  rw [coe_observableExpValue, coe_observableExpValue,
    expValue_evolveState_eq_heisenberg system]

/-- The lossless real density-state observable expectation is identical in the Schrödinger and
Heisenberg pictures. -/
theorem observableExpectation_evolveDensityOperator_eq_heisenberg
    (ρ : DensityOperator H) (A : Observable H) (t : ℝ) :
    (evolveDensityOperator system ρ t).observableExpectation A =
      ρ.observableExpectation (heisenbergObservable system A t) := by
  apply Complex.ofReal_injective
  rw [← (evolveDensityOperator system ρ t).expectation_observable A,
    ← ρ.expectation_observable (heisenbergObservable system A t)]
  exact expectation_evolveDensityOperator_eq_heisenberg system ρ A.1 t

/-- Physical pure-state observable expectations obey the same Schrödinger/Heisenberg equivalence as
their underlying density operators. -/
theorem observableExpectation_evolvePureState_eq_heisenberg
    (ρ : PureState H) (A : Observable H) (t : ℝ) :
    (evolvePureState system ρ t).observableExpectation A =
      ρ.observableExpectation (heisenbergObservable system A t) := by
  exact observableExpectation_evolveDensityOperator_eq_heisenberg system ρ.1 A t

end
end LinearResponse
end QuantumTheory
