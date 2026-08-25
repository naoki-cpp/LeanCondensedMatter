import LeanCondensedMatter.Analysis.Operator.TraceClass.Unitary
import LeanCondensedMatter.QuantumTheory.DensityOperator.Diagonal
import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
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

/-- The quadratic form of a bounded operator agrees after transporting either the vector or the
operator by the free dynamics. -/
theorem inner_freePropagator_apply_eq_heisenbergEvolution
    (A : H →L[ℂ] H) (x : H) (t : ℝ) :
    inner ℂ (freePropagator system t x)
        (A (freePropagator system t x)) =
      inner ℂ x (heisenbergEvolution system A t x) := by
  change inner ℂ (freePropagator system t x)
      (A (freePropagator system t x)) =
    inner ℂ x
      (freePropagator system (-t) (A (freePropagator system t x)))
  rw [← star_freePropagator system t]
  change inner ℂ (freePropagator system t x)
      (A (freePropagator system t x)) =
    inner ℂ x
      ((ContinuousLinearMap.adjoint (freePropagator system t))
        (A (freePropagator system t x)))
  exact (ContinuousLinearMap.adjoint_inner_right
    (freePropagator system t) x (A (freePropagator system t x))).symm

/-- The complex pure-state expectation is identical in the Schrödinger and Heisenberg pictures. -/
theorem expValue_evolveState_eq_heisenberg
    (A : Observable H) (ψ : State H) (t : ℝ) :
    expValue A (evolveState system ψ t) =
      expValue (heisenbergObservable system A t) ψ := by
  rw [expValue, expValue]
  change inner ℂ (freePropagator system t ψ.1)
      (A.1 (freePropagator system t ψ.1)) =
    inner ℂ ψ.1 (heisenbergEvolution system A.1 t ψ.1)
  exact inner_freePropagator_apply_eq_heisenbergEvolution system A.1 ψ.1 t

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
theorem evolveDensityOperator_trace_eq_one (ρ : DensityOperator H) (t : ℝ) :
    (evolveDensityOperator system ρ t).spectralTraceClass.trace = 1 :=
  (evolveDensityOperator system ρ t).spectralTrace_eq_one

/-- The free propagator as a linear isometric equivalence of the Hilbert space. -/
noncomputable def freePropagatorLinearIsometryEquiv (t : ℝ) : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv :=
    unitaryLinearEquiv (freePropagator system t)
      (star_mul_freePropagator system t)
      (freePropagator_mul_star system t)
  norm_map' := norm_freePropagator_apply system t

/-- Transport a Hilbert basis through the free propagator. -/
noncomputable def evolveHilbertBasis {ι : Type*}
    (b : HilbertBasis ι ℂ H) (t : ℝ) : HilbertBasis ι ℂ H :=
  HilbertBasis.ofRepr ((freePropagatorLinearIsometryEquiv system t).symm.trans b.repr)

@[simp]
theorem evolveHilbertBasis_apply {ι : Type*}
    (b : HilbertBasis ι ℂ H) (t : ℝ) (i : ι) :
    evolveHilbertBasis system b t i = freePropagator system t (b i) := by
  classical
  change (freePropagatorLinearIsometryEquiv system t)
      (b.repr.symm (lp.single 2 i 1)) = freePropagator system t (b i)
  rw [b.repr_symm_single]
  rfl

/-- The complex density-state expectation is identical in the Schrödinger and Heisenberg
pictures for every bounded operator. -/
theorem expectation_evolveDensityOperator_eq_heisenberg
    (ρ : DensityOperator H) (A : H →L[ℂ] H) (t : ℝ) :
    (evolveDensityOperator system ρ t).expectation A =
      ρ.expectation (heisenbergEvolution system A t) := by
  classical
  obtain ⟨ι, b, w, hρ⟩ := ρ.exists_diagonal_hilbertBasis
  let b' : HilbertBasis ι ℂ H := evolveHilbertBasis system b t
  have hρ' : ∀ i,
      (evolveDensityOperator system ρ t).op (b' i) = (w i : ℂ) • b' i := by
    intro i
    rw [evolveDensityOperator_op]
    change freePropagator system t
        (ρ.op ((star (freePropagator system t)) (freePropagator system t (b i)))) =
      (w i : ℂ) • freePropagator system t (b i)
    have hcancel :
        (star (freePropagator system t)) (freePropagator system t (b i)) = b i := by
      have h := congrArg (fun U : H →L[ℂ] H => U (b i))
        (star_mul_freePropagator system t)
      change (star (freePropagator system t))
        (freePropagator system t (b i)) = b i at h
      exact h
    rw [hcancel]
    simpa using congrArg (fun x : H => freePropagator system t x) (hρ i)
  rw [(evolveDensityOperator system ρ t).expectation_eq_tsum_diagonal A b' w hρ',
    ρ.expectation_eq_tsum_diagonal (heisenbergEvolution system A t) b w hρ]
  apply tsum_congr
  intro i
  apply congrArg (fun z : ℂ => (w i : ℂ) * z)
  rw [show b' i = freePropagator system t (b i) from
    evolveHilbertBasis_apply system b t i]
  exact inner_freePropagator_apply_eq_heisenbergEvolution system A (b i) t

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

end
end LinearResponse
end QuantumTheory
