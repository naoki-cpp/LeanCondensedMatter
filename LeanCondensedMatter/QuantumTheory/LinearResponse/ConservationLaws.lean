import LeanCondensedMatter.QuantumTheory.LinearResponse.EquationsOfMotion

set_option linter.style.header false

/-!
# Conservation laws for bounded free quantum dynamics

For the bounded free system `U₀(t) = exp (-(i t / ℏ) H₀)`, every bounded operator commuting with
`H₀` is fixed by Heisenberg evolution.  Schrödinger–Heisenberg picture equivalence then gives the
corresponding pure- and density-state expectation conservation laws without integrating the
equations of motion.

The density-state expectation is also exposed through the pre-existing `NormalizedExpectation`
interface.  A density operator commuting with the Hamiltonian therefore supplies a stationary
linear-response expectation directly from the canonical density dynamics.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- The free Hamiltonian bundled as an observable. -/
noncomputable def hamiltonianObservable : Observable H :=
  ⟨system.hamiltonian, system.hamiltonian_selfAdjoint⟩

@[simp]
theorem coe_hamiltonianObservable :
    (hamiltonianObservable system).1 = system.hamiltonian :=
  rfl

/-- Any bounded operator commuting with the Hamiltonian also commutes with the free propagator. -/
theorem commute_freePropagator_of_commute_hamiltonian
    (A : H →L[ℂ] H) (hA : Commute system.hamiltonian A) (t : ℝ) :
    Commute (freePropagator system t) A := by
  have hgenerator : Commute (schrodingerGenerator system) A := by
    simpa [schrodingerGenerator] using
      hA.smul_left (-(Complex.I / (system.hbar : ℂ)))
  have hscaled : Commute (timeScaledGenerator system t) A := by
    simpa [timeScaledGenerator] using hgenerator.smul_left (t : ℂ)
  simpa [freePropagator] using hscaled.exp_left

/-- A bounded operator commuting with the Hamiltonian is fixed by Heisenberg evolution. -/
theorem heisenbergEvolution_eq_self_of_commute_hamiltonian
    (A : H →L[ℂ] H) (hA : Commute system.hamiltonian A) (t : ℝ) :
    heisenbergEvolution system A t = A := by
  have hU := commute_freePropagator_of_commute_hamiltonian system A hA t
  calc
    heisenbergEvolution system A t =
        freePropagator system (-t) * A * freePropagator system t := rfl
    _ = freePropagator system (-t) * (A * freePropagator system t) :=
      mul_assoc _ _ _
    _ = freePropagator system (-t) * (freePropagator system t * A) := by
      rw [← hU.eq]
    _ = (freePropagator system (-t) * freePropagator system t) * A :=
      (mul_assoc _ _ _).symm
    _ = A := by rw [freePropagator_neg_mul, one_mul]

/-- An observable commuting with the Hamiltonian is fixed as a bundled Heisenberg observable. -/
theorem heisenbergObservable_eq_self_of_commute_hamiltonian
    (A : Observable H) (hA : Commute system.hamiltonian A.1) (t : ℝ) :
    heisenbergObservable system A t = A := by
  apply Subtype.ext
  exact heisenbergEvolution_eq_self_of_commute_hamiltonian system A.1 hA t

/-- Complex pure-state expectations of observables commuting with the Hamiltonian are conserved. -/
theorem expValue_evolveState_eq_of_commute_hamiltonian
    (A : Observable H) (hA : Commute system.hamiltonian A.1)
    (ψ : State H) (t : ℝ) :
    expValue A (evolveState system ψ t) = expValue A ψ := by
  rw [expValue_evolveState_eq_heisenberg system,
    heisenbergObservable_eq_self_of_commute_hamiltonian system A hA t]

/-- Real pure-state expectations of observables commuting with the Hamiltonian are conserved. -/
theorem observableExpValue_evolveState_eq_of_commute_hamiltonian
    (A : Observable H) (hA : Commute system.hamiltonian A.1)
    (ψ : State H) (t : ℝ) :
    observableExpValue A (evolveState system ψ t) = observableExpValue A ψ := by
  rw [observableExpValue_evolveState_eq_heisenberg system,
    heisenbergObservable_eq_self_of_commute_hamiltonian system A hA t]

/-- Complex density-state expectations of bounded operators commuting with the Hamiltonian are
conserved. -/
theorem expectation_evolveDensityOperator_eq_of_commute_hamiltonian
    (ρ : DensityOperator H) (A : H →L[ℂ] H)
    (hA : Commute system.hamiltonian A) (t : ℝ) :
    (evolveDensityOperator system ρ t).expectation A = ρ.expectation A := by
  rw [expectation_evolveDensityOperator_eq_heisenberg system,
    heisenbergEvolution_eq_self_of_commute_hamiltonian system A hA t]

/-- Real density-state expectations of observables commuting with the Hamiltonian are conserved. -/
theorem observableExpectation_evolveDensityOperator_eq_of_commute_hamiltonian
    (ρ : DensityOperator H) (A : Observable H)
    (hA : Commute system.hamiltonian A.1) (t : ℝ) :
    (evolveDensityOperator system ρ t).observableExpectation A =
      ρ.observableExpectation A := by
  rw [observableExpectation_evolveDensityOperator_eq_heisenberg system,
    heisenbergObservable_eq_self_of_commute_hamiltonian system A hA t]

/-- The Hamiltonian expectation is conserved in every pure state. -/
theorem expValue_hamiltonian_evolveState (ψ : State H) (t : ℝ) :
    expValue (hamiltonianObservable system) (evolveState system ψ t) =
      expValue (hamiltonianObservable system) ψ := by
  exact expValue_evolveState_eq_of_commute_hamiltonian system
    (hamiltonianObservable system) (Commute.refl system.hamiltonian) ψ t

/-- The lossless real Hamiltonian expectation is conserved in every pure state. -/
theorem observableExpValue_hamiltonian_evolveState (ψ : State H) (t : ℝ) :
    observableExpValue (hamiltonianObservable system) (evolveState system ψ t) =
      observableExpValue (hamiltonianObservable system) ψ := by
  exact observableExpValue_evolveState_eq_of_commute_hamiltonian system
    (hamiltonianObservable system) (Commute.refl system.hamiltonian) ψ t

/-- The Hamiltonian expectation is conserved in every density state. -/
theorem expectation_hamiltonian_evolveDensityOperator
    (ρ : DensityOperator H) (t : ℝ) :
    (evolveDensityOperator system ρ t).expectation system.hamiltonian =
      ρ.expectation system.hamiltonian := by
  exact expectation_evolveDensityOperator_eq_of_commute_hamiltonian system ρ
    system.hamiltonian (Commute.refl system.hamiltonian) t

/-- The lossless real Hamiltonian expectation is conserved in every density state. -/
theorem observableExpectation_hamiltonian_evolveDensityOperator
    (ρ : DensityOperator H) (t : ℝ) :
    (evolveDensityOperator system ρ t).observableExpectation
        (hamiltonianObservable system) =
      ρ.observableExpectation (hamiltonianObservable system) := by
  exact observableExpectation_evolveDensityOperator_eq_of_commute_hamiltonian system ρ
    (hamiltonianObservable system) (Commute.refl system.hamiltonian) t

/-- A bounded operator commuting with the Hamiltonian is unchanged by Schrödinger-picture unitary
conjugation. -/
theorem unitaryConjugate_freePropagator_eq_self_of_commute_hamiltonian
    (A : H →L[ℂ] H) (hA : Commute system.hamiltonian A) (t : ℝ) :
    unitaryConjugate (freePropagator system t) A = A := by
  have hU := commute_freePropagator_of_commute_hamiltonian system A hA t
  calc
    unitaryConjugate (freePropagator system t) A =
        freePropagator system t * A * star (freePropagator system t) := rfl
    _ = freePropagator system t * A * freePropagator system (-t) := by
      rw [star_freePropagator]
    _ = A * freePropagator system t * freePropagator system (-t) := by
      rw [hU.eq]
    _ = A * (freePropagator system t * freePropagator system (-t)) :=
      mul_assoc _ _ _
    _ = A := by rw [freePropagator_mul_neg, mul_one]

/-- A density operator commuting with the Hamiltonian is stationary under Schrödinger evolution. -/
theorem evolveDensityOperator_eq_self_of_commute_hamiltonian
    (ρ : DensityOperator H) (hρ : Commute system.hamiltonian ρ.op) (t : ℝ) :
    evolveDensityOperator system ρ t = ρ := by
  apply DensityOperator.ext
  exact unitaryConjugate_freePropagator_eq_self_of_commute_hamiltonian system ρ.op hρ t

/-- A density operator as the normalized expectation interface used by linear response. -/
noncomputable def DensityOperator.toNormalizedExpectation
    (ρ : DensityOperator H) : NormalizedExpectation H where
  toContinuousLinearMap := ρ.expectation
  map_one := by simpa using ρ.expectation_id

@[simp]
theorem DensityOperator.toNormalizedExpectation_apply
    (ρ : DensityOperator H) (A : H →L[ℂ] H) :
    ρ.toNormalizedExpectation A = ρ.expectation A :=
  rfl

/-- A density operator commuting with the Hamiltonian defines a stationary normalized expectation
for the existing linear-response API. -/
theorem isStationary_toNormalizedExpectation_of_commute_hamiltonian
    (ρ : DensityOperator H) (hρ : Commute system.hamiltonian ρ.op) :
    IsStationary system ρ.toNormalizedExpectation := by
  intro t A
  rw [DensityOperator.toNormalizedExpectation_apply,
    DensityOperator.toNormalizedExpectation_apply]
  rw [← expectation_evolveDensityOperator_eq_heisenberg system ρ A t]
  rw [evolveDensityOperator_eq_self_of_commute_hamiltonian system ρ hρ t]

end
end LinearResponse
end QuantumTheory
