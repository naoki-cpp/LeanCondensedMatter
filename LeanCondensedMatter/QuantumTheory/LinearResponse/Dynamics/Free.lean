import LeanCondensedMatter.Analysis.Operator.BoundedUnitaryEvolution
import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Algebra.Lie.OfAssociative

set_option linter.style.header false

/-!
# Bounded free quantum dynamics

This module fixes the free-dynamics conventions used by bounded linear response. A free system
consists of a bounded self-adjoint Hamiltonian `H₀` and a strictly positive reduced Planck constant
`ℏ`. Its Schrödinger propagator is

`U₀(t) = exp (-(i t / ℏ) H₀)`,

and the corresponding Heisenberg evolution is

`A_I(t) = U₀(-t) A U₀(t)`.

At fixed time, `heisenbergEvolution system t` is the corresponding star-algebra automorphism.
Consumers use its standard mapping laws; the product formula is an explicit evaluation theorem.

The API is dimension-independent. Unbounded Hamiltonians remain outside scope because their
exponentials and products require operator-domain arguments.
-/

namespace QuantumTheory
namespace LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Data defining bounded free quantum dynamics with the explicit convention `ℏ > 0`.

The Hamiltonian is stored in the canonical physical type `Observable H`; self-adjointness is not
carried as a parallel proof field. -/
structure BoundedFreeSystem (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] where
  /-- The bounded self-adjoint free Hamiltonian. -/
  hamiltonian : Observable H
  /-- The reduced Planck constant used to scale time evolution. -/
  hbar : ℝ
  hbar_pos : 0 < hbar

variable (system : BoundedFreeSystem H)

/-- Self-adjointness of the free Hamiltonian, exposed from its canonical observable data. -/
theorem BoundedFreeSystem.hamiltonian_selfAdjoint :
    IsSelfAdjoint system.hamiltonian.1 :=
  system.hamiltonian.2

/-- The bounded Schrödinger generator `-(i/ℏ) H₀`. -/
noncomputable def schrodingerGenerator : H →L[ℂ] H :=
  (-(Complex.I / (system.hbar : ℂ))) • system.hamiltonian.1

/-- The free Schrödinger propagator `U₀(t) = exp (-(i t / ℏ) H₀)`. -/
noncomputable def freePropagator (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp ((t : ℂ) • schrodingerGenerator system)

/-- The bounded free propagator is the generic bounded unitary evolution of the Hamiltonian scaled
by `ℏ⁻¹`. This bridge keeps the physical free-dynamics API on the shared operator-theoretic
implementation. -/
private theorem freePropagator_eq_boundedUnitaryEvolution (t : ℝ) :
    freePropagator system t =
      LinearPMap.boundedUnitaryEvolution
        (((system.hbar : ℂ)⁻¹) • system.hamiltonian.1) t := by
  unfold freePropagator
  rw [LinearPMap.boundedUnitaryEvolution_eq_exp]
  congr 1
  simp only [schrodingerGenerator, smul_smul, div_eq_mul_inv]
  congr 1
  ring

@[simp]
theorem freePropagator_zero : freePropagator system 0 = 1 := by
  rw [freePropagator_eq_boundedUnitaryEvolution]
  exact LinearPMap.boundedUnitaryEvolution_zero _

/-- The adjoint of the free propagator is the negative-time propagator. -/
theorem star_freePropagator (t : ℝ) :
    star (freePropagator system t) = freePropagator system (-t) := by
  rw [freePropagator_eq_boundedUnitaryEvolution system t,
    freePropagator_eq_boundedUnitaryEvolution system (-t)]
  exact LinearPMap.boundedUnitaryEvolution_star _ (by
    apply IsSelfAdjoint.smul
    · rw [isSelfAdjoint_iff, Complex.star_def]
      simp
    · exact system.hamiltonian_selfAdjoint) t

/-- Free propagators form a one-parameter multiplicative group. -/
theorem freePropagator_add (t s : ℝ) :
    freePropagator system (t + s) =
      freePropagator system t * freePropagator system s := by
  rw [freePropagator_eq_boundedUnitaryEvolution system (t + s),
    freePropagator_eq_boundedUnitaryEvolution system t,
    freePropagator_eq_boundedUnitaryEvolution system s]
  exact LinearPMap.boundedUnitaryEvolution_add _ t s

/-- The negative-time propagator is a left inverse. -/
theorem freePropagator_neg_mul (t : ℝ) :
    freePropagator system (-t) * freePropagator system t = 1 := by
  calc
    freePropagator system (-t) * freePropagator system t =
        freePropagator system (-t + t) := (freePropagator_add system (-t) t).symm
    _ = 1 := by simp

/-- The negative-time propagator is a right inverse. -/
theorem freePropagator_mul_neg (t : ℝ) :
    freePropagator system t * freePropagator system (-t) = 1 := by
  calc
    freePropagator system t * freePropagator system (-t) =
        freePropagator system (t + -t) := (freePropagator_add system t (-t)).symm
    _ = 1 := by simp

/-- The adjoint of the free propagator is its left inverse. -/
@[simp]
theorem star_mul_freePropagator (t : ℝ) :
    star (freePropagator system t) * freePropagator system t = 1 := by
  rw [star_freePropagator]
  exact freePropagator_neg_mul system t

/-- The adjoint of the free propagator is its right inverse. -/
@[simp]
theorem freePropagator_mul_star (t : ℝ) :
    freePropagator system t * star (freePropagator system t) = 1 := by
  rw [star_freePropagator]
  exact freePropagator_mul_neg system t

/-- Every free Schrödinger propagator is a unitary element of the bounded-operator C⋆-algebra. -/
theorem freePropagator_mem_unitary (t : ℝ) :
    freePropagator system t ∈ unitary (H →L[ℂ] H) := by
  rw [Unitary.mem_iff]
  exact ⟨star_mul_freePropagator system t, freePropagator_mul_star system t⟩

/-- The free propagator bundled as a unitary element. -/
noncomputable def freePropagatorUnitary (t : ℝ) : unitary (H →L[ℂ] H) :=
  ⟨freePropagator system t, freePropagator_mem_unitary system t⟩

/-- Free Heisenberg evolution at fixed time, as a star-algebra automorphism. -/
noncomputable def heisenbergEvolution (t : ℝ) :
    (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
  Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (freePropagatorUnitary system (-t))

/-- Applying Heisenberg evolution uses the convention `U₀(-t) A U₀(t)`. -/
theorem heisenbergEvolution_apply (t : ℝ) (A : H →L[ℂ] H) :
    heisenbergEvolution system t A =
      freePropagator system (-t) * A * freePropagator system t := by
  simp [heisenbergEvolution, freePropagatorUnitary, star_freePropagator]

@[simp]
theorem heisenbergEvolution_zero (A : H →L[ℂ] H) :
    heisenbergEvolution system 0 A = A := by
  simp [heisenbergEvolution_apply]

/-- Applying free Heisenberg evolution successively adds the two time parameters. -/
@[simp]
theorem heisenbergEvolution_heisenbergEvolution
    (A : H →L[ℂ] H) (t s : ℝ) :
    heisenbergEvolution system s (heisenbergEvolution system t A) =
      heisenbergEvolution system (t + s) A := by
  simp_rw [heisenbergEvolution_apply]
  rw [show -(t + s) = -s + -t by ring, freePropagator_add, freePropagator_add]
  noncomm_ring

/-- A two-time Heisenberg commutator is the evolution of a relative-time commutator. -/
theorem lie_heisenbergEvolution_eq_relativeTime
    (A B : H →L[ℂ] H) (t s : ℝ) :
    ⁅heisenbergEvolution system t A, heisenbergEvolution system s B⁆ =
      heisenbergEvolution system s ⁅heisenbergEvolution system (t - s) A, B⁆ := by
  have htime :
      heisenbergEvolution system s (heisenbergEvolution system (t - s) A) =
        heisenbergEvolution system t A := by
    rw [heisenbergEvolution_heisenbergEvolution, sub_add_cancel]
  rw [← htime]
  simp only [LieRing.of_associative_ring_bracket, map_sub, map_mul]

/-- Unitary free conjugation preserves the operator norm exactly. -/
@[simp]
theorem norm_heisenbergEvolution (A : H →L[ℂ] H) (t : ℝ) :
    ‖heisenbergEvolution system t A‖ = ‖A‖ := by
  have hU := freePropagator_mem_unitary system t
  rw [heisenbergEvolution_apply, ← star_freePropagator system t]
  calc
    ‖star (freePropagator system t) * A * freePropagator system t‖ =
        ‖star (freePropagator system t) * A‖ :=
      CStarRing.norm_mul_mem_unitary _ hU
    _ = ‖A‖ :=
      CStarRing.norm_mem_unitary_mul A (Unitary.star_mem hU)

/-- The free propagator depends continuously on real time in operator norm. -/
theorem continuous_freePropagator : Continuous (freePropagator system) := by
  change Continuous (fun t : ℝ => freePropagator system t)
  simpa only [freePropagator_eq_boundedUnitaryEvolution] using
    (LinearPMap.boundedUnitaryEvolution_continuous
      (((system.hbar : ℂ)⁻¹) • system.hamiltonian.1))

/-- Free Heisenberg evolution of a fixed bounded observable is norm-continuous in time. -/
theorem continuous_heisenbergEvolution (A : H →L[ℂ] H) :
    Continuous (fun t : ℝ => heisenbergEvolution system t A) := by
  have hneg : Continuous (fun t : ℝ => freePropagator system (-t)) :=
    (continuous_freePropagator system).comp continuous_neg
  simp_rw [heisenbergEvolution_apply]
  exact (hneg.mul continuous_const).mul (continuous_freePropagator system)

end
end LinearResponse
end QuantumTheory
