import LeanCondensedMatter.Analysis.Operator.BoundedUnitaryEvolution
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Unitary
import LeanCondensedMatter.QuantumTheory.Postulates
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option linter.style.header false

/-!
# Bounded free quantum dynamics

This module fixes the free-dynamics conventions used by bounded linear response. A free system
consists of a bounded self-adjoint Hamiltonian `H₀` and a strictly positive reduced Planck constant
`ℏ`. Its Schrödinger propagator is

`U₀(t) = exp (-(i t / ℏ) H₀)`,

and the corresponding Heisenberg evolution is

`A_I(t) = U₀(-t) A U₀(t)`.

At fixed time, `heisenbergEvolution (freePropagatorGroup system) t` is the corresponding
star-algebra automorphism.
Consumers use its standard mapping laws; the product formula is an explicit evaluation theorem.

This module constructs the bounded-generator instance of the unitary-group dynamics. The algebraic
Heisenberg laws and stationarity do not require this bounded-generator construction. Norm
continuity and generator differentiation remain specific to the bounded realization.
-/

namespace QuantumTheory
namespace LinearResponse

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

/-- The bounded Schrödinger propagators as a one-parameter unitary group. -/
noncomputable def freePropagatorGroup : Multiplicative ℝ →* unitary (H →L[ℂ] H) where
  toFun t := ⟨freePropagator system t.toAdd, freePropagator_mem_unitary system t.toAdd⟩
  map_one' := Subtype.ext (freePropagator_zero system)
  map_mul' t s := Subtype.ext (freePropagator_add system t.toAdd s.toAdd)

@[simp]
theorem freePropagatorGroup_apply (t : ℝ) :
    (freePropagatorGroup system (Multiplicative.ofAdd t) : H →L[ℂ] H) =
      freePropagator system t := rfl

/-- Applying Heisenberg evolution uses the convention `U₀(-t) A U₀(t)`. -/
theorem heisenbergEvolution_freePropagatorGroup_apply (t : ℝ) (A : H →L[ℂ] H) :
    heisenbergEvolution (freePropagatorGroup system) t A =
      freePropagator system (-t) * A * freePropagator system t := by
  simp only [heisenbergEvolution_apply, freePropagatorGroup_apply, star_freePropagator]

/-- The free propagator depends continuously on real time in operator norm. -/
theorem continuous_freePropagator : Continuous (freePropagator system) := by
  change Continuous (fun t : ℝ => freePropagator system t)
  simpa only [freePropagator_eq_boundedUnitaryEvolution] using
    (LinearPMap.boundedUnitaryEvolution_continuous
      (((system.hbar : ℂ)⁻¹) • system.hamiltonian.1))

/-- Free Heisenberg evolution of a fixed bounded observable is norm-continuous in time. -/
theorem continuous_heisenbergEvolution (A : H →L[ℂ] H) :
    Continuous (fun t : ℝ => heisenbergEvolution (freePropagatorGroup system) t A) := by
  have hneg : Continuous (fun t : ℝ => freePropagator system (-t)) :=
    (continuous_freePropagator system).comp continuous_neg
  simp_rw [heisenbergEvolution_freePropagatorGroup_apply]
  exact (hneg.mul continuous_const).mul (continuous_freePropagator system)

end
end LinearResponse
end QuantumTheory
