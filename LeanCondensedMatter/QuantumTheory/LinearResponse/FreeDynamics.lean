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

The API is dimension-independent. Unbounded Hamiltonians remain outside scope because their
exponentials and products require operator-domain arguments.
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

/-- Positivity of `ℏ` implies that it is nonzero. -/
theorem BoundedFreeSystem.hbar_ne_zero : system.hbar ≠ 0 :=
  ne_of_gt system.hbar_pos

/-- The bounded Schrödinger generator `-(i/ℏ) H₀`. -/
noncomputable def schrodingerGenerator : H →L[ℂ] H :=
  (-(Complex.I / (system.hbar : ℂ))) • system.hamiltonian.1

/-- The generator scaled by a real time parameter. -/
noncomputable def timeScaledGenerator (t : ℝ) : H →L[ℂ] H :=
  (t : ℂ) • schrodingerGenerator system

/-- The free Schrödinger propagator `U₀(t) = exp (-(i t / ℏ) H₀)`. -/
noncomputable def freePropagator (t : ℝ) : H →L[ℂ] H :=
  NormedSpace.exp (timeScaledGenerator system t)

@[simp]
theorem timeScaledGenerator_zero : timeScaledGenerator system 0 = 0 := by
  simp [timeScaledGenerator]

/-- Scaling the free generator is additive in time. -/
theorem timeScaledGenerator_add (t s : ℝ) :
    timeScaledGenerator system (t + s) =
      timeScaledGenerator system t + timeScaledGenerator system s := by
  simp [timeScaledGenerator, add_smul]

/-- The Schrödinger generator is skew-adjoint. -/
theorem star_schrodingerGenerator :
    star (schrodingerGenerator system) = -schrodingerGenerator system := by
  unfold schrodingerGenerator
  rw [star_smul, system.hamiltonian_selfAdjoint.star_eq, ← neg_smul]
  congr 1
  rw [Complex.star_def]
  simp
  ring_nf

/-- Taking the adjoint of the time-scaled generator reverses time. -/
theorem star_timeScaledGenerator (t : ℝ) :
    star (timeScaledGenerator system t) = timeScaledGenerator system (-t) := by
  simp [timeScaledGenerator, star_schrodingerGenerator]

@[simp]
theorem freePropagator_zero : freePropagator system 0 = 1 := by
  simp [freePropagator]

/-- The adjoint of the free propagator is the negative-time propagator. -/
theorem star_freePropagator (t : ℝ) :
    star (freePropagator system t) = freePropagator system (-t) := by
  simp [freePropagator, NormedSpace.star_exp, star_timeScaledGenerator]

/-- Free propagators form a one-parameter multiplicative group. -/
theorem freePropagator_add (t s : ℝ) :
    freePropagator system (t + s) =
      freePropagator system t * freePropagator system s := by
  have hcomm :
      Commute (timeScaledGenerator system t) (timeScaledGenerator system s) := by
    simpa [timeScaledGenerator] using
      ((Commute.refl (schrodingerGenerator system)).smul_left (t : ℂ)).smul_right (s : ℂ)
  rw [freePropagator, timeScaledGenerator_add]
  exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ) hcomm
    ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)
    ((NormedSpace.expSeries_radius_eq_top ℂ (H →L[ℂ] H)).symm ▸ edist_lt_top _ _)

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

/-- Free Heisenberg evolution of a bounded operator. -/
noncomputable def heisenbergEvolution (A : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  freePropagator system (-t) * A * freePropagator system t

@[simp]
theorem heisenbergEvolution_zero (A : H →L[ℂ] H) :
    heisenbergEvolution system A 0 = A := by
  simp [heisenbergEvolution]

/-- Free Heisenberg evolution preserves self-adjointness. -/
theorem isSelfAdjoint_heisenbergEvolution
    (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) :
    IsSelfAdjoint (heisenbergEvolution system A t) := by
  rw [isSelfAdjoint_iff]
  simp [heisenbergEvolution, star_freePropagator, hA.star_eq, mul_assoc]

end
end LinearResponse
end QuantumTheory
