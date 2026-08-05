import LeanCondensedMatter.QuantumTheory.LinearResponse.PictureEquivalence
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option linter.style.header false

/-!
# Bounded quantum equations of motion

This module differentiates the bounded free propagator and derives the Schrödinger, Heisenberg,
and von Neumann equations with the convention

`U₀(t) = exp (-(i t / ℏ) H₀)`.

All derivatives are norm derivatives of bounded operators or Hilbert-space vectors. No
finite-dimensional assumption or unbounded-operator domain argument is used.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (system : BoundedFreeSystem H)

/-- The bounded free propagator is norm differentiable, with derivative generated on the left by
`-(i/ℏ) H₀`. -/
theorem hasDerivAt_freePropagator (t : ℝ) :
    HasDerivAt (freePropagator system)
      (schrodingerGenerator system * freePropagator system t) t := by
  have h := hasDerivAt_exp_smul_const' (schrodingerGenerator system) t
  convert h using 1
  · funext s
    simp [freePropagator, timeScaledGenerator]
  · simp [freePropagator, timeScaledGenerator]

/-- The negative-time propagator is differentiable with generator `-G`, where
`G = -(i/ℏ) H₀`. -/
theorem hasDerivAt_freePropagator_neg (t : ℝ) :
    HasDerivAt (fun s : ℝ => freePropagator system (-s))
      ((-schrodingerGenerator system) * freePropagator system (-t)) t := by
  have h := hasDerivAt_exp_smul_const' (-schrodingerGenerator system) t
  convert h using 1
  · funext s
    simp [freePropagator, timeScaledGenerator]
  · simp [freePropagator, timeScaledGenerator]

/-- The constant Schrödinger generator commutes with every free propagator. -/
theorem schrodingerGenerator_commute_freePropagator (t : ℝ) :
    Commute (schrodingerGenerator system) (freePropagator system t) := by
  have h : Commute (schrodingerGenerator system)
      ((t : ℂ) • schrodingerGenerator system) :=
    (Commute.refl (schrodingerGenerator system)).smul_right (t : ℂ)
  simpa [freePropagator, timeScaledGenerator] using h.exp_right

/-- The Schrödinger-picture vector representative satisfies the generator form of the bounded
Schrödinger equation. -/
theorem hasDerivAt_evolveState_val (ψ : State H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveState system ψ s).1)
      (schrodingerGenerator system ((evolveState system ψ t).1)) t := by
  have hU := (hasDerivAt_freePropagator system t).hasFDerivAt
  have hEval : HasFDerivAt
      (fun T : H →L[ℂ] H => T ψ.1)
      ((ContinuousLinearMap.apply ℂ H ψ.1).restrictScalars ℝ)
      (freePropagator system t) :=
    ((ContinuousLinearMap.apply ℂ H ψ.1).restrictScalars ℝ).hasFDerivAt
  have hcomp := hEval.comp t hU
  simpa [evolveState, mul_apply_eq_comp] using hcomp.hasDerivAt

/-- Explicit bounded Schrödinger equation
`dψ/dt = -(i/ℏ) H₀ ψ`. -/
theorem schrodingerEquation (ψ : State H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveState system ψ s).1)
      ((-(Complex.I / (system.hbar : ℂ))) •
        system.hamiltonian ((evolveState system ψ t).1)) t := by
  simpa [schrodingerGenerator, smul_apply] using
    hasDerivAt_evolveState_val system ψ t

/-- Generator form of the bounded Heisenberg equation. -/
theorem hasDerivAt_heisenbergEvolution_generator
    (A : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (heisenbergEvolution system A)
      (heisenbergEvolution system A t * schrodingerGenerator system -
        schrodingerGenerator system * heisenbergEvolution system A t) t := by
  have hleft := (hasDerivAt_freePropagator_neg system t).mul_const A
  have hprod := hleft.mul (hasDerivAt_freePropagator system t)
  have hcomm := schrodingerGenerator_commute_freePropagator system t
  convert hprod using 1
  · funext s
    simp [heisenbergEvolution, mul_assoc]
  · rw [hcomm.eq]
    simp [heisenbergEvolution]
    noncomm_ring

/-- Explicit bounded Heisenberg equation
`dA_H/dt = (i/ℏ) [H₀, A_H]`. -/
theorem heisenbergEquation (A : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (heisenbergEvolution system A)
      ((Complex.I / (system.hbar : ℂ)) •
        (system.hamiltonian * heisenbergEvolution system A t -
          heisenbergEvolution system A t * system.hamiltonian)) t := by
  have h := hasDerivAt_heisenbergEvolution_generator system A t
  convert h using 1
  rw [schrodingerGenerator]
  simp only [mul_smul_comm, smul_mul_assoc, neg_smul]
  module

/-- Generator form of the bounded von Neumann equation for the evolved density operator. -/
theorem hasDerivAt_evolveDensityOperator_op_generator
    (ρ : DensityOperator H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveDensityOperator system ρ s).op)
      (schrodingerGenerator system * (evolveDensityOperator system ρ t).op -
        (evolveDensityOperator system ρ t).op * schrodingerGenerator system) t := by
  have hleft := (hasDerivAt_freePropagator system t).mul_const ρ.op
  have hprod := hleft.mul (hasDerivAt_freePropagator_neg system t)
  have hcomm := schrodingerGenerator_commute_freePropagator system (-t)
  convert hprod using 1
  · funext s
    simp [evolveDensityOperator_op, unitaryConjugate, star_freePropagator, mul_assoc]
  · rw [hcomm.eq]
    simp [evolveDensityOperator_op, unitaryConjugate, star_freePropagator]
    noncomm_ring

/-- Explicit bounded von Neumann equation
`dρ/dt = -(i/ℏ) [H₀, ρ]`. -/
theorem vonNeumannEquation (ρ : DensityOperator H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveDensityOperator system ρ s).op)
      ((-(Complex.I / (system.hbar : ℂ))) •
        (system.hamiltonian * (evolveDensityOperator system ρ t).op -
          (evolveDensityOperator system ρ t).op * system.hamiltonian)) t := by
  have h := hasDerivAt_evolveDensityOperator_op_generator system ρ t
  convert h using 1
  rw [schrodingerGenerator]
  simp only [mul_smul_comm, smul_mul_assoc, neg_smul]
  module

end
end LinearResponse
end QuantumTheory
