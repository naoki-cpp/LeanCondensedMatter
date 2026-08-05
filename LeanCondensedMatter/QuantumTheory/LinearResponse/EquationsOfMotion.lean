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
  simpa only [freePropagator, timeScaledGenerator, Complex.coe_smul] using h

/-- The negative-time propagator is differentiable with generator `-G`, where
`G = -(i/ℏ) H₀`. -/
theorem hasDerivAt_freePropagator_neg (t : ℝ) :
    HasDerivAt (fun s : ℝ => freePropagator system (-s))
      ((-schrodingerGenerator system) * freePropagator system (-t)) t := by
  have h := hasDerivAt_exp_smul_const' (-schrodingerGenerator system) t
  simpa only [freePropagator, timeScaledGenerator, Complex.coe_smul, smul_neg,
    neg_smul] using h

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
  change HasDerivAt (fun s : ℝ => freePropagator system s ψ.1)
    (schrodingerGenerator system (freePropagator system t ψ.1)) t
  simpa only [Function.comp_apply, mul_apply_eq_comp] using hcomp.hasDerivAt

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
  let G := schrodingerGenerator system
  let U := freePropagator system t
  let Uneg := freePropagator system (-t)
  have hleft := (hasDerivAt_freePropagator_neg system t).mul_const A
  have hprod := hleft.mul (hasDerivAt_freePropagator system t)
  have hraw : HasDerivAt (heisenbergEvolution system A)
      ((-G) * Uneg * A * U + Uneg * A * (G * U)) t := by
    simpa [G, U, Uneg, heisenbergEvolution, mul_assoc] using hprod
  have hcomm : Commute G U := by
    simpa [G, U] using schrodingerGenerator_commute_freePropagator system t
  have hcommNeg : Commute G Uneg := by
    simpa [G, Uneg] using schrodingerGenerator_commute_freePropagator system (-t)
  have hderiv :
      ((-G) * Uneg * A * U + Uneg * A * (G * U)) =
        heisenbergEvolution system A t * G -
          G * heisenbergEvolution system A t := by
    simp only [heisenbergEvolution]
    rw [neg_mul, hcommNeg.eq, hcomm.eq]
    noncomm_ring
  rw [← hderiv]
  exact hraw

/-- Explicit bounded Heisenberg equation
`dA_H/dt = (i/ℏ) [H₀, A_H]`. -/
theorem heisenbergEquation (A : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (heisenbergEvolution system A)
      ((Complex.I / (system.hbar : ℂ)) •
        (system.hamiltonian * heisenbergEvolution system A t -
          heisenbergEvolution system A t * system.hamiltonian)) t := by
  have h := hasDerivAt_heisenbergEvolution_generator system A t
  have hderiv :
      heisenbergEvolution system A t * schrodingerGenerator system -
          schrodingerGenerator system * heisenbergEvolution system A t =
        (Complex.I / (system.hbar : ℂ)) •
          (system.hamiltonian * heisenbergEvolution system A t -
            heisenbergEvolution system A t * system.hamiltonian) := by
    rw [schrodingerGenerator]
    simp only [mul_smul_comm, smul_mul_assoc]
    module
  rw [← hderiv]
  exact h

/-- Generator form of the bounded von Neumann equation for the evolved density operator. -/
theorem hasDerivAt_evolveDensityOperator_op_generator
    (ρ : DensityOperator H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveDensityOperator system ρ s).op)
      (schrodingerGenerator system * (evolveDensityOperator system ρ t).op -
        (evolveDensityOperator system ρ t).op * schrodingerGenerator system) t := by
  let G := schrodingerGenerator system
  let U := freePropagator system t
  let Uneg := freePropagator system (-t)
  have hleft := (hasDerivAt_freePropagator system t).mul_const ρ.op
  have hprod := hleft.mul (hasDerivAt_freePropagator_neg system t)
  have hraw : HasDerivAt (fun s : ℝ => (evolveDensityOperator system ρ s).op)
      (G * U * ρ.op * Uneg + U * ρ.op * ((-G) * Uneg)) t := by
    simpa [G, U, Uneg, evolveDensityOperator_op, unitaryConjugate,
      star_freePropagator, mul_assoc] using hprod
  have hcomm : Commute G U := by
    simpa [G, U] using schrodingerGenerator_commute_freePropagator system t
  have hcommNeg : Commute G Uneg := by
    simpa [G, Uneg] using schrodingerGenerator_commute_freePropagator system (-t)
  have hderiv :
      (G * U * ρ.op * Uneg + U * ρ.op * ((-G) * Uneg)) =
        G * (evolveDensityOperator system ρ t).op -
          (evolveDensityOperator system ρ t).op * G := by
    simp only [evolveDensityOperator_op, unitaryConjugate, star_freePropagator]
    rw [neg_mul, hcomm.eq, hcommNeg.eq]
    noncomm_ring
  rw [← hderiv]
  exact hraw

/-- Explicit bounded von Neumann equation
`dρ/dt = -(i/ℏ) [H₀, ρ]`. -/
theorem vonNeumannEquation (ρ : DensityOperator H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveDensityOperator system ρ s).op)
      ((-(Complex.I / (system.hbar : ℂ))) •
        (system.hamiltonian * (evolveDensityOperator system ρ t).op -
          (evolveDensityOperator system ρ t).op * system.hamiltonian)) t := by
  have h := hasDerivAt_evolveDensityOperator_op_generator system ρ t
  have hderiv :
      schrodingerGenerator system * (evolveDensityOperator system ρ t).op -
          (evolveDensityOperator system ρ t).op * schrodingerGenerator system =
        (-(Complex.I / (system.hbar : ℂ))) •
          (system.hamiltonian * (evolveDensityOperator system ρ t).op -
            (evolveDensityOperator system ρ t).op * system.hamiltonian) := by
    rw [schrodingerGenerator]
    simp only [mul_smul_comm, smul_mul_assoc]
    module
  rw [← hderiv]
  exact h

end
end LinearResponse
end QuantumTheory
