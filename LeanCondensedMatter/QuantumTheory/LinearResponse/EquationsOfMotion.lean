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
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at h
  simpa only [freePropagator, timeScaledGenerator, Complex.coe_smul] using h

/-- The negative-time propagator is differentiable with generator `-G`, where
`G = -(i/ℏ) H₀`. -/
theorem hasDerivAt_freePropagator_neg (t : ℝ) :
    HasDerivAt (fun s : ℝ => freePropagator system (-s))
      ((-schrodingerGenerator system) * freePropagator system (-t)) t := by
  have h := hasDerivAt_exp_smul_const' (-schrodingerGenerator system) t
  rw [hasDerivAt_iff_tendsto]
  rw [hasDerivAt_iff_tendsto] at h
  simpa only [freePropagator, timeScaledGenerator, Complex.coe_smul, smul_neg,
    neg_smul] using h

/-- The constant Schrödinger generator commutes with every free propagator. -/
theorem schrodingerGenerator_commute_freePropagator (t : ℝ) :
    Commute (schrodingerGenerator system) (freePropagator system t) := by
  have h : Commute (schrodingerGenerator system)
      ((t : ℂ) • schrodingerGenerator system) :=
    (Commute.refl (schrodingerGenerator system)).smul_right (t : ℂ)
  simpa [freePropagator, timeScaledGenerator] using h.exp_right

/-- Explicit bounded Schrödinger equation
`dψ/dt = -(i/ℏ) H₀ ψ`. -/
theorem schrodingerEquation (ψ : State H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveState system ψ s).1)
      ((-(Complex.I / (system.hbar : ℂ))) •
        system.hamiltonian.1 ((evolveState system ψ t).1)) t := by
  have hU := (hasDerivAt_freePropagator system t).hasFDerivAt
  have hEval : HasFDerivAt
      (fun T : H →L[ℂ] H => T ψ.1)
      ((ContinuousLinearMap.apply ℂ H ψ.1).restrictScalars ℝ)
      (freePropagator system t) :=
    ((ContinuousLinearMap.apply ℂ H ψ.1).restrictScalars ℝ).hasFDerivAt
  have hderiv := (hEval.comp t hU).hasDerivAt
  have hgenerator :
      HasDerivAt (fun s : ℝ => (evolveState system ψ s).1)
        (schrodingerGenerator system ((evolveState system ψ t).1)) t := by
    change HasDerivAt (fun s : ℝ => freePropagator system s ψ.1)
      (schrodingerGenerator system (freePropagator system t ψ.1)) t
    rw [hasDerivAt_iff_tendsto]
    rw [hasDerivAt_iff_tendsto] at hderiv
    simpa [Function.comp_def, mul_apply_eq_comp] using hderiv
  simpa [schrodingerGenerator, smul_apply] using hgenerator

/-- Explicit bounded Heisenberg equation
`dA_H/dt = (i/ℏ) [H₀, A_H]`. -/
theorem heisenbergEquation (A : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (heisenbergEvolution system A)
      ((Complex.I / (system.hbar : ℂ)) •
        (system.hamiltonian.1 * heisenbergEvolution system A t -
          heisenbergEvolution system A t * system.hamiltonian.1)) t := by
  let G := schrodingerGenerator system
  let U := freePropagator system t
  let Uneg := freePropagator system (-t)
  have hleft := (hasDerivAt_freePropagator_neg system t).mul_const A
  have hprod := hleft.mul (hasDerivAt_freePropagator system t)
  have hraw : HasDerivAt (heisenbergEvolution system A)
      ((-G) * Uneg * A * U + Uneg * A * (G * U)) t := by
    rw [hasDerivAt_iff_tendsto]
    rw [hasDerivAt_iff_tendsto] at hprod
    simpa [G, U, Uneg, heisenbergEvolution, mul_assoc] using hprod
  have hcomm : Commute G U := by
    simpa [G, U] using schrodingerGenerator_commute_freePropagator system t
  have hderivRaw :
      ((-G) * Uneg * A * U + Uneg * A * (G * U)) =
        (Uneg * A * U) * G - G * (Uneg * A * U) := by
    rw [hcomm.eq]
    noncomm_ring
  have hgenerator :
      HasDerivAt (heisenbergEvolution system A)
        (heisenbergEvolution system A t * schrodingerGenerator system -
          schrodingerGenerator system * heisenbergEvolution system A t) t := by
    have hderiv :
        ((-G) * Uneg * A * U + Uneg * A * (G * U)) =
          heisenbergEvolution system A t * G -
            G * heisenbergEvolution system A t := by
      simpa [G, U, Uneg, heisenbergEvolution] using hderivRaw
    rw [← hderiv]
    exact hraw
  have hderiv :
      heisenbergEvolution system A t * schrodingerGenerator system -
          schrodingerGenerator system * heisenbergEvolution system A t =
        (Complex.I / (system.hbar : ℂ)) •
          (system.hamiltonian.1 * heisenbergEvolution system A t -
            heisenbergEvolution system A t * system.hamiltonian.1) := by
    rw [schrodingerGenerator]
    simp only [mul_smul_comm, smul_mul_assoc]
    module
  rw [← hderiv]
  exact hgenerator

/-- Explicit bounded von Neumann equation
`dρ/dt = -(i/ℏ) [H₀, ρ]`. -/
theorem vonNeumannEquation (ρ : DensityOperator H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveDensityOperator system ρ s).op)
      ((-(Complex.I / (system.hbar : ℂ))) •
        (system.hamiltonian.1 * (evolveDensityOperator system ρ t).op -
          (evolveDensityOperator system ρ t).op * system.hamiltonian.1)) t := by
  have h := (heisenbergEquation system ρ.op (-t)).scomp t (hasDerivAt_neg t)
  have hevolved (s : ℝ) :
      heisenbergEvolution system ρ.op (-s) = (evolveDensityOperator system ρ s).op := by
    simp [evolveDensityOperator_op, unitaryConjugate, heisenbergEvolution,
      star_freePropagator]
  rw [show (heisenbergEvolution system ρ.op ∘ Neg.neg) =
      fun s : ℝ => (evolveDensityOperator system ρ s).op by
        funext s
        exact hevolved s] at h
  rw [hevolved t] at h
  simpa using h

end
end LinearResponse
end QuantumTheory
