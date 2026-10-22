import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.PictureEquivalence
import LeanCondensedMatter.Analysis.Calculus.ExponentialConjugation
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Algebra.Lie.OfAssociative

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

attribute [local instance 100] LieRing.ofAssociativeRing

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
  simpa only [freePropagator, Complex.coe_smul] using h

/-- Explicit bounded Schrödinger equation
`dψ/dt = -(i/ℏ) H₀ ψ`. -/
theorem schrodingerEquation (ψ : StateVector H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveState system ψ s).1)
      ((-(Complex.I / (system.hbar : ℂ))) •
        system.hamiltonian.1 ((evolveState system ψ t).1)) t := by
  let evaluation := (ContinuousLinearMap.apply ℂ H ψ.1).restrictScalars ℝ
  have h := evaluation.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_freePropagator system t)
  simpa [evaluation, Function.comp_def, evolveState, schrodingerGenerator, mul_apply_eq_comp,
    smul_apply] using h

/-- Explicit bounded Heisenberg equation
`dA_H/dt = (i/ℏ) [H₀, A_H]`. -/
theorem heisenbergEquation (A : H →L[ℂ] H) (t : ℝ) :
    HasDerivAt (fun t => heisenbergEvolution system t A)
      ((Complex.I / (system.hbar : ℂ)) •
        ⁅system.hamiltonian.1, heisenbergEvolution system t A⁆) t := by
  have h := hasDerivAt_exp_conjugate (-schrodingerGenerator system) A t
  have hfun (s : ℝ) :
      NormedSpace.exp (s • (-schrodingerGenerator system)) * A *
          NormedSpace.exp (-(s • (-schrodingerGenerator system))) =
        heisenbergEvolution system s A := by
    simp only [heisenbergEvolution_apply, freePropagator, Complex.coe_smul,
      smul_neg, neg_smul, neg_neg]
  have hderiv :
      (-schrodingerGenerator system) * heisenbergEvolution system t A -
          heisenbergEvolution system t A * (-schrodingerGenerator system) =
        (Complex.I / (system.hbar : ℂ)) •
          ⁅system.hamiltonian.1, heisenbergEvolution system t A⁆ := by
    rw [LieRing.of_associative_ring_bracket, schrodingerGenerator]
    simp only [neg_smul, neg_neg, mul_smul_comm, smul_mul_assoc]
    module
  rw [hasDerivAt_iff_tendsto] at h ⊢
  simpa only [hfun, hderiv] using h

/-- Explicit bounded von Neumann equation
`dρ/dt = -(i/ℏ) [H₀, ρ]`. -/
theorem vonNeumannEquation (ρ : DensityOperator H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (evolveDensityOperator system ρ s).op)
      ((-(Complex.I / (system.hbar : ℂ))) •
        ⁅system.hamiltonian.1, (evolveDensityOperator system ρ t).op⁆) t := by
  have h := (heisenbergEquation system ρ.op (-t)).scomp t (hasDerivAt_neg t)
  have hevolved (s : ℝ) :
      heisenbergEvolution system (-s) ρ.op = (evolveDensityOperator system ρ s).op := by
    simp [evolveDensityOperator_op, adjointConjugate, heisenbergEvolution_apply,
      star_freePropagator]
  rw [show ((fun t => heisenbergEvolution system t ρ.op) ∘ Neg.neg) =
      fun s : ℝ => (evolveDensityOperator system ρ s).op by
        funext s
        exact hevolved s] at h
  rw [hevolved t] at h
  simpa [LieRing.of_associative_ring_bracket] using h

end
end LinearResponse
end QuantumTheory
