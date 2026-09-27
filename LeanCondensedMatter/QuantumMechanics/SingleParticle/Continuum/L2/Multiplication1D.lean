import LeanCondensedMatter.Analysis.Operator.L2Multiplication
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option linter.style.header false

/-!
# Bounded multiplication operators on one-dimensional continuum `L²`

This module specializes the measure-space-independent multiplication-operator infrastructure from
`Analysis.Operator.L2Multiplication` to Lebesgue measure on `ℝ`. The names here retain the
continuum quantum-mechanics vocabulary used by the Hamiltonian and probability layers.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- Complex one-dimensional square-integrable wavefunctions. -/
abbrev ContinuumL2Wavefunction1D := L2Multiplication.ComplexL2 (volume : Measure ℝ)

/-- Essentially bounded complex multipliers on one-dimensional space. -/
abbrev ContinuumLInfMultiplier1D := L2Multiplication.ComplexLInf (volume : Measure ℝ)

/-- Multiplication by an `L∞` function as a bounded operator on continuum `L²`. -/
noncomputable abbrev l2MultiplicationOperator1D
    (f : ContinuumLInfMultiplier1D) :
    ContinuumL2Wavefunction1D →L[ℂ] ContinuumL2Wavefunction1D :=
  L2Multiplication.multiplicationOperator (volume : Measure ℝ) f

@[simp]
theorem l2MultiplicationOperator1D_apply
    (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    l2MultiplicationOperator1D f ψ = (f • ψ : ContinuumL2Wavefunction1D) := by
  exact L2Multiplication.multiplicationOperator_apply (volume : Measure ℝ) f ψ

/-- The `L²` expectation of a bounded multiplication operator is the Lebesgue integral of the
pointwise inner-product density. -/
theorem inner_l2MultiplicationOperator1D_eq_integral
    (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    inner ℂ ψ (l2MultiplicationOperator1D f ψ) =
      ∫ x : ℝ, inner ℂ (ψ x) (f x * ψ x) := by
  exact L2Multiplication.inner_multiplicationOperator_eq_integral (volume : Measure ℝ) f ψ

/-- A real essentially bounded function, embedded into `ℂ`, as an `L∞` multiplier. -/
noncomputable abbrev realLInfMultiplier1D
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ)) :
    ContinuumLInfMultiplier1D :=
  L2Multiplication.realMultiplier (volume : Measure ℝ) f hf

/-- The `L∞` representative chosen for a real bounded function agrees almost everywhere with its
pointwise complex embedding. -/
theorem realLInfMultiplier1D_coeFn
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ)) :
    (realLInfMultiplier1D f hf : ℝ → ℂ) =ᵐ[volume]
      fun x => (f x : ℂ) := by
  exact L2Multiplication.realMultiplier_coeFn (volume : Measure ℝ) f hf

/-- Multiplication by a bounded real function is symmetric on one-dimensional continuum `L²`. -/
theorem realL2MultiplicationOperator1D_symmetric
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ))
    (ψ φ : ContinuumL2Wavefunction1D) :
    inner ℂ (l2MultiplicationOperator1D (realLInfMultiplier1D f hf) ψ) φ =
      inner ℂ ψ (l2MultiplicationOperator1D (realLInfMultiplier1D f hf) φ) := by
  exact L2Multiplication.realMultiplicationOperator_symmetric
    (volume : Measure ℝ) f hf ψ φ

end
end Continuum
end SingleParticle
end QuantumMechanics
