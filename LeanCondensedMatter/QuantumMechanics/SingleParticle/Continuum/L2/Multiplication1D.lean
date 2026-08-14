import LeanCondensedMatter.Analysis.Operator.L2MultiplicationRealLine

set_option linter.style.header false

/-!
# Bounded multiplication operators on one-dimensional continuum `L²`

This module is the quantum-mechanics specialization of the analysis-level real-line multiplication
operator infrastructure. The canonical `L²(ℝ, ℂ)` and `L∞(ℝ, ℂ)` realizations and all bounded
operator facts are owned by `Analysis.Operator.L2MultiplicationRealLine`; the names here retain the
continuum quantum-mechanics vocabulary used by the Hamiltonian and probability layers.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- Complex one-dimensional square-integrable wavefunctions. -/
abbrev ContinuumL2Wavefunction1D := L2MultiplicationRealLine.ComplexL2

/-- Essentially bounded complex multipliers on one-dimensional space. -/
abbrev ContinuumLInfMultiplier1D := L2MultiplicationRealLine.ComplexLInf

/-- Multiplication by an `L∞` function as a bounded operator on continuum `L²`. -/
noncomputable def l2MultiplicationOperator1D
    (f : ContinuumLInfMultiplier1D) :
    ContinuumL2Wavefunction1D →L[ℂ] ContinuumL2Wavefunction1D :=
  L2MultiplicationRealLine.multiplicationOperator f

@[simp]
theorem l2MultiplicationOperator1D_apply
    (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    l2MultiplicationOperator1D f ψ = (f • ψ : ContinuumL2Wavefunction1D) := by
  exact L2MultiplicationRealLine.multiplicationOperator_apply f ψ

/-- The multiplication operator has operator norm at most the `L∞` norm of its multiplier. -/
theorem l2MultiplicationOperator1D_norm_le
    (f : ContinuumLInfMultiplier1D) :
    ‖l2MultiplicationOperator1D f‖ ≤ ‖f‖ := by
  exact L2MultiplicationRealLine.multiplicationOperator_norm_le f

/-- The bounded `L²` multiplication operator agrees almost everywhere with pointwise
multiplication of representatives. -/
theorem l2MultiplicationOperator1D_coeFn
    (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    (l2MultiplicationOperator1D f ψ : ℝ → ℂ) =ᵐ[volume]
      fun x => f x * ψ x := by
  exact L2MultiplicationRealLine.multiplicationOperator_coeFn f ψ

/-- The `L²` expectation of a bounded multiplication operator is the Lebesgue integral of the
pointwise inner-product density. -/
theorem inner_l2MultiplicationOperator1D_eq_integral
    (f : ContinuumLInfMultiplier1D) (ψ : ContinuumL2Wavefunction1D) :
    inner ℂ ψ (l2MultiplicationOperator1D f ψ) =
      ∫ x : ℝ, inner ℂ (ψ x) (f x * ψ x) := by
  exact L2MultiplicationRealLine.inner_multiplicationOperator_eq_integral f ψ

/-- A real essentially bounded function, embedded into `ℂ`, as an `L∞` multiplier. -/
noncomputable def realLInfMultiplier1D
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ)) :
    ContinuumLInfMultiplier1D :=
  L2MultiplicationRealLine.realMultiplier f hf

/-- The `L∞` representative chosen for a real bounded function agrees almost everywhere with its
pointwise complex embedding. -/
theorem realLInfMultiplier1D_coeFn
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ)) :
    (realLInfMultiplier1D f hf : ℝ → ℂ) =ᵐ[volume]
      fun x => (f x : ℂ) := by
  exact L2MultiplicationRealLine.realMultiplier_coeFn f hf

/-- Multiplication by a bounded real function is symmetric on `L²(ℝ, ℂ)`. -/
theorem l2RealMultiplicationOperator1D_symmetric
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ))
    (ψ φ : ContinuumL2Wavefunction1D) :
    inner ℂ
        (l2MultiplicationOperator1D (realLInfMultiplier1D f hf) ψ) φ =
      inner ℂ ψ
        (l2MultiplicationOperator1D (realLInfMultiplier1D f hf) φ) := by
  exact L2MultiplicationRealLine.realMultiplicationOperator_symmetric f hf ψ φ

/-- A bounded real multiplication operator, viewed as a partial operator with full domain, is a
formal adjoint of itself. -/
theorem l2RealMultiplicationOperator1D_isFormalAdjoint
    (f : ℝ → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) ∞ (volume : Measure ℝ)) :
    let M := l2MultiplicationOperator1D (realLInfMultiplier1D f hf)
    (M.toPMap ⊤).IsFormalAdjoint (M.toPMap ⊤) := by
  exact L2MultiplicationRealLine.realMultiplicationOperator_isFormalAdjoint f hf

end
end Continuum
end SingleParticle
end QuantumMechanics
