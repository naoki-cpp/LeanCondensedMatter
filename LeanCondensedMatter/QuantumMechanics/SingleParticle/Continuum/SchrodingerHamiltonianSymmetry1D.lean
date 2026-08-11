import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerHamiltonianClosedH21D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Symmetry ingredients for the one-dimensional Schrödinger Hamiltonian

This file starts the self-adjointness layer by isolating the bounded real-potential contribution.
Multiplication by a real essentially bounded function is symmetric on physical `L²(ℝ, ℂ)`.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

private theorem inner_real_mul_left_eq_inner_real_mul_right
    (r : ℝ) (z w : ℂ) :
    inner ℂ ((r : ℂ) * z) w = inner ℂ z ((r : ℂ) * w) := by
  simp [RCLike.inner_apply, mul_assoc, mul_comm]

/-- Multiplication by a bounded real function is symmetric on `L²(ℝ, ℂ)`. -/
theorem l2RealMultiplicationOperator1D_symmetric
    (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ))
    (ψ φ : ContinuumL2Wavefunction1D) :
    inner ℂ
        (l2MultiplicationOperator1D (realTestMultiplier1D potential hpotential) ψ) φ =
      inner ℂ ψ
        (l2MultiplicationOperator1D (realTestMultiplier1D potential hpotential) φ) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
      [l2MultiplicationOperator1D_coeFn (realTestMultiplier1D potential hpotential) ψ,
       l2MultiplicationOperator1D_coeFn (realTestMultiplier1D potential hpotential) φ,
       realTestMultiplier1D_coeFn potential hpotential] with x hψ hφ hpot
  rw [hψ, hφ, hpot]
  exact inner_real_mul_left_eq_inner_real_mul_right (potential x) (ψ x) (φ x)

/-- The real bounded multiplication operator, viewed as a partial operator with full domain,
 is a formal adjoint of itself. -/
theorem l2RealMultiplicationOperator1D_isFormalAdjoint
    (potential : ℝ → ℝ)
    (hpotential : MemLp (fun x => (potential x : ℂ)) ∞ (volume : Measure ℝ)) :
    let M := l2MultiplicationOperator1D (realTestMultiplier1D potential hpotential)
    (M.toPMap ⊤).IsFormalAdjoint (M.toPMap ⊤) := by
  dsimp
  intro ψ φ
  simpa using l2RealMultiplicationOperator1D_symmetric potential hpotential
    (ψ : ContinuumL2Wavefunction1D) (φ : ContinuumL2Wavefunction1D)

end
end Continuum
end SingleParticle
end QuantumMechanics
