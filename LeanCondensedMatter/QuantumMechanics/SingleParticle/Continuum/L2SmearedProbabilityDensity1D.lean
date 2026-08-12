import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.L2Multiplication1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.SchrodingerContinuityCompactSupport1D
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `L²` expectations and smeared probability density in one dimension

This module connects the bounded `L²` multiplication-operator layer to the whole-space smeared
probability density used by the continuum continuity equation. A real test function is embedded in
`ℂ` and supplied with an explicit `L∞` hypothesis, producing a bounded multiplication operator on
`L²(ℝ, ℂ)`. Its expectation is then exactly the complexification of
`∫ test(x) |ψ(x)|² dx`.

This is still a bounded-observable statement. No Laplacian, Schrödinger Hamiltonian, Sobolev domain,
or unbounded-operator assertion is introduced here.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace

/-- A real test function, embedded into `ℂ`, as an essentially bounded multiplier. -/
noncomputable def realTestMultiplier1D
    (test : ℝ → ℝ)
    (htest : MemLp (fun x => (test x : ℂ)) ∞ (volume : Measure ℝ)) :
    ContinuumLInfMultiplier1D :=
  htest.toLp (fun x => (test x : ℂ))

/-- The `L∞` representative chosen for a real test function agrees almost everywhere with its
pointwise complex embedding. -/
theorem realTestMultiplier1D_coeFn
    (test : ℝ → ℝ)
    (htest : MemLp (fun x => (test x : ℂ)) ∞ (volume : Measure ℝ)) :
    (realTestMultiplier1D test htest : ℝ → ℂ) =ᵐ[volume]
      fun x => (test x : ℂ) := by
  exact htest.coeFn_toLp

private theorem inner_real_mul_self_eq_probabilityDensityValue (r : ℝ) (z : ℂ) :
    inner ℂ z ((r : ℂ) * z) = (r * probabilityDensityValue z : ℂ) := by
  rw [probabilityDensityValue]
  rw [Complex.normSq_eq_conj_mul_self]
  simp [mul_assoc, mul_left_comm, mul_comm]

/-- The expectation of multiplication by a bounded real test function is the complexification of
its whole-space smeared probability density:

`⟪ψ, M_test ψ⟫ = ∫ test(x) |ψ(x)|² dx`.

The `MemLp ... ∞` hypothesis is the explicit boundedness condition needed to make `M_test` a bounded
operator on all of `L²`. -/
theorem inner_realTestMultiplicationOperator1D_eq_wholeSpaceSmearedProbabilityDensity1D
    (test : ℝ → ℝ)
    (htest : MemLp (fun x => (test x : ℂ)) ∞ (volume : Measure ℝ))
    (ψ : ContinuumL2Wavefunction1D) :
    inner ℂ ψ (l2MultiplicationOperator1D (realTestMultiplier1D test htest) ψ) =
      (wholeSpaceSmearedProbabilityDensity1D test (fun x => ψ x) : ℂ) := by
  rw [inner_l2MultiplicationOperator1D_eq_integral]
  unfold wholeSpaceSmearedProbabilityDensity1D
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [realTestMultiplier1D_coeFn test htest] with x hx
  rw [hx]
  simpa using inner_real_mul_self_eq_probabilityDensityValue (test x) (ψ x)

end
end Continuum
end SingleParticle
end QuantumMechanics
