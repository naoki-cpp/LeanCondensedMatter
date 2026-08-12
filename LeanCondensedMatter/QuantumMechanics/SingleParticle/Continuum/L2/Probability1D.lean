import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.L2.Multiplication1D
import LeanCondensedMatter.QuantumMechanics.SingleParticle.Continuum.ProbabilityIntegral1D
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `L²` probability bridges in one dimension

This module connects integrated pointwise probability quantities to their canonical `L²`
realization.  It owns two dynamics-independent bridges:

* total probability is the squared `L²` norm;
* expectation of a bounded real multiplication operator is the corresponding smeared probability.

The Schwartz-to-`L²` specialization also lives here, below any conservation or evolution theorem.
No Laplacian, Schrödinger Hamiltonian, Sobolev domain, or dynamics is introduced here.
-/

namespace QuantumMechanics
namespace SingleParticle
namespace Continuum

noncomputable section

open MeasureTheory
open scoped ENNReal MeasureTheory InnerProductSpace SchwartzMap

private theorem inner_self_complex_eq_probabilityDensityValue (z : ℂ) :
    inner ℂ z z = (probabilityDensityValue z : ℂ) := by
  rw [probabilityDensityValue]
  rw [inner_self_eq_norm_sq_to_K, pow_two]
  change Complex.ofReal ‖z‖ * Complex.ofReal ‖z‖ =
    Complex.ofReal (Complex.normSq z)
  calc
    Complex.ofReal ‖z‖ * Complex.ofReal ‖z‖ =
        Complex.ofReal (‖z‖ * ‖z‖) := (Complex.ofReal_mul _ _).symm
    _ = Complex.ofReal (Complex.normSq z) :=
      congrArg Complex.ofReal (Complex.norm_mul_self_eq_normSq z)

/-- The whole-space probability integral of the canonical representative of an `L²` wavefunction
is its squared Hilbert norm. -/
theorem totalProbability1D_l2_coe_eq_norm_sq (ψ : ContinuumL2Wavefunction1D) :
    totalProbability1D (fun x => ψ x) = ‖ψ‖ ^ 2 := by
  have hinner :
      inner ℂ ψ ψ = (totalProbability1D (fun x => ψ x) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    unfold totalProbability1D
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x =>
      inner_self_complex_eq_probabilityDensityValue (ψ x)
  have hnorm : inner ℂ ψ ψ = ((‖ψ‖ ^ 2 : ℝ) : ℂ) := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ)
  apply Complex.ofReal_injective
  exact hinner.symm.trans hnorm

/-- For a Schwartz wavefunction, the pointwise probability integral is exactly the squared norm of
its canonical `L²` image. -/
theorem totalProbability1D_schwartz_eq_toLp_norm_sq (ψ : SchwartzMap ℝ ℂ) :
    totalProbability1D (fun x => ψ x) =
      ‖ψ.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  calc
    totalProbability1D (fun x => ψ x) =
        totalProbability1D (fun x => ψ.toLp 2 (volume : Measure ℝ) x) := by
      unfold totalProbability1D
      apply integral_congr_ae
      filter_upwards [SchwartzMap.coeFn_toLp ψ 2 (volume : Measure ℝ)] with x hx
      rw [hx]
    _ = ‖ψ.toLp 2 (volume : Measure ℝ)‖ ^ 2 :=
      totalProbability1D_l2_coe_eq_norm_sq (ψ.toLp 2 (volume : Measure ℝ))

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
    inner ℂ ψ (l2MultiplicationOperator1D (realLInfMultiplier1D test htest) ψ) =
      (wholeSpaceSmearedProbabilityDensity1D test (fun x => ψ x) : ℂ) := by
  rw [inner_l2MultiplicationOperator1D_eq_integral]
  unfold wholeSpaceSmearedProbabilityDensity1D
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [realLInfMultiplier1D_coeFn test htest] with x hx
  rw [hx]
  simpa using inner_real_mul_self_eq_probabilityDensityValue (test x) (ψ x)

end
end Continuum
end SingleParticle
end QuantumMechanics
