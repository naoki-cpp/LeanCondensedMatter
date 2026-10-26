import LeanCondensedMatter.QuantumTheory.DensityOperator.DiagonalFormula
import LeanCondensedMatter.QuantumTheory.LinearResponse.Expectation.Density
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.RetardedSusceptibility
import Mathlib.Analysis.InnerProductSpace.Continuous

set_option linter.style.header false

/-!
# Scalar response continuity for diagonal density states

Strong continuity of the supplied unitary group suffices for continuity of the scalar commutator
kernel of bounded observables in a density state diagonal in a Hilbert basis. Summable density
weights control the series uniformly. No operator-norm continuity of the observable orbit is used.
-/

namespace QuantumTheory.LinearResponse

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Strongly continuous unitary dynamics give a continuous scalar susceptibility in a diagonal
density state. No stationarity assumption is needed for the kernel with second time fixed at zero. -/
theorem continuous_commutatorSusceptibility_of_diagonal_density
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H)) (hbar : ℝ)
    (ρ : DensityOperator H) (b : HilbertBasis ι ℂ H) (w : ι → ℝ)
    (hρ : ∀ i, ρ.op (b i) = (w i : ℂ) • b i)
    (hU : ∀ x : H, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (A B : H →L[ℂ] H) :
    Continuous (fun t : ℝ =>
      commutatorSusceptibility U hbar ρ.toNormalizedExpectation A B t 0) := by
  have hcoeff (i : ι) : Continuous (fun t : ℝ =>
      inner ℂ (b i) (⁅heisenbergEvolution U t A, B⁆ (b i))) := by
    have hleft := (hU (b i)).inner (𝕜 := ℂ) (A.continuous.comp (hU (B (b i))))
    have hright := (hU ((star B) (b i))).inner (𝕜 := ℂ) (A.continuous.comp (hU (b i)))
    convert hleft.sub hright using 1
    funext t
    simp only [Pi.sub_apply, Function.comp_apply,
      LieRing.of_associative_ring_bracket, ContinuousLinearMap.sub_apply,
      inner_sub_right, heisenbergEvolution_apply, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint]
    rw [ContinuousLinearMap.adjoint_inner_right,
      ← ContinuousLinearMap.adjoint_inner_left B, ContinuousLinearMap.adjoint_inner_right]
  have hexpect := ρ.continuous_expectation_of_diagonal b w hρ
    (fun t : ℝ => ⁅heisenbergEvolution U t A, B⁆) (2 * ‖A‖ * ‖B‖)
    (fun t => by simpa only [heisenbergEvolution_zero] using
      norm_lie_heisenbergEvolution_le U A B t 0) hcoeff
  convert (continuous_const : Continuous (fun _ : ℝ => Complex.I / (hbar : ℂ))).mul
    hexpect using 1
  funext t
  simp only [Pi.mul_apply, commutatorSusceptibility, heisenbergEvolution_zero,
    DensityOperator.toNormalizedExpectation_apply]

end

end QuantumTheory.LinearResponse
