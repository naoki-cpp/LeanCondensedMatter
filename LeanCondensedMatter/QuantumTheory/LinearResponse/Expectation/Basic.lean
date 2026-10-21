import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.header false

/-!
# Normalized expectation functionals

This module owns the minimal normalized continuous expectation-functional interface used by bounded
linear response, together with its two-point connected correlation. It is independent of free
dynamics, propagators, ensembles, and Dyson-series infrastructure.

Positivity is intentionally not part of this interface: the algebraic linear-response arguments
only require a continuous linear functional normalized on the identity. Physical state and density
operator constructions may provide stronger properties in downstream modules.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A normalized continuous linear expectation functional on bounded operators.

Positivity is intentionally not part of this minimal interface: it is unnecessary for the
algebraic first derivative underlying the Kubo formula. -/
structure NormalizedExpectation (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- The underlying continuous linear functional on bounded operators. -/
  toContinuousLinearMap : (H →L[ℂ] H) →L[ℂ] ℂ
  map_one : toContinuousLinearMap 1 = 1

instance : CoeFun (NormalizedExpectation H) fun _ => (H →L[ℂ] H) → ℂ :=
  ⟨fun expectation => expectation.toContinuousLinearMap⟩

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

/-- Pull a normalized expectation back along a continuous linear operator map that preserves the
identity. No positivity or multiplicativity assumption is needed for this minimal linear-response
interface. -/
noncomputable def NormalizedExpectation.pullback
    (expectation : NormalizedExpectation K)
    (Φ : (H →L[ℂ] H) →L[ℂ] (K →L[ℂ] K))
    (hΦ : Φ 1 = 1) : NormalizedExpectation H where
  toContinuousLinearMap := expectation.toContinuousLinearMap.comp Φ
  map_one := by
    simpa [hΦ] using expectation.map_one

@[simp]
theorem NormalizedExpectation.pullback_apply
    (expectation : NormalizedExpectation K)
    (Φ : (H →L[ℂ] H) →L[ℂ] (K →L[ℂ] K))
    (hΦ : Φ 1 = 1) (A : H →L[ℂ] H) :
    expectation.pullback Φ hΦ A = expectation (Φ A) :=
  rfl

/-- The connected two-point correlation (second cumulant) of two bounded observables,
defined for any normalized continuous linear expectation. No Gibbs, KMS, or Gaussian
hypotheses are needed. The order of the operator product is retained. -/
noncomputable def NormalizedExpectation.connectedCorrelation
    (expectation : NormalizedExpectation H)
    (A B : H →L[ℂ] H) : ℂ :=
  expectation (A * B) - expectation A * expectation B

/-- The connected correlation with the identity in the first slot vanishes by normalization. -/
@[simp]
theorem NormalizedExpectation.connectedCorrelation_one_left
    (expectation : NormalizedExpectation H) (A : H →L[ℂ] H) :
    expectation.connectedCorrelation 1 A = 0 := by
  change expectation (1 * A) -
    expectation.toContinuousLinearMap 1 * expectation A = 0
  rw [one_mul, expectation.map_one]
  ring

/-- The connected correlation with the identity in the second slot vanishes by normalization. -/
@[simp]
theorem NormalizedExpectation.connectedCorrelation_one_right
    (expectation : NormalizedExpectation H) (A : H →L[ℂ] H) :
    expectation.connectedCorrelation A 1 = 0 := by
  change expectation (A * 1) -
    expectation A * expectation.toContinuousLinearMap 1 = 0
  rw [mul_one, expectation.map_one]
  ring

end
end LinearResponse
end QuantumTheory
