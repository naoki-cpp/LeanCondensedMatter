import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option linter.style.header false

/-!
# Normalized expectation functionals

This module owns the minimal normalized continuous expectation-functional interface used by bounded
linear response. It is independent of free dynamics, propagators, and Dyson-series infrastructure.

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

@[simp]
theorem NormalizedExpectation.apply_one (expectation : NormalizedExpectation H) :
    expectation (1 : H →L[ℂ] H) = 1 :=
  expectation.map_one

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
    simp [hΦ]

@[simp]
theorem NormalizedExpectation.pullback_apply
    (expectation : NormalizedExpectation K)
    (Φ : (H →L[ℂ] H) →L[ℂ] (K →L[ℂ] K))
    (hΦ : Φ 1 = 1) (A : H →L[ℂ] H) :
    expectation.pullback Φ hΦ A = expectation (Φ A) :=
  rfl

end
end LinearResponse
end QuantumTheory
