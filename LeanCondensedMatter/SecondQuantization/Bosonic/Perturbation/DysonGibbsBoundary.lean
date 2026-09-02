import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs

set_option linter.style.header false

/-!
# Convergence-aware Gibbs boundary for bosonic Dyson coefficients

Finite reachable support makes every matrix coefficient of `Common.dysonCoeff` continuous and
interval-integrable on the genuinely infinite bosonic occupation space. That coefficientwise fact
is not enough to move the normalized Gibbs expectation through the recursive Dyson integral: the
Gibbs numerator is an infinite occupation sum.

This module records the missing analytic obligations explicitly. It does not prove them from
coefficientwise continuity and it does not introduce a false finite occupation basis. A future
quartic Dyson/partition-function theorem can consume this boundary together with the existing Wick
and ordered-simplex diagram layers.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Analytic data needed to evaluate the arbitrary-configuration finite-order Dyson recursion in the
convergence-aware free bosonic Gibbs functional.

`coeff_mem` is summability of every finite-order Dyson coefficient. `integrand_mem` is the explicit
product/domain closure needed by the recursive integrand. `expectation_succ` is the nontrivial
interchange of the infinite Gibbs numerator with the recursive scalar interval integral. -/
structure FreeGibbsDysonIntegralBoundary
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) where
  /-- Every finite-order Dyson coefficient has a summable free Gibbs numerator. -/
  coeff_mem : ∀ (order : ℕ) (t : ℝ),
    Common.dysonCoeff (freeEigenvalue ε) V order t ∈ freeGibbsDomain ε β
  /-- The operator product occurring in the Dyson recursion stays in the Gibbs domain. -/
  integrand_mem : ∀ (order : ℕ) (σ : ℝ),
    (interactionPicture ε V σ).comp
        (Common.dysonCoeff (freeEigenvalue ε) V order σ) ∈ freeGibbsDomain ε β
  /-- The normalized Gibbs expectation commutes with the recursive Dyson interval integral. -/
  expectation_succ : ∀ (order : ℕ) (t : ℝ),
    freeGibbsExpectation ε β
        (Common.dysonCoeff (freeEigenvalue ε) V (order + 1) t) =
      - ∫ σ in (0 : ℝ)..t,
          freeGibbsExpectation ε β
            ((interactionPicture ε V σ).comp
              (Common.dysonCoeff (freeEigenvalue ε) V order σ))

/-- Normalized free Gibbs expectation of an arbitrary-configuration finite-order Dyson coefficient.
The definition itself is algebraic; physical use should provide `FreeGibbsDysonIntegralBoundary`
when recursive integration is involved. -/
noncomputable def freeGibbsDysonCoeff
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (order : ℕ) (t : ℝ) : ℂ :=
  freeGibbsExpectation ε β (Common.dysonCoeff (freeEigenvalue ε) V order t)

set_option linter.unusedFintypeInType false in
/-- The zeroth normalized bosonic Dyson coefficient is one under the explicit positive Gibbs
hypothesis. The finite mode instance is used in the summability proof behind
`freeGibbsExpectation_id`, although it is not syntactically visible in the conclusion. -/
@[simp]
theorem freeGibbsDysonCoeff_zero
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (t : ℝ) :
    freeGibbsDysonCoeff ε β V 0 t = 1 := by
  rw [freeGibbsDysonCoeff, Common.dysonCoeff_zero]
  exact freeGibbsExpectation_id ε β hpos

omit [Fintype Mode] in
/-- Under the explicit analytic boundary, the Gibbs-evaluated Dyson coefficient obeys the expected
recursive scalar integral equation. -/
theorem freeGibbsDysonCoeff_succ
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (H : FreeGibbsDysonIntegralBoundary ε β V)
    (order : ℕ) (t : ℝ) :
    freeGibbsDysonCoeff ε β V (order + 1) t =
      - ∫ σ in (0 : ℝ)..t,
          freeGibbsExpectation ε β
            ((interactionPicture ε V σ).comp
              (Common.dysonCoeff (freeEigenvalue ε) V order σ)) :=
  H.expectation_succ order t

end
end Bosonic
end SecondQuantization
