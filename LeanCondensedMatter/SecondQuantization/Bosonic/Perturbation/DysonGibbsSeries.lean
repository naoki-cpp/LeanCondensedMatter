import LeanCondensedMatter.Analysis.PowerSeries.LogAlgebra
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs

set_option linter.style.header false

/-!
# Bosonic Dyson Gibbs formal series

A finite-order physical-H bosonic Dyson coefficient can be evaluated in a convergence-aware
explicit-μ grand-canonical Gibbs
functional without asserting any all-order analytic convergence. This file packages those normalized
finite-order coefficients into a formal power series.

For quartic interactions, downstream diagrammatic theorems prove Gibbs-domain membership at every
finite Dyson order by expanding each coefficient into a finite sum of thermal-field products. No
interchange of an infinite Gibbs sum with the recursive operator-valued Dyson integral is built into
this definition.

Physical Dyson time evolution continues to use H, while the thermal weighting uses K = H - μN.
Unlike finite-dimensional fermionic trace series, no interacting bosonic partition function or
analytic convergence statement is asserted here.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- Grand-canonical expectation of a physical-H Dyson coefficient at explicit chemical potential. -/
noncomputable def grandCanonicalGibbsDysonCoeff
    (ε : Mode → ℝ) (β μ : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (order : ℕ) (t : ℝ) : ℂ :=
  freeGibbsExpectation (fun i => ε i - μ) β
    (Common.dysonCoeff (freeEigenvalue ε) V order t)

set_option linter.unusedFintypeInType false in
/-- The zeroth grand-canonical bosonic Dyson coefficient is one under the explicit positive Gibbs
hypothesis. -/
@[simp]
theorem grandCanonicalGibbsDysonCoeff_zero [Fintype Mode]
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (t : ℝ) :
    grandCanonicalGibbsDysonCoeff ε β μ V 0 t = 1 := by
  rw [grandCanonicalGibbsDysonCoeff, Common.dysonCoeff_zero]
  exact freeGibbsExpectation_id (fun i => ε i - μ) β hpos

/-- Formal series whose coefficients are the convergence-aware normalized free-Gibbs Dyson
coefficients evaluated at imaginary time `β` and explicit chemical potential `μ`. -/
noncomputable def grandCanonicalGibbsDysonSeries
    (ε : Mode → ℝ) (β μ : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) : PowerSeries ℂ :=
  PowerSeries.mk fun n => grandCanonicalGibbsDysonCoeff ε β μ V n β

@[simp]
theorem coeff_grandCanonicalGibbsDysonSeries
    (ε : Mode → ℝ) (β μ : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (n : ℕ) :
    PowerSeries.coeff n (grandCanonicalGibbsDysonSeries ε β μ V) =
      grandCanonicalGibbsDysonCoeff ε β μ V n β := by
  simp [grandCanonicalGibbsDysonSeries]

set_option linter.unusedFintypeInType false in
/-- Under the positive free-Gibbs hypothesis, the physical bosonic Dyson series has unit constant
coefficient. The finite mode instance enters through the Gibbs summability theorem used at zeroth
order. -/
theorem constantCoeff_grandCanonicalGibbsDysonSeries
    [Fintype Mode]
    (ε : Mode → ℝ) (β μ : ℝ) (hpos : ∀ i, 0 < β * (ε i - μ))
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    PowerSeries.constantCoeff (grandCanonicalGibbsDysonSeries ε β μ V) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_grandCanonicalGibbsDysonSeries]
  exact grandCanonicalGibbsDysonCoeff_zero ε β μ hpos V β

/-- Formal logarithm of the normalized physical bosonic Dyson series. This is purely coefficientwise;
it does not assert convergence to an interacting bosonic partition function. -/
noncomputable def grandCanonicalGibbsDysonFormalLog
    (ε : Mode → ℝ) (β μ : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) : PowerSeries ℂ :=
  PowerSeries.logOf (grandCanonicalGibbsDysonSeries ε β μ V)

end
end Bosonic
end SecondQuantization
