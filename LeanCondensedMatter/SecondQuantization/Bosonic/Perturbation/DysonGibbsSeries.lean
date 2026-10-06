import LeanCondensedMatter.Analysis.PowerSeries.LogAlgebra
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.ConvergenceAwareGibbs

set_option linter.style.header false

/-!
# Bosonic Dyson Gibbs formal series

A finite-order bosonic Dyson coefficient can be evaluated in the convergence-aware free Gibbs
functional without asserting any all-order analytic convergence. This file packages those normalized
finite-order coefficients into a formal power series.

For quartic interactions, downstream diagrammatic theorems prove Gibbs-domain membership at every
finite Dyson order by expanding each coefficient into a finite sum of thermal-field products. No
interchange of an infinite Gibbs sum with the recursive operator-valued Dyson integral is built into
this definition.

Unlike the finite-dimensional fermionic trace series, no interacting bosonic partition function or
analytic convergence statement is asserted here.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*}

/-- Normalized free Gibbs expectation of an arbitrary-configuration finite-order Dyson coefficient. -/
noncomputable def freeGibbsDysonCoeff
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (order : ℕ) (t : ℝ) : ℂ :=
  freeGibbsExpectation ε β (Common.dysonCoeff (freeEigenvalue ε) V order t)

set_option linter.unusedFintypeInType false in
/-- The zeroth normalized bosonic Dyson coefficient is one under the explicit positive Gibbs
hypothesis. -/
@[simp]
theorem freeGibbsDysonCoeff_zero [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (t : ℝ) :
    freeGibbsDysonCoeff ε β V 0 t = 1 := by
  rw [freeGibbsDysonCoeff, Common.dysonCoeff_zero]
  exact freeGibbsExpectation_id ε β hpos

/-- Formal series whose coefficients are the convergence-aware normalized free-Gibbs Dyson
coefficients evaluated at imaginary time `β`. -/
noncomputable def freeGibbsDysonSeries
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) : PowerSeries ℂ :=
  PowerSeries.mk fun n => freeGibbsDysonCoeff ε β V n β

@[simp]
theorem coeff_freeGibbsDysonSeries
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) (n : ℕ) :
    PowerSeries.coeff n (freeGibbsDysonSeries ε β V) =
      freeGibbsDysonCoeff ε β V n β := by
  simp [freeGibbsDysonSeries]

set_option linter.unusedFintypeInType false in
/-- Under the positive free-Gibbs hypothesis, the physical bosonic Dyson series has unit constant
coefficient. The finite mode instance enters through the Gibbs summability theorem used at zeroth
order. -/
theorem constantCoeff_freeGibbsDysonSeries
    [Fintype Mode]
    (ε : Mode → ℝ) (β : ℝ) (hpos : ∀ i, 0 < β * ε i)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    PowerSeries.constantCoeff (freeGibbsDysonSeries ε β V) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_freeGibbsDysonSeries]
  exact freeGibbsDysonCoeff_zero ε β hpos V β

/-- Formal logarithm of the normalized physical bosonic Dyson series. This is purely coefficientwise;
it does not assert convergence to an interacting bosonic partition function. -/
noncomputable def freeGibbsDysonFormalLog
    (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpace Mode →ₗ[ℂ] FockSpace Mode) : PowerSeries ℂ :=
  PowerSeries.logOf (freeGibbsDysonSeries ε β V)

end
end Bosonic
end SecondQuantization
