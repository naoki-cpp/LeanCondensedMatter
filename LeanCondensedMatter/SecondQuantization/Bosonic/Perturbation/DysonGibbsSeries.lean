import LeanCondensedMatter.Analysis.PowerSeries.LogAlgebra
import LeanCondensedMatter.SecondQuantization.Bosonic.Perturbation.DysonGibbsBoundary

set_option linter.style.header false

/-!
# Bosonic Dyson Gibbs formal series

The convergence-aware bosonic Dyson coefficient is already normalized by the free Gibbs partition
function. This file packages those physical finite-order coefficients into a formal power series.
Unlike the finite-dimensional fermionic trace series, no interacting bosonic partition function or
analytic convergence statement is asserted here.
-/

namespace SecondQuantization
namespace Bosonic

noncomputable section

variable {Mode : Type*} [Fintype Mode]

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

/-- Under the positive free-Gibbs hypothesis, the physical bosonic Dyson series has unit constant
coefficient. -/
theorem constantCoeff_freeGibbsDysonSeries
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
