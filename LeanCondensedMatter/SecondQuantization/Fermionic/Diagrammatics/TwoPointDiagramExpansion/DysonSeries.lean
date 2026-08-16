import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.QuarticInteraction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

set_option linter.style.header false

/-!
# The perturbative two-point series

The order-`n` mixed time-ordered density-state coefficients of `DysonCoefficient.lean` are assembled
into a formal power series in the coupling. The coefficient-level diagram presentation remains the
bridge to finite diagram sums and factorization, so no parallel diagram-series API is maintained.

The series is divided by the partition series of the same interaction, normalized to constant
coefficient one. That division is what the linked-cluster theorem asks for: the coefficients are
already free Gibbs expectations, so only the interacting vacuum contributions remain to be
cancelled.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **The perturbative two-point series**, in the mixed time-ordered density-state presentation. -/
noncomputable def twoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => twoPointDysonCoefficient (n := n) ε β g i j τ τ'

@[simp]
theorem coeff_twoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    PowerSeries.coeff n (twoPointDysonSeries ε β g i j τ τ') =
      twoPointDysonCoefficient (n := n) ε β g i j τ τ' :=
  PowerSeries.coeff_mk n _

/-- **The vacuum-normalized two-point series**: the two-point series divided by the partition series
of the same interaction, normalized to constant coefficient one.

The division is by the *normalized* partition series because the two-point coefficients are already
free Gibbs **expectations** — the free partition function has been divided out of each of them, so
only the interacting vacuum contributions remain to be cancelled. -/
noncomputable def vacuumNormalizedTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  twoPointDysonSeries ε β g i j τ τ' *
    (PowerSeries.normalizeByConstantCoeff
      (dysonPartitionSeries ε β (quarticInteraction g)))⁻¹

end Fermionic
end SecondQuantization
