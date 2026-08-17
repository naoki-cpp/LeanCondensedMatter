import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.DysonCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.ConnectedCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.QuarticInteraction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

set_option linter.style.header false

/-!
# Perturbative two-point series

The order-`n` mixed time-ordered density-state coefficients of `DysonCoefficient.lean` are assembled
into formal power series in the coupling. The connected coefficient is owned by the integration
layer; this module only packages coefficient-level data into formal power series and performs vacuum
normalization.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **The perturbative two-point series**, in the mixed time-ordered density-state presentation. -/
noncomputable def twoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => twoPointDysonCoefficient (n := n) ε β g i j τ τ'

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

/-- **The connected perturbative two-point series.** -/
noncomputable def connectedTwoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (connectedTwoPointDysonCoefficient ε β g i j τ τ')

end Fermionic
end SecondQuantization
