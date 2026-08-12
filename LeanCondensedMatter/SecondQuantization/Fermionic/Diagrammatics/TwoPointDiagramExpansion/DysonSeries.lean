import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonCoefficient
import Mathlib.RingTheory.PowerSeries.Basic

set_option linter.style.header false

/-!
# The perturbative two-point series

The order-`n` two-point coefficients of `DysonCoefficient.lean` are assembled into formal power
series in the coupling, one for each presentation: the diagram sum and the mixed time-ordered
density-state expectation. They are the same series, because the two coefficients agree at every
order.

This is the series the linked-cluster theorem divides by the partition series; collecting the
coefficients here keeps that division a statement about power series rather than about a family of
integrals.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The perturbative two-point series in the diagram-sum presentation. -/
noncomputable def twoPointDiagramSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => twoPointDiagramCoefficient (n := n) ε β g i j τ τ'

/-- **The perturbative two-point series**, in the mixed time-ordered density-state presentation. -/
noncomputable def twoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => twoPointDysonCoefficient (n := n) ε β g i j τ τ'

@[simp]
theorem coeff_twoPointDiagramSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    PowerSeries.coeff n (twoPointDiagramSeries ε β g i j τ τ') =
      twoPointDiagramCoefficient (n := n) ε β g i j τ τ' :=
  PowerSeries.coeff_mk n _

@[simp]
theorem coeff_twoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    PowerSeries.coeff n (twoPointDysonSeries ε β g i j τ τ') =
      twoPointDysonCoefficient (n := n) ε β g i j τ τ' :=
  PowerSeries.coeff_mk n _

/-- **The two presentations are the same series.** -/
theorem twoPointDiagramSeries_eq_twoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    twoPointDiagramSeries ε β g i j τ τ' = twoPointDysonSeries ε β g i j τ τ' := by
  ext n
  rw [coeff_twoPointDiagramSeries, coeff_twoPointDysonSeries,
    twoPointDiagramCoefficient_eq_twoPointDysonCoefficient]

/-- The constant coefficient is the order-zero two-point coefficient: the free two-point function. -/
theorem constantCoeff_twoPointDysonSeries (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    PowerSeries.constantCoeff (twoPointDysonSeries ε β g i j τ τ') =
      twoPointDysonCoefficient (n := 0) ε β g i j τ τ' := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_twoPointDysonSeries]

end Fermionic
end SecondQuantization
