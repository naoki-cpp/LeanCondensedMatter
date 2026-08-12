import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DysonCoefficient
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.QuarticInteraction
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

set_option linter.style.header false

/-!
# The perturbative two-point series

The order-`n` two-point coefficients of `DysonCoefficient.lean` are assembled into formal power
series in the coupling, one for each presentation: the diagram sum and the mixed time-ordered
density-state expectation. They are the same series, because the two coefficients agree at every
order.

The series is then divided by the partition series of the same interaction, normalized to constant
coefficient one. That division is what the linked-cluster theorem asks for: the coefficients are
already free Gibbs expectations, so only the interacting vacuum contributions remain to be
cancelled.
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

omit [LinearOrder Mode] in
/-- The normalized partition series is invertible: its constant coefficient is one. -/
theorem constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries_ne_zero
    (ε : Mode → ℝ) (β : ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    PowerSeries.constantCoeff
        (PowerSeries.normalizeByConstantCoeff (dysonPartitionSeries ε β V)) ≠ 0 := by
  rw [constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries]
  exact one_ne_zero

/-- **The defining property of the vacuum normalization**: multiplying back by the normalized
partition series recovers the two-point series. -/
theorem vacuumNormalizedTwoPointDysonSeries_mul_normalizeByConstantCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    vacuumNormalizedTwoPointDysonSeries ε β g i j τ τ' *
        PowerSeries.normalizeByConstantCoeff
          (dysonPartitionSeries ε β (quarticInteraction g)) =
      twoPointDysonSeries ε β g i j τ τ' := by
  rw [vacuumNormalizedTwoPointDysonSeries, mul_assoc,
    PowerSeries.inv_mul_cancel _
      (constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries_ne_zero ε β
        (quarticInteraction g)),
    mul_one]

/-- Normalizing by the vacuum leaves the order-zero coefficient unchanged. -/
theorem constantCoeff_vacuumNormalizedTwoPointDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    PowerSeries.constantCoeff (vacuumNormalizedTwoPointDysonSeries ε β g i j τ τ') =
      twoPointDysonCoefficient (n := 0) ε β g i j τ τ' := by
  rw [vacuumNormalizedTwoPointDysonSeries, map_mul, PowerSeries.constantCoeff_inv,
    constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries, inv_one, mul_one,
    constantCoeff_twoPointDysonSeries]

end Fermionic
end SecondQuantization
