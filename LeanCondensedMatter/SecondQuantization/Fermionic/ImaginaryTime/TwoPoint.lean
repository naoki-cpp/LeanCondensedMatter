import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TimeOrdering
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# Canonical fermionic two-point operator in imaginary time

This module owns the diagram-independent operator

`Tτ cᵢ(τ) cⱼ†(τ')`.

It combines free imaginary-time evolution of the ladder operators with the common fermionic
`timeOrderedProduct`. Thermal modules apply state functionals to this operator, while diagrammatic
external-field modules relate it to their labelled representation.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode]

/-- The canonical fermionic two-point operator `Tτ cᵢ(τ) cⱼ†(τ')`. -/
noncomputable def twoPointTimeOrderedProduct (ε : Mode → ℝ)
    (i j : Mode) (τ τ' : ℝ) : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  Common.timeOrderedProduct Common.Statistics.fermion
    (imaginaryTimeEvolve ε τ (annihilate i))
    (imaginaryTimeEvolve ε τ' (create j)) τ τ'

/-- When the annihilation field is later, it remains on the left. -/
theorem twoPointTimeOrderedProduct_of_gt (ε : Mode → ℝ) (i j : Mode)
    {τ τ' : ℝ} (h : τ' < τ) :
    twoPointTimeOrderedProduct ε i j τ τ' =
      (imaginaryTimeEvolve ε τ (annihilate i)).comp
        (imaginaryTimeEvolve ε τ' (create j)) := by
  exact Common.timeOrderedProduct_of_gt Common.Statistics.fermion _ _ h

/-- When the creation field is later, exchanging the two odd fields contributes the fermionic
sign. -/
theorem twoPointTimeOrderedProduct_of_lt (ε : Mode → ℝ) (i j : Mode)
    {τ τ' : ℝ} (h : τ < τ') :
    twoPointTimeOrderedProduct ε i j τ τ' =
      (Common.Statistics.fermion.zetaInt : ℂ) •
        ((imaginaryTimeEvolve ε τ' (create j)).comp
          (imaginaryTimeEvolve ε τ (annihilate i))) := by
  exact Common.timeOrderedProduct_of_lt Common.Statistics.fermion _ _ h

/-- At equal imaginary times, the project convention uses the symmetric `θ(0) = 1/2` value. -/
@[simp]
theorem twoPointTimeOrderedProduct_self_time (ε : Mode → ℝ) (i j : Mode) (τ : ℝ) :
    twoPointTimeOrderedProduct ε i j τ τ =
      (2⁻¹ : ℂ) •
        ((imaginaryTimeEvolve ε τ (annihilate i)).comp
            (imaginaryTimeEvolve ε τ (create j)) +
          (Common.Statistics.fermion.zetaInt : ℂ) •
            ((imaginaryTimeEvolve ε τ (create j)).comp
              (imaginaryTimeEvolve ε τ (annihilate i)))) := by
  exact Common.timeOrderedProduct_self_time Common.Statistics.fermion _ _ τ

end Fermionic
end SecondQuantization
