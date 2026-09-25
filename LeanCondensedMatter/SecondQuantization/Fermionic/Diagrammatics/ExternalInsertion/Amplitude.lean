import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.TimedField
import Mathlib.GroupTheory.Perm.Sign

set_option linter.style.header false

/-!
# Fixed-time amplitudes for arbitrary external insertions

The canonical fixed flattened leg order is transported to mixed imaginary-time order by
`externalInsertionStandardToMixedAtomicPositionEquiv`. Its permutation sign supplies the fermionic
ordering factor for the full atomic field list. Quartic interaction vertices contribute four
consecutive legs, so no separate interaction-order sign is introduced here.

The fixed-time amplitude is this ordering sign times the generic interaction-vertex weight and the
mixed-time pairing evaluation from `TimedField`.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Fermionic sign of the permutation from fixed flattened atomic order to mixed-time atomic order. -/
noncomputable def externalInsertionMixedAtomicOrderSign {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  ((Equiv.Perm.sign
    (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) : ℤ) : ℂ)

/-- Fixed-time amplitude of an arbitrary external-insertion Wick diagram. -/
noncomputable def ExternalInsertionWickDiagram.fixedTimeAmplitude {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) : ℂ :=
  externalInsertionMixedAtomicOrderSign externalTime σ *
    d.vertexWeight g *
      d.mixedPairingValue ε β externalTime σ

end Fermionic
end SecondQuantization
