import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Reindexing

set_option linter.style.header false

/-!
# Fixed-time two-point Wick-diagram amplitudes

This module packages the canonical mixed-time pairing value as an amplitude of a two-point Wick
diagram with fixed external annihilation/creation labels. Pair construction and free Gibbs
state evaluation are owned by the preceding pairing layer.

The interaction times are still parameters. Ordered-simplex integration and the Dyson factor are
deliberately left to the next layer.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Product of the quartic coupling attached to the slot-indexed interaction labels. -/
noncomputable def orderedTwoPointVertexWeight {n : ℕ}
    (g : QuarticVertexLabel Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) : ℂ :=
  ∏ v, g (q v)

/-- Fixed-time amplitude in the slot-label/pairing representation. -/
noncomputable def orderedTwoPointFixedTimeAmplitude {n : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (x : OrderedTwoPointWickDiagramData Mode n) : ℂ :=
  twoPointExternalOrderSign τ τ' * orderedTwoPointVertexWeight g x.1 *
    orderedTwoPointPairingValue ε β i j τ τ' σ x.1 x.2

/-- Fixed-time amplitude of a two-point Wick diagram with the external labels fixed to
`Tτ cᵢ(τ) cⱼ†(τ')`. The pairing is evaluated after transport back to mixed-time atomic order. -/
noncomputable def FixedExternalTwoPointWickDiagram.fixedTimeAmplitude {n : ℕ} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ
    (fixedExternalTwoPointWickDiagramEquivOrderedData i j τ τ' σ d)

end Fermionic
end SecondQuantization
