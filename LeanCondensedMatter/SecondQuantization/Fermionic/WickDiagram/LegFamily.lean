import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram
import LeanCondensedMatter.SecondQuantization.Fermionic.QuarticLocalLeg

set_option linter.style.header false

/-!
# The atomic leg operator for an arbitrary vertex-label sequence

Refactor PR B of the post-PR-6 cleanup (`notes/roadmaps/second-quantization.md`): a single generic
operator family, `quarticLegOperatorForSequence`, for the atomic operator at a flattened leg
position `p : Fin (2 * (2 * n))`, given *any* vertex-label sequence `q : Fin n →
QuarticVertexLabel Mode` and time assignment `τ : Fin n → ℝ` — looks up which slot/local-leg `p`
corresponds to (`orderedQuarticLegEquiv`) and evolves that vertex's local-leg operator
(`QuarticLocalLeg.lean`) to the slot's assigned time.

This is the common shape behind two previously independent constructions:
`Fermionic/DysonDiagramExpansion.lean`'s `flatVertexLegOperator` (for a bare vertex-label sequence,
not yet a `QuarticWickDiagram`) and `WickDiagram/Amplitude.lean`'s `orderedQuarticLegOperator` (for
a fixed diagram `d` and vertex order, via `q := fun i => d.vertexLabel (order i)`) — both are now
literally `quarticLegOperatorForSequence` specializations, so
`orderedQuarticLegOperator_eq_flatVertexLegOperator` (`DysonDiagramExpansion.lean`) is a structural
consequence of sharing this one definition, not a coincidental `rfl`.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The atomic operator at a flattened leg position, for an arbitrary vertex-label sequence `q`
and time assignment `τ`**: look up which slot/local-leg the position corresponds to
(`orderedQuarticLegEquiv`), and evolve that vertex's local-leg operator to the slot's assigned
time. -/
noncomputable def quarticLegOperatorForSequence (ε : Mode → ℝ) {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  let slotLeg := orderedQuarticLegEquiv n p
  imaginaryTimeEvolve ε (τ slotLeg.1) (quarticLocalLegOperator (q slotLeg.1) slotLeg.2)

end SecondQuantization
