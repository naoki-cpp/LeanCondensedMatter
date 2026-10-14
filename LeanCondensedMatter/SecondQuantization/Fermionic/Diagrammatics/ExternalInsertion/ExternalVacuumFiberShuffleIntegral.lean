import LeanCondensedMatter.Combinatorics.SlotShuffle
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Pairing

set_option linter.style.header false

/-!
# Vacuum ordered data in binary support-slot shuffle coordinates

The vacuum factor inherited from a support-slot split has the same oriented
quartic pairing value and Dyson vertex weights as the fixed ordered vacuum
datum. The time coordinates are the right embedding of the binary shuffle.
This is the vacuum-coordinate part of the integrated external/vacuum fiber bridge.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

private theorem quarticVacuumDysonFactor_orderIsoOfFin
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {N k : ℕ} (S : Finset (Fin N)) (h : S.card = k)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) N S)
    (σ : Fin N → ℝ) :
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin N := fun i => (S.orderIsoOfFin rfl i).1
    let x : OrderedQuarticDiagramData (QuarticVertexLabel Mode) k :=
      quarticDiagramEquivOrderedData (S.orderIsoOfFin h).toEquiv vac
    ((-1 : ℂ) ^ S.card * vac.vertexWeight g) *
      (vac.pairingInOrder order).evaluation
        ((vac.pairingInOrder order).weight Statistics.fermion)
        (flatVertexLegPairValue ε β
          (fun i => vac.vertexLabel (S.orderIsoOfFin rfl i)) (σ ∘ f)) =
      ((-1 : ℂ) ^ k * (∏ i : Fin k, g (x.1 i))) *
        flatVertexLegPairingEvaluation ε β x.1
          (fun i => σ ((S.orderIsoOfFin h i).1)) x.2 := by
  cases h
  dsimp only
  rw [vac.vertexWeight_eq_prod_vertexLabel_order g (S.orderIsoOfFin rfl).toEquiv]
  rfl

/-- The vacuum Dyson factor of a split diagram is the ordered-quartic factor
evaluated on the right coordinates of the ambient binary slot shuffle.
In particular, no reversal of a fermionic pairing kernel is used. -/
theorem externalInsertionVacuumDysonFactor_eq_shuffleOrderedData
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {m k : ℕ} (shuffle : SlotShuffle m k)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) (m + k)
      ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots))
    (σ : Fin (m + k) → ℝ) :
    let S := (Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin (m + k) := fun i => (S.orderIsoOfFin rfl i).1
    let x : OrderedQuarticDiagramData (QuarticVertexLabel Mode) k :=
      quarticDiagramEquivOrderedData shuffle.sdiffLeftSlotsOrderEquiv vac
    ((-1 : ℂ) ^ S.card * vac.vertexWeight g) *
      (vac.pairingInOrder order).evaluation
        ((vac.pairingInOrder order).weight Statistics.fermion)
        (flatVertexLegPairValue ε β
          (fun i => vac.vertexLabel (S.orderIsoOfFin rfl i)) (σ ∘ f)) =
      ((-1 : ℂ) ^ k * (∏ i : Fin k, g (x.1 i))) *
        flatVertexLegPairingEvaluation ε β x.1
          (fun i => σ (shuffle.slotEquiv (Sum.inr i))) x.2 := by
  dsimp only
  have h := quarticVacuumDysonFactor_orderIsoOfFin ε β g
    ((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots)
    shuffle.card_sdiff_leftSlots vac σ
  have htime :
      (fun i : Fin k =>
          σ (((((Finset.univ : Finset (Fin (m + k))) \ shuffle.leftSlots).orderIsoOfFin
            shuffle.card_sdiff_leftSlots) i).1)) =
        (fun i : Fin k => σ (shuffle.slotEquiv (Sum.inr i))) := by
    funext i
    exact congrArg σ (shuffle.sdiffLeftSlots_orderEmbOfFin i)
  rw [htime] at h
  exact h

end Fermionic
end SecondQuantization
