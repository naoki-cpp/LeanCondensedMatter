import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointWickDiagram
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Mixed.MixedOrderPairing

set_option linter.style.header false

/-!
# Reindexing the fermionic two-point pairing expansion

`SecondQuantization.Common` owns the statistics-independent mixed event/leg enumeration, the
standard-to-mixed position permutation, and the mixed-order pairing. This module adds only the
fermionic quartic labels and fixed external-field specialization needed for the Wick expansion.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*}

/-- Two-point Wick diagrams whose external labels are fixed to
`Tτ cᵢ(τ) cⱼ†(τ')`. -/
abbrev FixedExternalTwoPointWickDiagram (Mode : Type*) (n : ℕ) (i j : Mode) : Type _ :=
  {d : TwoPointWickDiagram Mode n (Finset.univ : Finset (Fin n)) //
    d.externalLabel = twoPointExternalLabels i j}

/-- Slot-indexed quartic labels together with a pairing in mixed-time atomic order. -/
abbrev OrderedTwoPointWickDiagramData (Mode : Type*) (n : ℕ) : Type _ :=
  (Fin n → QuarticVertexLabel Mode) × Pairing (2 * n + 1)

/-- The slot-indexed interaction labels of a fixed-external two-point diagram. -/
def FixedExternalTwoPointWickDiagram.vertexLabelSequence {n : ℕ} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    Fin n → QuarticVertexLabel Mode :=
  fun v => d.1.vertexLabel ⟨v, Finset.mem_univ v⟩

/-- Fixed-external two-point diagrams are equivalent to slot-indexed vertex labels and a pairing
in the Common-owned mixed-time atomic enumeration. -/
noncomputable def fixedExternalTwoPointWickDiagramEquivOrderedData
    {n : ℕ} (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    FixedExternalTwoPointWickDiagram Mode n i j ≃
      OrderedTwoPointWickDiagramData Mode n where
  toFun d := (d.vertexLabelSequence, d.1.pairingInMixedOrder τ τ' σ)
  invFun x :=
    ⟨{
      externalLabel := twoPointExternalLabels i j
      vertexLabel := fun v => x.1 v.1
      pairing := (Common.orderedTwoPointPairingCastEquiv n).symm
        (x.2.relabel (standardToMixedAtomicPositionEquiv τ τ' σ))
    }, rfl⟩
  left_inv d := by
    apply Subtype.ext
    apply Common.TwoPointDiagram.ext
    · exact d.2.symm
    · funext _
      rfl
    · change (Common.orderedTwoPointPairingCastEquiv n).symm
        (((Common.orderedTwoPointPairingCastEquiv n d.1.pairing).relabel
          (standardToMixedAtomicPositionEquiv τ τ' σ).symm).relabel
            (standardToMixedAtomicPositionEquiv τ τ' σ)) = d.1.pairing
      rw [Pairing.relabel_relabel_symm]
      exact (Common.orderedTwoPointPairingCastEquiv n).left_inv d.1.pairing
  right_inv x := by
    obtain ⟨labels, pairing⟩ := x
    apply Prod.ext
    · funext _
      rfl
    · change ((Common.orderedTwoPointPairingCastEquiv n
        ((Common.orderedTwoPointPairingCastEquiv n).symm
          (pairing.relabel (standardToMixedAtomicPositionEquiv τ τ' σ)))).relabel
            (standardToMixedAtomicPositionEquiv τ τ' σ).symm) = pairing
      calc
        ((Common.orderedTwoPointPairingCastEquiv n
            ((Common.orderedTwoPointPairingCastEquiv n).symm
              (pairing.relabel (standardToMixedAtomicPositionEquiv τ τ' σ)))).relabel
              (standardToMixedAtomicPositionEquiv τ τ' σ).symm) =
            (pairing.relabel (standardToMixedAtomicPositionEquiv τ τ' σ)).relabel
              (standardToMixedAtomicPositionEquiv τ τ' σ).symm :=
          congrArg
            (fun p : Pairing (2 * n + 1) =>
              p.relabel (standardToMixedAtomicPositionEquiv τ τ' σ).symm)
            ((Common.orderedTwoPointPairingCastEquiv n).right_inv
              (pairing.relabel (standardToMixedAtomicPositionEquiv τ τ' σ)))
        _ = pairing := Pairing.relabel_symm_relabel pairing
          (standardToMixedAtomicPositionEquiv τ τ' σ)

noncomputable instance FixedExternalTwoPointWickDiagram.instFintype
    [Fintype Mode] {n : ℕ} {i j : Mode} :
    Fintype (FixedExternalTwoPointWickDiagram Mode n i j) :=
  Fintype.ofFinite
    {d : TwoPointWickDiagram Mode n (Finset.univ : Finset (Fin n)) //
      d.externalLabel = twoPointExternalLabels i j}

end Fermionic
end SecondQuantization
