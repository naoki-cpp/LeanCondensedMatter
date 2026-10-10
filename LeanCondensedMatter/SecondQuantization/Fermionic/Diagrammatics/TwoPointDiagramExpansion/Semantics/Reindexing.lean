import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.Pairing
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
      pairing := x.2.transport (mixedTimeAmbientPositionEquiv τ τ' σ).symm
    }, rfl⟩
  left_inv d := by
    apply Subtype.ext
    apply Common.TwoPointDiagram.ext
    · exact d.2.symm
    · funext _
      rfl
    · change (d.1.pairing.transport (mixedTimeAmbientPositionEquiv τ τ' σ)).transport
          (mixedTimeAmbientPositionEquiv τ τ' σ).symm = d.1.pairing
      exact PairingOn.transport_symm_transport _ _
  right_inv x := by
    obtain ⟨labels, pairing⟩ := x
    apply Prod.ext
    · funext _
      rfl
    · change (pairing.transport (mixedTimeAmbientPositionEquiv τ τ' σ).symm).transport
          (mixedTimeAmbientPositionEquiv τ τ' σ) = pairing
      exact PairingOn.transport_transport_symm _ _

noncomputable instance FixedExternalTwoPointWickDiagram.instFintype
    [Fintype Mode] {n : ℕ} {i j : Mode} :
    Fintype (FixedExternalTwoPointWickDiagram Mode n i j) :=
  Fintype.ofFinite
    {d : TwoPointWickDiagram Mode n (Finset.univ : Finset (Fin n)) //
      d.externalLabel = twoPointExternalLabels i j}

end Fermionic
end SecondQuantization
