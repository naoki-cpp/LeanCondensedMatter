import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointWickDiagram
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.TwoPointMixedLegOrder
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Reindexing the fermionic two-point pairing expansion

`SecondQuantization.Common` owns the statistics-independent mixed event/leg enumeration and the
standard-to-mixed position permutation. This module adds the fermionic quartic labels and fixed
external-field specialization needed to transport Wick pairings into that Common enumeration.
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

/-- Cast the standard diagram pairing cardinality from `univ.card` to the explicit slot count. -/
noncomputable def orderedTwoPointPairingCastEquiv (n : ℕ) :
    Pairing (2 * (Finset.univ : Finset (Fin n)).card + 1) ≃ Pairing (2 * n + 1) :=
  Equiv.cast (by simp)

/-- The slot-indexed interaction labels of a fixed-external two-point diagram. -/
def FixedExternalTwoPointWickDiagram.vertexLabelSequence {n : ℕ} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagram Mode n i j) :
    Fin n → QuarticVertexLabel Mode :=
  fun v => d.1.vertexLabel ⟨v, Finset.mem_univ v⟩

/-- A diagram pairing transported from standard diagram-leg order back to mixed-time atomic order. -/
noncomputable def FixedExternalTwoPointWickDiagram.pairingInMixedOrder {n : ℕ} {i j : Mode}
    (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : Pairing (2 * n + 1) :=
  (orderedTwoPointPairingCastEquiv n d.1.pairing).relabel
    (standardToMixedAtomicPositionEquiv τ τ' σ).symm

/-- Fixed-external two-point diagrams are equivalent to slot-indexed vertex labels and a pairing
in the mixed-time atomic enumeration. -/
noncomputable def fixedExternalTwoPointWickDiagramEquivOrderedData
    {n : ℕ} (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ) :
    FixedExternalTwoPointWickDiagram Mode n i j ≃
      OrderedTwoPointWickDiagramData Mode n where
  toFun d := (d.vertexLabelSequence, d.pairingInMixedOrder τ τ' σ)
  invFun x :=
    ⟨{
      externalLabel := twoPointExternalLabels i j
      vertexLabel := fun v => x.1 v.1
      pairing := (orderedTwoPointPairingCastEquiv n).symm
        (x.2.relabel (standardToMixedAtomicPositionEquiv τ τ' σ))
    }, rfl⟩
  left_inv d := by
    apply Subtype.ext
    apply Common.TwoPointDiagram.ext
    · exact d.2.symm
    · funext _
      rfl
    · change (orderedTwoPointPairingCastEquiv n).symm
        (((orderedTwoPointPairingCastEquiv n d.1.pairing).relabel
          (standardToMixedAtomicPositionEquiv τ τ' σ).symm).relabel
            (standardToMixedAtomicPositionEquiv τ τ' σ)) = d.1.pairing
      rw [Pairing.relabel_relabel_symm]
      exact (orderedTwoPointPairingCastEquiv n).left_inv d.1.pairing
  right_inv x := by
    obtain ⟨labels, pairing⟩ := x
    apply Prod.ext
    · funext _
      rfl
    · change ((orderedTwoPointPairingCastEquiv n
        ((orderedTwoPointPairingCastEquiv n).symm
          (pairing.relabel (standardToMixedAtomicPositionEquiv τ τ' σ)))).relabel
            (standardToMixedAtomicPositionEquiv τ τ' σ).symm) = pairing
      calc
        ((orderedTwoPointPairingCastEquiv n
            ((orderedTwoPointPairingCastEquiv n).symm
              (pairing.relabel (standardToMixedAtomicPositionEquiv τ τ' σ)))).relabel
              (standardToMixedAtomicPositionEquiv τ τ' σ).symm) =
            (pairing.relabel (standardToMixedAtomicPositionEquiv τ τ' σ)).relabel
              (standardToMixedAtomicPositionEquiv τ τ' σ).symm :=
          congrArg
            (fun p : Pairing (2 * n + 1) =>
              p.relabel (standardToMixedAtomicPositionEquiv τ τ' σ).symm)
            ((orderedTwoPointPairingCastEquiv n).right_inv
              (pairing.relabel (standardToMixedAtomicPositionEquiv τ τ' σ)))
        _ = pairing := Pairing.relabel_symm_relabel pairing
          (standardToMixedAtomicPositionEquiv τ τ' σ)

noncomputable instance FixedExternalTwoPointWickDiagram.instFintype
    [Fintype Mode] {n : ℕ} {i j : Mode} :
    Fintype (FixedExternalTwoPointWickDiagram Mode n i j) :=
  Fintype.ofFinite
    {d : TwoPointWickDiagram Mode n (Finset.univ : Finset (Fin n)) //
      d.externalLabel = twoPointExternalLabels i j}

/-- Reindex a finite sum over fixed-external diagrams as a sum over slot labels and mixed-order
pairings. -/
theorem sum_fixedExternalTwoPointWickDiagram_eq_sum_orderedData
    [Fintype Mode] {n : ℕ} (i j : Mode) (τ τ' : ℝ) (σ : Fin n → ℝ)
    (F : OrderedTwoPointWickDiagramData Mode n → ℂ) :
    ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        F (fixedExternalTwoPointWickDiagramEquivOrderedData i j τ τ' σ d) =
      ∑ x : OrderedTwoPointWickDiagramData Mode n, F x :=
  Equiv.sum_comp (fixedExternalTwoPointWickDiagramEquivOrderedData i j τ τ' σ) F

end Fermionic
end SecondQuantization
