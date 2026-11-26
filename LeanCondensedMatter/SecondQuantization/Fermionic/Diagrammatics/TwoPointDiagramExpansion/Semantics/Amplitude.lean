import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Semantics.PairContraction
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Amplitude

set_option linter.style.header false

/-!
# Fixed-time two-point Wick-diagram amplitudes

This module packages the canonical mixed-time pairing value as an amplitude of a two-point Wick
diagram with fixed external annihilation/creation labels. Pair construction and free Gibbs
state evaluation are owned by the preceding pairing layer.

The interaction times are still parameters. The pointwise Dyson sign is included here;
ordered-simplex integration belongs to the integration layer.
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

open Common in
/-- The actual fixed-time amplitude of a two-point Wick diagram equals the
general external-insertion amplitude after transporting its fixed-leg pairing.
Both oriented contractions live at exactly the same mixed positions, even
at coincident times. -/
theorem FixedExternalTwoPointWickDiagram.fixedTimeAmplitude_eq_externalInsertion
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    d.fixedTimeAmplitude ε β g τ τ' σ =
      ExternalInsertionWickDiagram.fixedTimeAmplitude
        (twoPointDiagramExternalInsertionEquiv Finset.univ d.1) ε β g
        (twoPointExternalTimes τ τ') σ := by
  classical
  let D := twoPointDiagramExternalInsertionEquiv Finset.univ d.1
  have hlabel : D.externalLabel = twoPointExternalLabels i j := d.2
  have hvertex : D.vertexLabelSequence = d.vertexLabelSequence := rfl
  have hweight : D.vertexWeight g = orderedTwoPointVertexWeight g d.vertexLabelSequence := by
    unfold ExternalInsertionDiagram.vertexWeight orderedTwoPointVertexWeight
    rw [← hvertex]
    exact (Equiv.prod_comp
      (Equiv.ofBijective (fun v : Fin n => (⟨v, Finset.mem_univ v⟩ :
        ↥(Finset.univ : Finset (Fin n)))) ⟨fun a b h => congrArg Subtype.val h,
          fun v => ⟨v.1, Subtype.ext rfl⟩⟩)
      (fun v => g (D.vertexLabel v))).symm
  change orderedTwoPointFixedTimeAmplitude ε β g i j τ τ' σ
      (d.vertexLabelSequence, d.1.pairingInMixedOrder τ τ' σ) =
    ExternalInsertionWickDiagram.fixedTimeAmplitude D ε β g
      (twoPointExternalTimes τ τ') σ
  unfold orderedTwoPointFixedTimeAmplitude ExternalInsertionWickDiagram.fixedTimeAmplitude
    orderedTwoPointPairingValue ExternalInsertionWickDiagram.mixedPairingValue
    mixedTimeOrderedAtomicPairValue externalInsertionMixedTimeOrderedAtomicPairValue
  rw [externalInsertionMixedAtomicOrderSign_twoPoint, hweight,
    show D.pairingInMixedOrder (twoPointExternalTimes τ τ') σ =
      d.1.pairingInMixedOrder τ τ' σ from
        twoPointDiagramExternalInsertionEquiv_pairingInMixedOrder d.1 τ τ' σ,
    hlabel, hvertex, mixedTimeOrderedAtomicFieldFamily_eq_externalInsertion]

/-- Pointwise fixed-time amplitude with the global order-`n` Dyson sign included. -/
noncomputable def FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : ℂ :=
  (-1 : ℂ) ^ n * d.fixedTimeAmplitude ε β g τ τ' σ

end Fermionic
end SecondQuantization
