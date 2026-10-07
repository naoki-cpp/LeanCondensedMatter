import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Factorization.ComponentVertexProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ComponentPairingValue

set_option linter.style.header false

/-!
# Component factorization of external-insertion fixed-time amplitudes

The mixed pairing value already factors after multiplying by the relative component-shuffle sign.
The remaining permutation identity compares that relative sign with the ambient and component-local
mixed-time ordering signs. Combining the two identities with the component decomposition of the
quartic vertex product gives the fixed-time amplitude product over connected components.

The residual component external-order sign is the fermionic sign for regrouping the fixed external
insertions by connected component; it cannot in general be dropped.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open scoped BigOperators

variable {Mode : Type*}

private theorem ExternalInsertionWickDiagram.componentWickDiagram_vertexWeight_eq_restrictComponent
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (g : QuarticVertexLabel Mode → ℂ)
    (B : d.vertexGraph.componentPartition.parts) :
    (d.componentWickDiagram B).vertexWeight g =
      (d.restrictComponent B).vertexWeight g := by
  classical
  let T :=
    interactionSector
      (B : Finset (ExternalInsertionVertex E (Finset.univ : Finset (Fin n))))
  let r := d.restrictComponent B
  change
    (∏ v : ↥(Finset.univ : Finset (Fin T.card)),
      g (r.vertexLabel (T.orderIsoOfFin rfl v.1))) =
      ∏ v : ↥T, g (r.vertexLabel v)
  let e : Fin T.card ≃ ↥(Finset.univ : Finset (Fin T.card)) :=
    (Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)).symm
  calc
    _ = ∏ v : Fin T.card, g (r.vertexLabel (T.orderIsoOfFin rfl v)) := by
      simpa [e] using
        (Equiv.prod_comp e
          (fun v : ↥(Finset.univ : Finset (Fin T.card)) =>
            g (r.vertexLabel (T.orderIsoOfFin rfl v.1)))).symm
    _ = _ := by
      simpa using
        (Equiv.prod_comp (T.orderIsoOfFin rfl).toEquiv
          (fun v : ↥T => g (r.vertexLabel v)))

variable [LinearOrder Mode] [Fintype Mode]

private theorem ExternalInsertionWickDiagram.mixedAtomicOrderSign_mul_mixedPairingValue_eq_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    externalInsertionMixedAtomicOrderSign externalTime σ *
        d.mixedPairingValue ε β externalTime σ =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          externalInsertionMixedAtomicOrderSign
              (d.componentExternalTime externalTime B)
              (d.componentInteractionTime σ B) *
            (d.componentWickDiagram B).mixedPairingValue ε β
              (d.componentExternalTime externalTime B)
              (d.componentInteractionTime σ B) := by
  classical
  have hglobalUnits :
      Equiv.Perm.sign
          (externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ) =
        Equiv.Perm.sign (d.relativeComponentShuffle externalTime σ) *
          ∏ B : d.vertexGraph.componentPartition.parts,
            Equiv.Perm.sign
              (externalInsertionStandardToMixedAtomicPositionEquiv
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B)) := by
    rw [d.relativeComponentShuffle_sign_eq_mixedAtomic_mul_prod_components,
      mul_assoc, Int.units_mul_self, mul_one]
  have hglobal :=
    congrArg (fun u : ℤˣ => (((u : ℤ) : ℂ))) hglobalUnits
  simp only [Units.val_mul, Units.coe_prod, Int.cast_mul, Int.cast_prod] at hglobal
  unfold externalInsertionMixedAtomicOrderSign
  rw [hglobal]
  calc
    _ =
        (∏ B : d.vertexGraph.componentPartition.parts,
          (((Equiv.Perm.sign
            (externalInsertionStandardToMixedAtomicPositionEquiv
              (d.componentExternalTime externalTime B)
              (d.componentInteractionTime σ B)) : ℤ) : ℂ))) *
          ((((Equiv.Perm.sign
            (d.relativeComponentShuffle externalTime σ) : ℤ) : ℂ)) *
            d.mixedPairingValue ε β externalTime σ) := by
      ring
    _ =
        (∏ B : d.vertexGraph.componentPartition.parts,
          (((Equiv.Perm.sign
            (externalInsertionStandardToMixedAtomicPositionEquiv
              (d.componentExternalTime externalTime B)
              (d.componentInteractionTime σ B)) : ℤ) : ℂ))) *
          (componentExternalOrderSign d blockOrder *
            ∏ B : d.vertexGraph.componentPartition.parts,
              (d.componentWickDiagram B).mixedPairingValue ε β
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B)) := by
      rw [d.relativeComponentShuffleSign_mul_mixedPairingValue_eq_componentExternalOrderSign_mul_prod_components
        ε β externalTime σ blockOrder]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      ring

/-- A fixed-time external-insertion amplitude is the fixed external regrouping sign times the
product of the standalone fixed-time amplitudes of all full connected components. -/
theorem ExternalInsertionWickDiagram.fixedTimeAmplitude_eq_componentExternalOrderSign_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    d.fixedTimeAmplitude ε β g externalTime σ =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          (d.componentWickDiagram B).fixedTimeAmplitude ε β g
            (d.componentExternalTime externalTime B)
            (d.componentInteractionTime σ B) := by
  classical
  have hvertex :
      d.vertexWeight g =
        ∏ B : d.vertexGraph.componentPartition.parts,
          (d.componentWickDiagram B).vertexWeight g := by
    rw [d.vertexWeight_eq_prod_components g]
    apply Finset.prod_congr rfl
    intro B _
    exact (d.componentWickDiagram_vertexWeight_eq_restrictComponent g B).symm
  have horderPairing :=
    d.mixedAtomicOrderSign_mul_mixedPairingValue_eq_components
      ε β externalTime σ blockOrder
  unfold ExternalInsertionWickDiagram.fixedTimeAmplitude
  calc
    _ = d.vertexWeight g *
        (externalInsertionMixedAtomicOrderSign externalTime σ *
          d.mixedPairingValue ε β externalTime σ) := by
      ring
    _ = d.vertexWeight g *
        (componentExternalOrderSign d blockOrder *
          ∏ B : d.vertexGraph.componentPartition.parts,
            externalInsertionMixedAtomicOrderSign
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B) *
              (d.componentWickDiagram B).mixedPairingValue ε β
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B)) := by
      rw [horderPairing]
    _ = componentExternalOrderSign d blockOrder *
        ((∏ B : d.vertexGraph.componentPartition.parts,
            (d.componentWickDiagram B).vertexWeight g) *
          ∏ B : d.vertexGraph.componentPartition.parts,
            externalInsertionMixedAtomicOrderSign
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B) *
              (d.componentWickDiagram B).mixedPairingValue ε β
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B)) := by
      rw [hvertex]
      ring
    _ = componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          (d.componentWickDiagram B).vertexWeight g *
            (externalInsertionMixedAtomicOrderSign
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B) *
              (d.componentWickDiagram B).mixedPairingValue ε β
                (d.componentExternalTime externalTime B)
                (d.componentInteractionTime σ B)) := by
      rw [← Finset.prod_mul_distrib]
    _ = _ := by
      apply congrArg (fun z : ℂ => componentExternalOrderSign d blockOrder * z)
      apply Finset.prod_congr rfl
      intro B _
      ring

end Fermionic
end SecondQuantization
