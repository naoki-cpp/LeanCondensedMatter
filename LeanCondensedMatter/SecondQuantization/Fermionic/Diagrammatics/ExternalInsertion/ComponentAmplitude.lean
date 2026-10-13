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

private theorem ExternalInsertionWickDiagram.componentOrderedDiagram_vertexWeight_eq_restrictComponent
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (g : QuarticVertexLabel Mode → ℂ)
    (B : d.vertexGraph.componentPartition.parts) :
    (d.componentOrderedDiagram B).vertexWeight g =
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
            (d.componentOrderedDiagram B).mixedPairingValue ε β
              (d.componentExternalTime externalTime B)
              (d.componentInteractionTime σ B) := by
  classical
  let localSign : d.vertexGraph.componentPartition.parts → ℂ := fun B =>
    externalInsertionMixedAtomicOrderSign
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B)
  let localValue : d.vertexGraph.componentPartition.parts → ℂ := fun B =>
    (d.componentOrderedDiagram B).mixedPairingValue ε β
      (d.componentExternalTime externalTime B)
      (d.componentInteractionTime σ B)
  let relativeSign : ℂ :=
    ((Equiv.Perm.sign (d.relativeComponentShuffle externalTime σ) : ℤ) : ℂ)
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
  have hglobal :
      externalInsertionMixedAtomicOrderSign externalTime σ =
        relativeSign * ∏ B, localSign B := by
    have h := congrArg (fun u : ℤˣ => (((u : ℤ) : ℂ))) hglobalUnits
    simpa only [externalInsertionMixedAtomicOrderSign, relativeSign, localSign,
      Units.val_mul, Units.coe_prod, Int.cast_mul, Int.cast_prod] using h
  have hlocal :
      relativeSign * d.mixedPairingValue ε β externalTime σ =
        componentExternalOrderSign d blockOrder * ∏ B, localValue B :=
    d.relativeComponentShuffleSign_mul_mixedPairingValue_eq_componentExternalOrderSign_mul_prod_components
      ε β externalTime σ blockOrder
  change externalInsertionMixedAtomicOrderSign externalTime σ *
      d.mixedPairingValue ε β externalTime σ =
    componentExternalOrderSign d blockOrder *
      ∏ B, localSign B * localValue B
  calc
    _ = (∏ B, localSign B) *
        (relativeSign * d.mixedPairingValue ε β externalTime σ) := by
      rw [hglobal]
      ring
    _ = (∏ B, localSign B) *
        (componentExternalOrderSign d blockOrder * ∏ B, localValue B) := by
      rw [hlocal]
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
          (d.componentOrderedDiagram B).fixedTimeAmplitude ε β g
            (d.componentExternalTime externalTime B)
            (d.componentInteractionTime σ B) := by
  classical
  have hvertex :
      d.vertexWeight g =
        ∏ B : d.vertexGraph.componentPartition.parts,
          (d.componentOrderedDiagram B).vertexWeight g := by
    rw [d.vertexWeight_eq_prod_components g]
    apply Finset.prod_congr rfl
    intro B _
    exact (d.componentOrderedDiagram_vertexWeight_eq_restrictComponent g B).symm
  have horderPairing :=
    d.mixedAtomicOrderSign_mul_mixedPairingValue_eq_components
      ε β externalTime σ blockOrder
  unfold ExternalInsertionWickDiagram.fixedTimeAmplitude
  calc
    _ = d.vertexWeight g *
          (externalInsertionMixedAtomicOrderSign externalTime σ *
            d.mixedPairingValue ε β externalTime σ) := by
      ring
    _ = componentExternalOrderSign d blockOrder *
          ((∏ B : d.vertexGraph.componentPartition.parts,
              (d.componentOrderedDiagram B).vertexWeight g) *
            ∏ B : d.vertexGraph.componentPartition.parts,
              externalInsertionMixedAtomicOrderSign
                  (d.componentExternalTime externalTime B)
                  (d.componentInteractionTime σ B) *
                (d.componentOrderedDiagram B).mixedPairingValue ε β
                  (d.componentExternalTime externalTime B)
                  (d.componentInteractionTime σ B)) := by
      rw [hvertex, horderPairing]
      ring
    _ = _ := by
      rw [← Finset.prod_mul_distrib]
      apply congrArg (fun z : ℂ => componentExternalOrderSign d blockOrder * z)
      apply Finset.prod_congr rfl
      intro B _
      ring

/-- The Dyson-signed fixed-time amplitude factors into the fixed external regrouping sign and the
product of the standalone Dyson-signed component amplitudes. -/
theorem ExternalInsertionWickDiagram.dysonFixedTimeAmplitude_eq_componentExternalOrderSign_mul_prod_components
    {E n : ℕ}
    (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ)
    (blockOrder : d.vertexGraph.componentPartition.parts ≃
      Fin (Fintype.card d.vertexGraph.componentPartition.parts)) :
    d.dysonFixedTimeAmplitude ε β g externalTime σ =
      componentExternalOrderSign d blockOrder *
        ∏ B : d.vertexGraph.componentPartition.parts,
          (d.componentOrderedDiagram B).dysonFixedTimeAmplitude ε β g
            (d.componentExternalTime externalTime B)
            (d.componentInteractionTime σ B) := by
  classical
  have hdyson :
      (-1 : ℂ) ^ n =
        ∏ B : d.vertexGraph.componentPartition.parts,
          (-1 : ℂ) ^ (interactionSector
            (B : Finset (ExternalInsertionVertex E
              (Finset.univ : Finset (Fin n))))).card := by
    have hcount :
        (∑ B : d.vertexGraph.componentPartition.parts,
          (interactionSector
            (B : Finset (ExternalInsertionVertex E
              (Finset.univ : Finset (Fin n))))).card) = n := by
      simpa using (sum_interactionSector_card_eq d.vertexGraph)
    calc
      (-1 : ℂ) ^ n =
          (-1 : ℂ) ^ (∑ B : d.vertexGraph.componentPartition.parts,
            (interactionSector
              (B : Finset (ExternalInsertionVertex E
                (Finset.univ : Finset (Fin n))))).card) :=
        congrArg (fun k : ℕ => (-1 : ℂ) ^ k) hcount.symm
      _ = _ := by rw [← Finset.prod_pow_eq_pow_sum]
  unfold ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
  rw [d.fixedTimeAmplitude_eq_componentExternalOrderSign_mul_prod_components
    ε β g externalTime σ blockOrder, hdyson, Finset.prod_mul_distrib]
  ring

end Fermionic
end SecondQuantization
