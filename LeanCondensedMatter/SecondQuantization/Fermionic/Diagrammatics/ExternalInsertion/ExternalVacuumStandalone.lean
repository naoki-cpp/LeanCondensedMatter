import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumAmplitude
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SupportPairingStandardization

set_option linter.style.header false

/-!
# Standalone amplitude of an external-support sector

Increasing enumeration of the supported interaction slots identifies the
local mixed-time Dyson factor with the usual standalone external-insertion
amplitude. In particular, missing ambient interaction slots introduce neither
an extra pairing reindexing nor a new fermionic sign.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The external-support Dyson factor in a slot split is precisely the Dyson
amplitude of the canonical standalone diagram on its consecutive support slots.
The complementary vacuum sector occurs only in the identity permutation used
to express the local fermionic sign. -/
theorem externalInsertionSupport_dysonFactor_eq_standardizedAmplitude
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let fT : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
    let localFixed :=
      (externalInsertionStandardToMixedAtomicPositionEquiv externalTime (σ ∘ fT)).symm
    let localPairing : Pairing (2 * T.card + E) :=
      ext.pairing.transport localFixed
    let localSign : ℂ :=
      ((Equiv.Perm.sign
        (Equiv.sumCongr localFixed
          (Equiv.refl (Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))))) : ℤ) : ℂ)
    let localKernel := externalInsertionMixedTimeOrderedAtomicPairValue ε β
      ext.externalLabel externalTime
      (fun v => ext.vertexLabel (T.orderIsoOfFin rfl v)) (σ ∘ fT)
    let localValue : ℂ :=
      localPairing.evaluation (localPairing.weight Statistics.fermion) localKernel
    let e : ↥T ≃ ↥(Finset.univ : Finset (Fin T.card)) :=
      (T.orderIsoOfFin rfl).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin T.card => Finset.mem_univ i)).symm
    ((-1 : ℂ) ^ T.card * ext.vertexWeight g) * (localSign * localValue) =
      (ext.slotCongr e : ExternalInsertionWickDiagram Mode E T.card).dysonFixedTimeAmplitude ε β g externalTime (σ ∘ fT) := by
  intro fT localFixed localPairing localSign localKernel localValue e
  have hpair :
      (ext.slotCongr e).pairingInMixedOrder externalTime (σ ∘ fT) =
        localPairing := by
    exact ext.supportSlotCongr_pairingInMixedOrder T externalTime σ
  have hvertices :
      (ext.slotCongr e).vertexLabelSequence =
        (fun v => ext.vertexLabel (T.orderIsoOfFin rfl v)) := by
    funext v
    change ext.vertexLabel (e.symm ⟨v, Finset.mem_univ v⟩) =
      ext.vertexLabel (T.orderIsoOfFin rfl v)
    rfl
  have hkernel :
      externalInsertionMixedTimeOrderedAtomicPairValue ε β
          (ext.slotCongr e).externalLabel externalTime
          (ext.slotCongr e).vertexLabelSequence (σ ∘ fT) = localKernel := by
    simp only [localKernel, ExternalInsertionDiagram.slotCongr_externalLabel, hvertices]
  have hvalue :
      (ext.slotCongr e : ExternalInsertionWickDiagram Mode E T.card).mixedPairingValue ε β externalTime (σ ∘ fT) =
        localValue := by
    change ((ext.slotCongr e).pairingInMixedOrder externalTime (σ ∘ fT)).evaluation
      (((ext.slotCongr e).pairingInMixedOrder externalTime (σ ∘ fT)).weight
        Statistics.fermion)
      (externalInsertionMixedTimeOrderedAtomicPairValue ε β
        (ext.slotCongr e).externalLabel externalTime
        (ext.slotCongr e).vertexLabelSequence (σ ∘ fT)) = localValue
    rw [hpair, hkernel]
  have hweight : (ext.slotCongr e).vertexWeight g = ext.vertexWeight g :=
    ext.slotCongr_vertexWeight e g
  have hsign :
      localSign = externalInsertionMixedAtomicOrderSign externalTime (σ ∘ fT) := by
    change ((Equiv.Perm.sign
      (Equiv.sumCongr localFixed
        (Equiv.refl (Fin (2 * (2 * ((Finset.univ : Finset (Fin n)) \ T).card))))) : ℤ) : ℂ) =
      ((Equiv.Perm.sign
        (externalInsertionStandardToMixedAtomicPositionEquiv externalTime (σ ∘ fT)) : ℤ) : ℂ)
    simp only [localFixed, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl,
      mul_one, Equiv.Perm.sign_symm]
  unfold ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
    ExternalInsertionWickDiagram.fixedTimeAmplitude
  rw [← hsign, hweight, hvalue]
  ring

end Fermionic
end SecondQuantization
