import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumPairing
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.SupportPairingStandardization

set_option linter.style.header false

/-!
# Standalone Dyson factorization of external support and vacuum components

The mixed atomic ordering sign and inter-sector pairing crossings cancel before
Dyson signs and vertex couplings are split. The external-support sector first
factors in local mixed-time pairing coordinates; increasing enumeration of
the supported interaction slots identifies that local factor with a canonical
standalone external-insertion amplitude. Missing ambient interaction slots
introduce neither an extra pairing reindexing nor a fermionic sign.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The Dyson-signed amplitude of a reassembled external/vacuum diagram factors
pointwise on strictly antitone vacuum chambers. The local factor retains the
external support's genuine mixed-to-fixed reordering sign; the vacuum factor
uses its increasing slot order and correctly oriented pairing evaluation. -/
theorem externalInsertionOfSlotSplit_dysonFixedTimeAmplitude_eq_local_mul_vacuum
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let fT : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
    let localFixed :=
      (externalInsertionStandardToMixedAtomicPositionEquiv externalTime (σ ∘ fT)).symm
    let localPairing : Combinatorics.Pairing (2 * T.card + E) :=
      ext.pairing.transport localFixed
    let localSign : ℂ :=
      ((Equiv.Perm.sign
        (Equiv.sumCongr localFixed (Equiv.refl (Fin (2 * (2 * S.card))))) : ℤ) : ℂ)
    let localKernel := externalInsertionMixedTimeOrderedAtomicPairValue ε β
      ext.externalLabel externalTime
      (fun v => ext.vertexLabel (T.orderIsoOfFin rfl v)) (σ ∘ fT)
    let localValue : ℂ :=
      localPairing.evaluation (localPairing.weight Common.Statistics.fermion) localKernel
    let vacuumKernel := flatVertexLegPairValue ε β
      (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
    let vacuumValue : ℂ :=
      (vac.pairingInOrder order).evaluation
        ((vac.pairingInOrder order).weight Common.Statistics.fermion) vacuumKernel
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    StrictAnti (σ ∘ f) →
      d.dysonFixedTimeAmplitude ε β g externalTime σ =
        (((-1 : ℂ) ^ T.card * ext.vertexWeight g) * (localSign * localValue)) *
          (((-1 : ℂ) ^ S.card * vac.vertexWeight g) * vacuumValue) := by
  intro S _order _f _fT _localFixed _localPairing localSign _localKernel localValue
    _vacuumKernel vacuumValue d htime
  have hpair :
      externalInsertionMixedAtomicOrderSign externalTime σ *
          d.mixedPairingValue ε β externalTime σ =
        localSign * (localValue * vacuumValue) := by
    simpa only [externalInsertionMixedAtomicOrderSign,
      ExternalInsertionWickDiagram.mixedPairingValue] using
      (externalInsertionOfSlotSplit_globalSign_mul_mixedPairingEvaluation_eq_localSign_mul
        ε β T ext vac externalTime σ htime)
  have hweight :
      (-1 : ℂ) ^ n * d.vertexWeight g =
        ((-1 : ℂ) ^ T.card * ext.vertexWeight g) *
          ((-1 : ℂ) ^ S.card * vac.vertexWeight g) := by
    have hcard : n = T.card + S.card := by
      simpa only [S, Fintype.card_sum, Fintype.card_coe,
        Finset.card_univ, Fintype.card_fin] using
        (Fintype.card_congr
          (Combinatorics.subsetSumSdiffEquiv (Finset.subset_univ T))).symm
    change (-1 : ℂ) ^ n *
      (ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac).vertexWeight g = _
    have hpow : (-1 : ℂ) ^ n =
        (-1 : ℂ) ^ T.card * (-1 : ℂ) ^ S.card := by
      simpa only [pow_add] using
        (congrArg (fun k : ℕ => (-1 : ℂ) ^ k) hcard)
    rw [hpow, ExternalInsertionDiagram.ofSlotSplit_vertexWeight]
    ring
  change (-1 : ℂ) ^ n *
      (externalInsertionMixedAtomicOrderSign externalTime σ *
        d.vertexWeight g * d.mixedPairingValue ε β externalTime σ) =
    (((-1 : ℂ) ^ T.card * ext.vertexWeight g) * (localSign * localValue)) *
      (((-1 : ℂ) ^ S.card * vac.vertexWeight g) * vacuumValue)
  calc
    _ = ((-1 : ℂ) ^ n * d.vertexWeight g) *
        (externalInsertionMixedAtomicOrderSign externalTime σ *
          d.mixedPairingValue ε β externalTime σ) := by ring
    _ = (((-1 : ℂ) ^ T.card * ext.vertexWeight g) *
          ((-1 : ℂ) ^ S.card * vac.vertexWeight g)) *
        (localSign * (localValue * vacuumValue)) := by
          rw [hweight, hpair]
    _ = _ := by ring

open Combinatorics

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
      ExternalInsertionWickDiagram.dysonFixedTimeAmplitude (ext.slotCongr e) ε β g externalTime (σ ∘ fT) := by
  intro fT localFixed localPairing localSign localKernel localValue e
  have hpair :
      (ext.slotCongr e).pairingInMixedOrder externalTime (σ ∘ fT) =
        localPairing :=
    ext.supportSlotCongr_pairingInMixedOrder T externalTime σ
  have hvertices :
      (ext.slotCongr e).vertexLabelSequence =
        (fun v => ext.vertexLabel (T.orderIsoOfFin rfl v)) :=
    funext (fun v => rfl)
  have hkernel :
      externalInsertionMixedTimeOrderedAtomicPairValue ε β
          (ext.slotCongr e).externalLabel externalTime
          (ext.slotCongr e).vertexLabelSequence (σ ∘ fT) = localKernel := by
    simp only [localKernel, ExternalInsertionDiagram.slotCongr_externalLabel, hvertices]
  have hvalue :
      ExternalInsertionWickDiagram.mixedPairingValue (ext.slotCongr e) ε β externalTime (σ ∘ fT) =
        localValue := by
    simp only [ExternalInsertionWickDiagram.mixedPairingValue, hpair, hkernel, localValue]
  have hweight : (ext.slotCongr e).vertexWeight g = ext.vertexWeight g :=
    ext.slotCongr_vertexWeight e g
  have hsign :
      localSign = externalInsertionMixedAtomicOrderSign externalTime (σ ∘ fT) := by
    simp only [localSign, externalInsertionMixedAtomicOrderSign, localFixed,
      Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, mul_one, Equiv.Perm.sign_symm]
  unfold ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
    ExternalInsertionWickDiagram.fixedTimeAmplitude
  rw [← hsign, hweight, hvalue]
  ring


/-- Pointwise Dyson factorization with the external-support sector expressed as
a standalone diagram on its canonical consecutive slots. The vacuum factor
retains its increasing complementary slot order and oriented Wick evaluation.
The vacuum-time chamber hypothesis is the same as in the local split theorem. -/
theorem externalInsertionOfSlotSplit_dysonFixedTimeAmplitude_eq_standalone_mul_vacuum
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let fT : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
    let e : ↥T ≃ ↥(Finset.univ : Finset (Fin T.card)) :=
      (T.orderIsoOfFin rfl).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin T.card => Finset.mem_univ i)).symm
    let vacuumKernel := flatVertexLegPairValue ε β
      (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)
    let vacuumValue : ℂ :=
      (vac.pairingInOrder order).evaluation
        ((vac.pairingInOrder order).weight Statistics.fermion) vacuumKernel
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    StrictAnti (σ ∘ f) →
      d.dysonFixedTimeAmplitude ε β g externalTime σ =
        ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
          (ext.slotCongr e) ε β g externalTime (σ ∘ fT) *
        (((-1 : ℂ) ^ S.card * vac.vertexWeight g) * vacuumValue) := by
  intro S order f fT e vacuumKernel vacuumValue d htime
  calc
    _ = _ :=
      externalInsertionOfSlotSplit_dysonFixedTimeAmplitude_eq_local_mul_vacuum
        ε β g T ext vac externalTime σ htime
    _ = _ := by
      rw [externalInsertionSupport_dysonFactor_eq_standardizedAmplitude
        ε β g T ext externalTime σ]

end Fermionic
end SecondQuantization
