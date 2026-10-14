import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumPairing

set_option linter.style.header false

/-!
# Pointwise Dyson factorization for external support and vacuum slots

The mixed atomic ordering sign and inter-sector pairing crossings cancel before the
Dyson signs and vertex couplings are split. The support-side factor is expressed in
its actual local mixed-time pairing coordinates; standardizing it as a diagram on
consecutive interaction slots is a separate reindexing step.
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
    let localFixed := externalInsertionLeftMixedToFixedEquiv T externalTime σ
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
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (ExternalInsertionDiagram.ofSlotSplit_dysonSign_mul_vertexWeight
        (S := (Finset.univ : Finset (Fin n)))
        (Finset.subset_univ T) ext vac g)
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

end Fermionic
end SecondQuantization
