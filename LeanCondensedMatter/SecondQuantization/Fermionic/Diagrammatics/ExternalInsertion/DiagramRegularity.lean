import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderSignature
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Amplitude

set_option linter.style.header false

/-!
# Regularity of arbitrary-external fermionic Dyson integrands

At fixed external times, the mixed atomic-leg order is constant on each finite
strict-comparison chamber. Free-Gibbs contractions between fixed canonical legs
vary continuously with interaction times. These facts give continuous chamber
representatives and measurable local boundedness of the full Dyson integrand.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The representative of a realized signature has the same mixed event ordering. -/
private theorem sameExternalInsertionOrderChamber_signatureBase {E n : ℕ}
    (externalTime : Fin (2 * E) → ℝ) (σ : Fin n → ℝ) :
    SameExternalInsertionOrderChamber externalTime
      (intervalIntegral.finiteSignatureBase (externalInsertionOrderSignature externalTime)
        (externalInsertionOrderSignature externalTime σ)) σ := by
  rw [sameExternalInsertionOrderChamber_iff_orderSignature_eq]
  exact intervalIntegral.finiteSignatureBase_signature_eq
    (externalInsertionOrderSignature externalTime) σ

/-- For two fixed canonical legs, the Gibbs contraction is continuous in all
interaction-time coordinates. -/
private theorem continuous_orderedExternalInsertionLegPairContraction
    {E n : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ)
    (q : Fin n → QuarticVertexLabel Mode)
    (a b : OrderedExternalInsertionLeg E n) :
    Continuous (fun σ : Fin n → ℝ =>
      timedFieldPairContraction ε β
        (orderedExternalInsertionLegField externalLabel externalTime q σ a)
        (orderedExternalInsertionLegField externalLabel externalTime q σ b)) := by
  rcases a with a | ⟨v, l⟩ <;> rcases b with b | ⟨w, k⟩ <;>
    simp only [timedFieldPairContraction_eq, orderedExternalInsertionLegField,
      orderedExternalInsertionLegTime, orderedExternalInsertionLegFieldLabel] <;>
    fun_prop

/-- Extend the Dyson integrand on a chamber to a globally continuous function by
freezing the mixed-leg permutation and pairing, but not the field times. -/
private noncomputable def ExternalInsertionWickDiagram.dysonFixedTimeChamberRepresentative
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ₀ : Fin n → ℝ) :
    (Fin n → ℝ) → ℂ :=
  let p := d.pairingInMixedOrder externalTime σ₀
  fun σ =>
    ((-1 : ℂ) ^ n * externalInsertionMixedAtomicOrderSign externalTime σ₀ *
      d.vertexWeight g * p.weight Common.Statistics.fermion) *
    ∏ pr ∈ p.pairs,
      timedFieldPairContraction ε β
        (orderedExternalInsertionLegField d.externalLabel externalTime
          d.vertexLabelSequence σ
          (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ₀ pr.1))
        (orderedExternalInsertionLegField d.externalLabel externalTime
          d.vertexLabelSequence σ
          (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ₀ pr.2))

private theorem ExternalInsertionWickDiagram.continuous_dysonFixedTimeChamberRepresentative
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ₀ : Fin n → ℝ) :
    Continuous (d.dysonFixedTimeChamberRepresentative ε β g externalTime σ₀) := by
  unfold ExternalInsertionWickDiagram.dysonFixedTimeChamberRepresentative
  apply continuous_const.mul
  apply continuous_finsetProd
  intro pr _
  exact continuous_orderedExternalInsertionLegPairContraction
    ε β d.externalLabel externalTime d.vertexLabelSequence
    (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ₀ pr.1)
    (externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ₀ pr.2)

private theorem ExternalInsertionWickDiagram.dysonFixedTimeChamberRepresentative_eq_of_sameChamber
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ₀ σ : Fin n → ℝ)
    (h : SameExternalInsertionOrderChamber externalTime σ₀ σ) :
    d.dysonFixedTimeChamberRepresentative ε β g externalTime σ₀ σ =
      d.dysonFixedTimeAmplitude ε β g externalTime σ := by
  have hlegs :=
    externalInsertionMixedTimeOrderedAtomicLegEquiv_eq_of_comparisons
      externalTime σ₀ σ h
  have hperm :
      externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ₀ =
        externalInsertionStandardToMixedAtomicPositionEquiv externalTime σ := by
    unfold externalInsertionStandardToMixedAtomicPositionEquiv
    rw [hlegs]
  have hpair : d.pairingInMixedOrder externalTime σ₀ =
      d.pairingInMixedOrder externalTime σ := by
    unfold ExternalInsertionDiagram.pairingInMixedOrder
    rw [hperm]
  have hsign : externalInsertionMixedAtomicOrderSign externalTime σ₀ =
      externalInsertionMixedAtomicOrderSign externalTime σ := by
    unfold externalInsertionMixedAtomicOrderSign
    rw [hperm]
  dsimp [ExternalInsertionWickDiagram.dysonFixedTimeChamberRepresentative,
    ExternalInsertionWickDiagram.dysonFixedTimeAmplitude,
    ExternalInsertionWickDiagram.fixedTimeAmplitude,
    ExternalInsertionWickDiagram.mixedPairingValue, Pairing.evaluation,
    externalInsertionMixedTimeOrderedAtomicPairValue,
    externalInsertionMixedTimeOrderedAtomicFieldFamily]
  rw [hsign, hpair, hlegs]
  ring

private theorem ExternalInsertionWickDiagram.measurable_dysonFixedTimeAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    Measurable (fun σ : Fin n → ℝ =>
      d.dysonFixedTimeAmplitude ε β g externalTime σ) := by
  apply intervalIntegral.measurable_of_finite_continuous_signature
    (signature := externalInsertionOrderSignature externalTime)
    (branch := fun s =>
      d.dysonFixedTimeChamberRepresentative ε β g externalTime
        (intervalIntegral.finiteSignatureBase (externalInsertionOrderSignature externalTime) s))
  · intro s
    simpa [externalInsertionOrderSignatureFiber] using
      measurableSet_externalInsertionOrderSignatureFiber externalTime s
  · intro s
    exact d.continuous_dysonFixedTimeChamberRepresentative ε β g externalTime
      (intervalIntegral.finiteSignatureBase (externalInsertionOrderSignature externalTime) s)
  · intro σ
    exact (d.dysonFixedTimeChamberRepresentative_eq_of_sameChamber
      ε β g externalTime
      (intervalIntegral.finiteSignatureBase (externalInsertionOrderSignature externalTime)
        (externalInsertionOrderSignature externalTime σ)) σ
      (sameExternalInsertionOrderChamber_signatureBase externalTime σ)).symm

/-- The arbitrary-external fermionic Dyson fixed-time integrand is measurable
and uniformly bounded on each finite interaction-time cube. -/
theorem ExternalInsertionWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    intervalIntegral.MeasurableLocallyBounded
      (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g externalTime σ) := by
  apply intervalIntegral.measurableLocallyBounded_of_finite_continuous_selection
    (g := fun s : ExternalInsertionOrderSignature E n =>
      d.dysonFixedTimeChamberRepresentative ε β g externalTime
        (intervalIntegral.finiteSignatureBase (externalInsertionOrderSignature externalTime) s))
  · exact d.measurable_dysonFixedTimeAmplitude ε β g externalTime
  · intro s
    exact d.continuous_dysonFixedTimeChamberRepresentative ε β g externalTime
      (intervalIntegral.finiteSignatureBase (externalInsertionOrderSignature externalTime) s)
  · intro σ
    refine ⟨externalInsertionOrderSignature externalTime σ, ?_⟩
    exact (d.dysonFixedTimeChamberRepresentative_eq_of_sameChamber
      ε β g externalTime
      (intervalIntegral.finiteSignatureBase (externalInsertionOrderSignature externalTime)
        (externalInsertionOrderSignature externalTime σ)) σ
      (sameExternalInsertionOrderChamber_signatureBase externalTime σ)).symm

end Fermionic
end SecondQuantization
