import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableRegularity
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.ImaginaryTimeOrderSignature
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

/-- Extend the Dyson integrand on a chamber to a globally continuous function by
freezing the mixed-leg permutation and pairing, but not the field times. -/
private noncomputable def ExternalInsertionWickDiagram.dysonFixedTimeChamberRepresentative
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ₀ : Fin n → ℝ) :
    (Fin n → ℝ) → ℂ :=
  let p := d.pairingInMixedOrder externalTime σ₀
  let order := externalInsertionMixedTimeOrderedAtomicLegEquiv externalTime σ₀
  fun σ =>
    let fields := (orderedExternalInsertionLegField d.externalLabel externalTime
      d.vertexLabelSequence σ) ∘ order
    ((-1 : ℂ) ^ n * externalInsertionMixedAtomicOrderSign externalTime σ₀ *
      d.vertexWeight g * p.weight Common.Statistics.fermion) *
    ∏ pr ∈ p.pairs,
      grandCanonicalTimedFieldPairContraction ε β 0 (fields pr.1) (fields pr.2)

private theorem ExternalInsertionWickDiagram.dysonFixedTimeChamberRepresentative_eq_of_sameChamber
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) (σ₀ σ : Fin n → ℝ)
    (hSignature : externalInsertionOrderSignature externalTime σ₀ =
      externalInsertionOrderSignature externalTime σ) :
    d.dysonFixedTimeChamberRepresentative ε β g externalTime σ₀ σ =
      d.dysonFixedTimeAmplitude ε β g externalTime σ := by
  have hlegs :=
    externalInsertionMixedTimeOrderedAtomicLegEquiv_eq_of_comparisons
      externalTime σ₀ σ
      ((externalInsertionOrderSignature_eq_iff externalTime σ₀ σ).mp hSignature)
  dsimp [ExternalInsertionWickDiagram.dysonFixedTimeChamberRepresentative,
    ExternalInsertionWickDiagram.dysonFixedTimeAmplitude,
    ExternalInsertionWickDiagram.fixedTimeAmplitude,
    ExternalInsertionWickDiagram.mixedPairingValue, Pairing.evaluation,
    externalInsertionMixedTimeOrderedAtomicPairValue,
    externalInsertionMixedTimeOrderedAtomicFieldFamily,
    externalInsertionMixedAtomicOrderSign,
    ExternalInsertionDiagram.pairingInMixedOrder,
    externalInsertionMixedTimeAmbientPositionEquiv,
    externalInsertionStandardToMixedAtomicPositionEquiv]
  rw [hlegs]
  ring

/-- The arbitrary-external fermionic Dyson fixed-time integrand is measurable
and uniformly bounded on each finite interaction-time cube. -/
theorem ExternalInsertionWickDiagram.measurableLocallyBounded_dysonFixedTimeAmplitude
    {E n : ℕ} (d : ExternalInsertionWickDiagram Mode E n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalTime : Fin (2 * E) → ℝ) :
    intervalIntegral.MeasurableLocallyBounded
      (fun σ : Fin n → ℝ => d.dysonFixedTimeAmplitude ε β g externalTime σ) := by
  apply intervalIntegral.measurableLocallyBounded_of_finite_continuous_signature
    (signature := externalInsertionOrderSignature externalTime)
    (branch := fun s =>
      d.dysonFixedTimeChamberRepresentative ε β g externalTime
        (intervalIntegral.finiteSignatureBase (externalInsertionOrderSignature externalTime) s))
  · intro s
    simpa [externalInsertionOrderSignatureFiber] using
      measurableSet_externalInsertionOrderSignatureFiber externalTime s
  · intro s
    unfold ExternalInsertionWickDiagram.dysonFixedTimeChamberRepresentative
    apply continuous_const.mul
    apply continuous_finsetProd
    intro pr _
    simp only [grandCanonicalTimedFieldPairContraction_eq, Function.comp_apply,
      orderedExternalInsertionLegField, orderedExternalInsertionLegTime,
      orderedExternalInsertionLegFieldLabel]
    split <;> split <;> fun_prop
  · intro σ
    exact (d.dysonFixedTimeChamberRepresentative_eq_of_sameChamber
      ε β g externalTime
      (intervalIntegral.finiteSignatureBase (externalInsertionOrderSignature externalTime)
        (externalInsertionOrderSignature externalTime σ)) σ
      (intervalIntegral.finiteSignatureBase_signature_eq
        (externalInsertionOrderSignature externalTime) σ)).symm

end Fermionic
end SecondQuantization
