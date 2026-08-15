import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DiagramSumIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalPieceAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberVacuumIntegrand

set_option linter.style.header false

/-!
# Binary ordered-simplex product for the fixed-fiber factors

The fixed-fiber pointwise product identity is kept here together with the scalar binary-shuffle
endpoint that consumes it. The external signed amplitude has the required measurable local
boundedness, while the quartic contraction integrand is continuous.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {i j : Mode}

/-- For an externally connected left piece and strictly decreasing inherited vacuum times, the
signed fixed-time amplitude of the reassembled diagram is the product of the standalone external
piece amplitude and the standalone fixed-order quartic vacuum integrand. -/
theorem fixedExternalOfSlotSplit_dysonFixedTimeAmplitude_eq_externalPiece_mul_quarticIntegrand
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    {n : ℕ} (T : Finset (Fin n))
    (ext : FixedExternalTwoPointWickDiagramOn Mode n T i j)
    (hext : ext.1.IsExternallyConnected)
    (vac : QuarticWickDiagram Mode n ((Finset.univ : Finset (Fin n)) \ T))
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (hσ : StrictAnti (σ ∘ slotSplitVacuumSlot T)) :
    let d := fixedExternalOfSlotSplit T ext vac
    d.dysonFixedTimeAmplitude ε β g τ τ' σ =
      d.externalPiece.dysonFixedTimeAmplitude ε β g τ τ' (d.1.externalPieceTimes σ) *
        ((-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g *
          vac.contractionIntegrand ε β (slotSplitVacuumOrder T)
            (σ ∘ slotSplitVacuumSlot T)) := by
  classical
  let d := fixedExternalOfSlotSplit T ext vac
  change d.dysonFixedTimeAmplitude ε β g τ τ' σ = _
  rw [d.dysonFixedTimeAmplitude_eq_external_mul_prod_vacuum ε β g τ τ' σ,
    d.mixedExternalDysonFixedTimeValue_eq_externalPiece ε β g τ τ' σ]
  have hvac :
      d.1.vacuumComponentParts.prod
          (d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ) =
        (-1 : ℂ) ^ ((Finset.univ : Finset (Fin n)) \ T).card * vac.couplingWeight g *
          vac.contractionIntegrand ε β (slotSplitVacuumOrder T)
            (σ ∘ slotSplitVacuumSlot T) := by
    simpa [d] using
      (fixedExternalOfSlotSplit_prod_vacuumDysonFixedTimeValue_eq_quarticIntegrand
        ε β g T ext hext vac τ τ' σ hσ)
  rw [hvac]

/-- Summing all ambient binary interleavings of a signed connected two-point integrand and a signed
fixed-order quartic vacuum integrand gives the product of their ordered-simplex amplitudes. -/
theorem sum_slotShuffle_externalDyson_mul_quarticIntegrand_eq_mul
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) {m N : ℕ} {S : Finset (Fin N)}
    (ext : FixedExternalTwoPointWickDiagram Mode m i j)
    (vac : QuarticWickDiagram Mode N S)
    (order : Common.QuarticVertexOrder S) :
    (∑ shuffle : Combinatorics.BinaryShuffle.SlotShuffle m S.card,
      intervalIntegral.orderedSimplexIntegral (m + S.card) β
        (shuffle.integrand
          (fun σ => ext.dysonFixedTimeAmplitude ε β g τ τ' σ)
          (fun σ =>
            (-1 : ℂ) ^ S.card * vac.couplingWeight g *
              vac.contractionIntegrand ε β order σ))) =
      ext.dysonAmplitude ε β g τ τ' *
        ((-1 : ℂ) ^ S.card * vac.couplingWeight g *
          vac.orderedSimplexContribution ε β order) := by
  have hext :
      intervalIntegral.MeasurableLocallyBounded
        (fun σ : Fin m → ℝ => ext.dysonFixedTimeAmplitude ε β g τ τ' σ) :=
    ext.measurableLocallyBounded_dysonFixedTimeAmplitude ε β g τ τ'
  have hvac :
      intervalIntegral.MeasurableLocallyBounded
        (fun σ : Fin S.card → ℝ =>
          (-1 : ℂ) ^ S.card * vac.couplingWeight g *
            vac.contractionIntegrand ε β order σ) :=
    (intervalIntegral.measurableLocallyBounded_const
      ((-1 : ℂ) ^ S.card * vac.couplingWeight g)).mul
      (intervalIntegral.Continuous.measurableLocallyBounded
        (continuous_contractionIntegrand ε β vac order))
  simpa [FixedExternalTwoPointWickDiagram.dysonFixedTimeAmplitude,
    FixedExternalTwoPointWickDiagram.dysonAmplitude,
    FixedExternalTwoPointWickDiagram.orderedSimplexContribution,
    QuarticWickDiagram.orderedSimplexContribution,
    intervalIntegral.orderedSimplexIntegral_smul] using
    (Combinatorics.BinaryShuffle.sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul_of_measurableLocallyBounded
      m S.card β
      (fun σ => ext.dysonFixedTimeAmplitude ε β g τ τ' σ)
      (fun σ =>
        (-1 : ℂ) ^ S.card * vac.couplingWeight g *
          vac.contractionIntegrand ε β order σ)
      hext hvac)

end Fermionic
end SecondQuantization
