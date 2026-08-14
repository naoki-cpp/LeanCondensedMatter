import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DiagramSumIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberProductIntegrand

set_option linter.style.header false

/-!
# Binary ordered-simplex product for the fixed-fiber factors

`FiberProductIntegrand` identifies the signed pointwise amplitude in one external-slot fiber with an
external two-point factor times a fixed-order quartic vacuum factor.  The coefficientwise
linked-cluster theorem next sums the ambient interleavings of those two local time families.

This module records the scalar endpoint of that analytic step.  It applies the existing measurable
binary ordered-simplex shuffle theorem directly: the external signed amplitude already has the
required measurable local boundedness, while the quartic contraction integrand is continuous.
No new shuffle decomposition is introduced here.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {i j : Mode}

/-- Summing all ambient binary interleavings of a signed connected two-point integrand and a signed
fixed-order quartic vacuum integrand gives the product of their ordered-simplex amplitudes.

This is the analytic product theorem consumed after the external-slot subsets are reindexed by
`SlotShuffle.leftSlots` in the coefficientwise linked-cluster convolution. -/
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
      (continuous_contractionIntegrand ε β vac order).measurableLocallyBounded
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
