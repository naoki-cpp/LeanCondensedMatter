import LeanCondensedMatter.Analysis.OrderedSimplex.BinarySlotShuffle
import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableFiniteSum
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.AmplitudeFactorization
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.IntegratedDiagramSum

set_option linter.style.header false

/-!
# Binary external/vacuum shuffle product

This module isolates the analytic binary-shuffle step used by the external-leg linked-cluster
theorem. Once a reassembled fixed diagram agrees away from interaction-time diagonals with the
binary shuffled product of its connected external core and fixed-order vacuum remainder, the
ordered-simplex a.e. congruence and measurable binary-shuffle theorem give the integrated product
immediately.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Combinatorics.BinaryShuffle

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The fixed-order quartic vacuum contraction integrand on the explicit `Fin m` slot presentation. -/
noncomputable def explicitVacuumContractionIntegrand
    (ε : Mode → ℝ) (β : ℝ) {m : ℕ}
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m))) :
    (Fin m → ℝ) → ℂ :=
  fun σ => vacuum.contractionIntegrand ε β (explicitQuarticVertexOrder m)
    (fun r => σ (Fin.cast (by simp) r))

/-- The explicit-slot vacuum integrand integrates to the existing fixed-order quartic simplex
contribution. -/
theorem orderedSimplexIntegral_explicitVacuumContractionIntegrand
    (ε : Mode → ℝ) (β : ℝ) {m : ℕ}
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m))) :
    intervalIntegral.orderedSimplexIntegral m β
        (explicitVacuumContractionIntegrand ε β vacuum) =
      vacuum.orderedSimplexContribution ε β (explicitQuarticVertexOrder m) := by
  unfold explicitVacuumContractionIntegrand QuarticWickDiagram.orderedSimplexContribution
  let hcard : (Finset.univ : Finset (Fin m)).card = m := by simp
  exact (intervalIntegral.orderedSimplexIntegral_cast hcard β
    (vacuum.contractionIntegrand ε β (explicitQuarticVertexOrder m))).symm

/-- The explicit-slot vacuum contraction integrand is measurably locally bounded. -/
theorem measurableLocallyBounded_explicitVacuumContractionIntegrand
    (ε : Mode → ℝ) (β : ℝ) {m : ℕ}
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m))) :
    intervalIntegral.MeasurableLocallyBounded
      (explicitVacuumContractionIntegrand ε β vacuum) := by
  have hcast : Continuous (fun σ : Fin m → ℝ =>
      fun r : Fin (Finset.univ : Finset (Fin m)).card => σ (Fin.cast (by simp) r)) := by
    exact continuous_pi fun r => continuous_apply (Fin.cast (by simp) r)
  have hcont : Continuous (explicitVacuumContractionIntegrand ε β vacuum) :=
    (continuous_contractionIntegrand ε β vacuum
      (explicitQuarticVertexOrder m)).comp hcast
  exact intervalIntegral.Continuous.measurableLocallyBounded hcont

set_option maxHeartbeats 1000000 in
/-- Injective-time binary external/vacuum factorization for one reassembled diagram. -/
theorem reassembleExternalVacuumSlotShuffle_dysonFixedTimeAmplitude_eq_integrand_of_injective
    {k m : ℕ} (i j : Mode)
    (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (shuffle : SlotShuffle k m)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ : Fin (k + m) → ℝ)
    (_hσ : Function.Injective σ) :
    (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).dysonFixedTimeAmplitude
        ε β g τ τ' σ =
      shuffle.integrand
        (fun σExternal =>
          external.1.dysonFixedTimeAmplitude ε β g τ τ' σExternal)
        (fun σVacuum =>
          ((-1 : ℂ) ^ m * vacuum.couplingWeight g) *
            explicitVacuumContractionIntegrand ε β vacuum σVacuum)
        σ := by
  let d := reassembleExternalVacuumSlotShuffle i j external vacuum shuffle
  change d.dysonFixedTimeAmplitude ε β g τ τ' σ = _
  rw [d.dysonFixedTimeAmplitude_eq_external_mul_prod_vacuum]
  rw [SlotShuffle.integrand]
  apply congrArg₂ (· * ·)
  · rw [d.mixedExternalDysonFixedTimeValue_eq_restricted]
    rw [external.dysonFixedTimeAmplitude_eq_external]
    rw [external.1.mixedExternalDysonFixedTimeValue_eq_restricted]
    simp?
  · simp?

/-- An injective-time pointwise binary external/vacuum factorization is sufficient to factor the
sum of reassembled integrated amplitudes. Equal-time walls are discarded only here, by the generic
ordered-simplex a.e. congruence theorem. -/
theorem sum_reassembleExternalVacuumSlotShuffle_dysonAmplitude_eq_mul_of_injective
    {k m : ℕ} (i j : Mode)
    (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ)
    (hpoint : ∀ (shuffle : SlotShuffle k m) (σ : Fin (k + m) → ℝ),
      Function.Injective σ →
        (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).dysonFixedTimeAmplitude
            ε β g τ τ' σ =
          shuffle.integrand
            (fun σExternal =>
              external.1.dysonFixedTimeAmplitude ε β g τ τ' σExternal)
            (fun σVacuum =>
              ((-1 : ℂ) ^ m * vacuum.couplingWeight g) *
                explicitVacuumContractionIntegrand ε β vacuum σVacuum)
            σ) :
    (∑ shuffle : SlotShuffle k m,
      (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).dysonAmplitude
        ε β g τ τ') =
      external.1.dysonAmplitude ε β g τ τ' *
        explicitVacuumFixedOrderAmplitude ε β g vacuum := by
  let f : (Fin k → ℝ) → ℂ := fun σExternal =>
    external.1.dysonFixedTimeAmplitude ε β g τ τ' σExternal
  let h : (Fin m → ℝ) → ℂ := fun σVacuum =>
    ((-1 : ℂ) ^ m * vacuum.couplingWeight g) *
      explicitVacuumContractionIntegrand ε β vacuum σVacuum
  have hf : intervalIntegral.MeasurableLocallyBounded f := by
    exact external.1.measurableLocallyBounded_dysonFixedTimeAmplitude ε β g τ τ'
  have hgBase : intervalIntegral.MeasurableLocallyBounded
      (explicitVacuumContractionIntegrand ε β vacuum) :=
    measurableLocallyBounded_explicitVacuumContractionIntegrand ε β vacuum
  have hg : intervalIntegral.MeasurableLocallyBounded h := by
    exact hgBase.const_mul ((-1 : ℂ) ^ m * vacuum.couplingWeight g)
  calc
    (∑ shuffle : SlotShuffle k m,
      (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).dysonAmplitude
        ε β g τ τ') =
      ∑ shuffle : SlotShuffle k m,
        intervalIntegral.orderedSimplexIntegral (k + m) β (fun σ =>
          (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).dysonFixedTimeAmplitude
            ε β g τ τ' σ) := by
      apply Finset.sum_congr rfl
      intro shuffle _
      exact (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle)
        |>.dysonAmplitude_eq_orderedSimplexIntegral_dysonFixedTimeAmplitude ε β g τ τ'
    _ = ∑ shuffle : SlotShuffle k m,
        intervalIntegral.orderedSimplexIntegral (k + m) β (shuffle.integrand f h) := by
      apply Finset.sum_congr rfl
      intro shuffle _
      apply intervalIntegral.orderedSimplexIntegral_congr_of_injective
      intro σ hσ
      simpa [f, h] using hpoint shuffle σ hσ
    _ = intervalIntegral.orderedSimplexIntegral k β f *
        intervalIntegral.orderedSimplexIntegral m β h := by
      exact sum_slotShuffle_orderedSimplexIntegral_integrand_eq_mul_of_measurableLocallyBounded
        k m β f h hf hg
    _ = external.1.dysonAmplitude ε β g τ τ' *
        explicitVacuumFixedOrderAmplitude ε β g vacuum := by
      dsimp [f, h]
      rw [external.1.dysonAmplitude_eq_orderedSimplexIntegral_dysonFixedTimeAmplitude]
      rw [intervalIntegral.orderedSimplexIntegral_smul]
      rw [orderedSimplexIntegral_explicitVacuumContractionIntegrand]
      rfl

/-- The binary external/vacuum shuffle sum factors with no caller-supplied transport hypothesis. -/
theorem sum_reassembleExternalVacuumSlotShuffle_dysonAmplitude_eq_mul
    {k m : ℕ} (i j : Mode)
    (external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j)
    (vacuum : QuarticWickDiagram Mode m (Finset.univ : Finset (Fin m)))
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    (∑ shuffle : SlotShuffle k m,
      (reassembleExternalVacuumSlotShuffle i j external vacuum shuffle).dysonAmplitude
        ε β g τ τ') =
      external.1.dysonAmplitude ε β g τ τ' *
        explicitVacuumFixedOrderAmplitude ε β g vacuum := by
  apply sum_reassembleExternalVacuumSlotShuffle_dysonAmplitude_eq_mul_of_injective
    i j external vacuum ε β g τ τ'
  intro shuffle σ hσ
  exact reassembleExternalVacuumSlotShuffle_dysonFixedTimeAmplitude_eq_integrand_of_injective
    i j external vacuum shuffle ε β g τ τ' σ hσ

/-- The fixed external-order fiber factors into its connected external contribution and the
normalized vacuum coefficient, with the binary-shuffle identity discharged internally. -/
theorem sum_fixedExternalTwoPointWickDiagramOfExternalOrder_eq_connected_mul_vacuum
    {k m : ℕ} (i j : Mode)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) :
    (∑ d : FixedExternalTwoPointWickDiagramOfExternalOrder Mode k m i j,
        d.1.dysonAmplitude ε β g τ τ') =
      (∑ external : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode k i j,
        external.1.dysonAmplitude ε β g τ τ') *
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) m := by
  apply sum_fixedExternalTwoPointWickDiagramOfExternalOrder_eq_connected_mul_vacuum_of_shuffle
    i j ε β g τ τ'
  intro external vacuum
  exact sum_reassembleExternalVacuumSlotShuffle_dysonAmplitude_eq_mul
    i j external vacuum ε β g τ τ'

end Fermionic
end SecondQuantization
