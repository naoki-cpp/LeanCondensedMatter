import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabelIntegralCovariance
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentShuffleIntegrability
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentDysonIntegral
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition

set_option linter.style.header false

/-!
# The component-shuffle orbit of a diagram integrates to a product over its components

Summing the integrated Dyson amplitude over the component-shuffle relabelings of one fixed-external
two-point diagram gives the product of the component-local integrated factors, times the external
ordering sign.

Nothing new is proved here. The three inputs are already available:

* each shuffle term is the amplitude of an explicitly relabeled diagram under the ordered-simplex
  integral, by strict-order relabel covariance;
* the sum over shuffles of the localized integrands is the product over components of their
  ordered-simplex integrals, by the finite-family shuffle theorem;
* the coordinate count `n` and its `Finset.card` presentation differ only by `Fin.cast`.

In particular no per-diagram stabilizer or orbit cardinality enters: the shuffle type is summed over
directly, and each of its elements names a diagram through `relabelForComponentShuffle`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **Shuffle-orbit amplitude sum.** The integrated Dyson amplitudes of the component-shuffle
relabelings of a diagram sum to the external ordering sign times the product of the component-local
integrated factors. -/
theorem FixedExternalTwoPointWickDiagram.sum_componentInteractionShuffle_dysonAmplitude_relabelForComponentShuffle_eq_prod
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) :
    (∑ shuffle : d.1.ComponentInteractionShuffle,
        (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ') =
      twoPointExternalOrderSign τ τ' *
        ∏ B : d.1.componentPartition.parts,
          intervalIntegral.orderedSimplexIntegral (d.1.interactionComponentSize B) β
            (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
              d.1.canonicalComponentInteractionShuffle B) := by
  have hcard : n = (Finset.univ : Finset (Fin n)).card := by simp
  have hterm (shuffle : d.1.ComponentInteractionShuffle) :
      (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ' =
        twoPointExternalOrderSign τ τ' *
          intervalIntegral.orderedSimplexIntegral (Finset.univ : Finset (Fin n)).card β
            (d.1.interactionComponentShuffleIntegrand shuffle
              (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
                d.1.canonicalComponentInteractionShuffle)) := by
    have hcast :
        intervalIntegral.orderedSimplexIntegral n β
            (fun σ =>
              (d.relabelForComponentShuffle shuffle).dysonFixedTimeAmplitude ε β g τ τ' σ) =
          intervalIntegral.orderedSimplexIntegral (Finset.univ : Finset (Fin n)).card β
            (fun σ =>
              (d.relabelForComponentShuffle shuffle).dysonFixedTimeAmplitude ε β g τ τ'
                (ambientToTwoPointSlotTimePermutation σ)) :=
      intervalIntegral.orderedSimplexIntegral_cast hcard β _
    rw [(d.relabelForComponentShuffle
        shuffle).dysonAmplitude_eq_orderedSimplexIntegral_dysonFixedTimeAmplitude ε β g τ τ',
      hcast,
      ← d.orderedSimplexIntegral_externalSign_mul_componentShuffleIntegrand ε β hβ g τ τ' shuffle,
      intervalIntegral.orderedSimplexIntegral_smul]
  rw [Finset.sum_congr rfl fun shuffle _ => hterm shuffle, ← Finset.mul_sum,
    d.sum_componentInteractionShuffle_orderedSimplexIntegral_mixedComponentDysonLocalIntegrand_eq_prod
      ε β g τ τ' d.1.canonicalComponentInteractionShuffle]

/-- **Shuffle-orbit amplitude sum, split into external and vacuum.** The product over all components
regroups into the external component and the vacuum ones.

This is the form the linked-cluster factorization consumes: one distinguished factor carrying the
external legs, and a product of vacuum factors. No sign is left over between them — cross-component
crossings are even. -/
theorem FixedExternalTwoPointWickDiagram.sum_componentInteractionShuffle_dysonAmplitude_relabelForComponentShuffle_eq_external_mul_prod_vacuum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β) (g : QuarticVertexLabel Mode → ℂ) (τ τ' : ℝ) :
    (∑ shuffle : d.1.ComponentInteractionShuffle,
        (d.relabelForComponentShuffle shuffle).dysonAmplitude ε β g τ τ') =
      twoPointExternalOrderSign τ τ' *
        (intervalIntegral.orderedSimplexIntegral
            (d.1.interactionComponentSize d.1.externalComponentPart) β
            (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
              d.1.canonicalComponentInteractionShuffle d.1.externalComponentPart) *
          d.1.vacuumComponentParts.prod fun B =>
            intervalIntegral.orderedSimplexIntegral (d.1.interactionComponentSize B) β
              (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
                d.1.canonicalComponentInteractionShuffle B)) := by
  rw [d.sum_componentInteractionShuffle_dysonAmplitude_relabelForComponentShuffle_eq_prod
      ε β hβ g τ τ',
    d.1.prod_componentParts_eq_external_mul_prod_vacuum fun B =>
      intervalIntegral.orderedSimplexIntegral (d.1.interactionComponentSize B) β
        (d.mixedComponentDysonLocalIntegrand ε β g τ τ'
          d.1.canonicalComponentInteractionShuffle B)]

omit [LinearOrder Mode] in
open Classical in
/-- **The diagram sum organized by which slots are external.**

Every fixed-external diagram determines the interaction vertices of its external component, so the
sum over all diagrams is the sum over that choice of the sum over the diagrams realizing it. This is
the organization the linked-cluster factorization needs: for a fixed pair of pieces, varying which
slots are external is exactly the shuffle freedom that turns one global ordered-simplex integral into
a product of two local ones. -/
theorem FixedExternalTwoPointWickDiagram.sum_eq_sum_fiberwise_externalInteractionPart
    {n : ℕ} {i j : Mode} {M : Type*} [AddCommMonoid M]
    (F : FixedExternalTwoPointWickDiagram Mode n i j → M) :
    (∑ d : FixedExternalTwoPointWickDiagram Mode n i j, F d) =
      ∑ T ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ d ∈ Finset.univ.filter fun d : FixedExternalTwoPointWickDiagram Mode n i j =>
            d.1.externalInteractionPart = T, F d :=
  (Finset.sum_fiberwise_of_maps_to
    (fun _ _ => Finset.mem_powerset.2 (Finset.subset_univ _)) F).symm

end Fermionic
end SecondQuantization
