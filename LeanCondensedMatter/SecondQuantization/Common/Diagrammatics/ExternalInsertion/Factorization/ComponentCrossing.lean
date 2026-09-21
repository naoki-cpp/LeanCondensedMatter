import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.Pairing.ComponentPairEquiv
import LeanCondensedMatter.Combinatorics.PerfectPairing.ComponentCrossing
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight

set_option linter.style.header false

/-!
# Crossing decomposition for external-insertion components

For a generic external-insertion diagram, component-internal crossings need not account for the
entire global crossing parity. Distinct connected components can interleave in the canonical ambient
leg order, so their crossings contribute an explicit residual inter-component term.

This module isolates that residual exactly. It does not assume the quartic-only parity cancellation.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- Total oriented crossing count between distinct connected components of an external-insertion
diagram. -/
noncomputable def ExternalInsertionDiagram.interComponentCrossingCount
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) : ℕ :=
  d.pairing.interComponentCrossingCount d.componentPairEquiv

private theorem ExternalInsertionDiagram.componentCrossingCount_self
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S)
    (B : d.componentPartition.parts) :
    d.pairing.componentCrossingCount d.componentPairEquiv B B =
      (d.restrictComponent B).pairing.crossingCount := by
  classical
  rw [Combinatorics.Pairing.componentCrossingCount, Fintype.sum_prod_type,
    Combinatorics.Pairing.crossingCount_eq_sum_sum_crosses]
  exact Combinatorics.sum_sum_crosses_eq_of_equiv
    (fun p : (d.restrictComponent B).pairing.NormalizedPair =>
      (d.componentPairEquiv ⟨B, p⟩).1)
    (fun p : (d.restrictComponent B).pairing.NormalizedPair => p.1)
    (Equiv.refl (d.restrictComponent B).pairing.NormalizedPair)
    (fun p q => by
      simp only [Equiv.refl_apply]
      rw [d.componentPairEquiv_apply, d.componentPairEquiv_apply]
      have hmono : StrictMono (fun i => d.componentDiagramLeg B i) := by
        change StrictMono (fun i => d.componentDiagramLeg B i)
        exact (d.componentDiagramLegOrderEmbedding B).strictMono
      exact Combinatorics.crosses_map_iff
        (d.componentDiagramLeg B) hmono
        p.1.1 p.1.2 q.1.1 q.1.2)

/-- The ambient crossing count is the sum of all component-local crossing counts plus the residual
crossing count between distinct connected components. -/
theorem ExternalInsertionDiagram.crossingCount_eq_sum_components_add_inter
    {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.pairing.crossingCount =
      (∑ B : d.componentPartition.parts, (d.restrictComponent B).pairing.crossingCount) +
        d.interComponentCrossingCount := by
  rw [d.pairing.crossingCount_eq_sum_componentCrossingCount_diag_add_inter d.componentPairEquiv]
  apply congrArg (fun n : ℕ => n + d.interComponentCrossingCount)
  apply Finset.sum_congr rfl
  intro B _
  exact d.componentCrossingCount_self B

/-- The exchange-statistics weight factors into the residual inter-component exchange sign and the
product of component-local pairing weights. -/
theorem ExternalInsertionDiagram.weight_eq_inter_mul_prod_components
    (s : Statistics) {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    d.pairing.weight s =
      (s.zetaInt : ℂ) ^ d.interComponentCrossingCount *
        ∏ B : d.componentPartition.parts, (d.restrictComponent B).pairing.weight s := by
  classical
  simp only [Combinatorics.Pairing.weight]
  rw [d.crossingCount_eq_sum_components_add_inter, pow_add,
    ← Finset.prod_pow_eq_pow_sum]
  exact mul_comm _ _

end Common
end SecondQuantization
