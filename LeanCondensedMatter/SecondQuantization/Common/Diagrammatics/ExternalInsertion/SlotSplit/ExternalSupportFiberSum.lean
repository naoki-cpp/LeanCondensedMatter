import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportFiber
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Equiv.Basic

set_option linter.style.header false

/-!
# Finite sums over external-support fibers

The canonical external-support subset partitions arbitrary external-insertion diagrams into
fibers. Reindexing each fiber by the vacuum-free external diagram and the complementary
quartic diagram gives a finite double sum. This is a purely combinatorial identity: no
integral, fermionic sign, or Dyson coefficient is required.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

open Classical in
/-- Reindex a finite sum over arbitrary external-insertion diagrams by their externally
supported interaction slots and the corresponding vacuum-free / quartic diagram pair.

The supported slot subsets are indexed by a subtype rather than a dependent `Sigma`
equivalence, so each fiber can be reindexed independently. -/
theorem ExternalInsertionDiagram.sum_eq_sum_externalSupportFiber
    [Fintype ExternalLabel] [Fintype InternalLabel]
    (S : Finset (Fin N)) {M : Type*} [AddCommMonoid M]
    (F : ExternalInsertionDiagram ExternalLabel InternalLabel E N S → M) :
    (∑ d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S, F d) =
      ∑ T : {T : Finset (Fin N) // T ⊆ S},
        ∑ p : {ext : ExternalInsertionDiagram ExternalLabel InternalLabel E N T.1 //
            HasNoVacuumComponent ext.vertexGraph} ×
              QuarticDiagram InternalLabel N (S \ T.1),
          F ((ExternalInsertionDiagram.externalSupportFiberEquiv T.2).symm p).1 := by
  classical
  let g (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
      {T : Finset (Fin N) // T ⊆ S} :=
    ⟨d.externallySupportedInteractionPart, d.externallySupportedInteractionPart_subset⟩
  rw [← Fintype.sum_fiberwise g F]
  refine Finset.sum_congr rfl fun T _ => ?_
  let e : {d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S //
        d.externallySupportedInteractionPart = T.1} ≃ {d // g d = T} :=
    (Equiv.refl _).subtypeEquiv (fun d => by
      change d.externallySupportedInteractionPart = T.1 ↔ g d = T
      exact ⟨fun h => Subtype.ext h, fun h => congrArg (fun t => t.1) h⟩)
  exact (Equiv.sum_comp
    ((ExternalInsertionDiagram.externalSupportFiberEquiv T.2).symm.trans e)
    (fun d => F d.1)).symm

end Common
end SecondQuantization
