import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ExternalInsertion.SlotSplit.ExternalSupportFiber

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
  rw [(Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (ExternalInsertionDiagram
      ExternalLabel InternalLabel E N S)))
    (t := (Finset.univ : Finset {T : Finset (Fin N) // T ⊆ S}))
    (g := fun d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S =>
      (⟨d.externallySupportedInteractionPart,
        d.externallySupportedInteractionPart_subset⟩ :
          {T : Finset (Fin N) // T ⊆ S}))
    (fun _ _ => Finset.mem_univ _) F).symm]
  refine Finset.sum_congr rfl fun T _ => ?_
  have hfilter :
      (Finset.univ : Finset (ExternalInsertionDiagram
        ExternalLabel InternalLabel E N S)).filter
          (fun d => (⟨d.externallySupportedInteractionPart,
              d.externallySupportedInteractionPart_subset⟩ :
                {T : Finset (Fin N) // T ⊆ S}) = T) =
        (Finset.univ : Finset (ExternalInsertionDiagram
          ExternalLabel InternalLabel E N S)).filter
            (fun d => d.externallySupportedInteractionPart = T.1) := by
    ext d
    cases T with
    | mk T hT => simp
  rw [hfilter]
  rw [Finset.sum_subtype
    (p := fun d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S =>
      d.externallySupportedInteractionPart = T.1)
    _ (fun x => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]) F]
  exact (Equiv.sum_comp
    (ExternalInsertionDiagram.externalSupportFiberEquiv T.2).symm
    (fun d => F d.1)).symm

end Common
end SecondQuantization
