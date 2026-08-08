import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumEquiv

set_option linter.style.header false

/-!
# Finite sums over the external/vacuum decomposition

The binary decomposition equivalence turns every finite sum over full two-point diagrams into a sum
over an interaction subset, one externally connected core on that subset, and one arbitrary quartic
vacuum diagram on the complement.  This is the only diagram-enumeration reindexing needed by the
normalized two-point linked-cluster theorem.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel M : Type*} {N : ℕ}

/-- Reindex a finite sum over all full two-point diagrams by the unique binary external/vacuum
decomposition. -/
theorem sum_twoPointDiagram_eq_sum_externalVacuum
    [Fintype ExternalLabel] [Fintype InternalLabel] [AddCommMonoid M]
    {S : Finset (Fin N)}
    (F : TwoPointDiagram ExternalLabel InternalLabel N S → M) :
    (∑ d : TwoPointDiagram ExternalLabel InternalLabel N S, F d) =
      ∑ E : {E : Finset (Fin N) // E ⊆ S},
        ∑ external : ExternallyConnectedTwoPointDiagram
            ExternalLabel InternalLabel N E.1,
          ∑ vacuum : QuarticDiagram InternalLabel N (S \ E.1),
            F (TwoPointDiagram.reassembleExternalVacuum E.2 external vacuum) := by
  rw [← Equiv.sum_comp
    (TwoPointDiagram.externalVacuumDecompositionEquiv
      (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) S)]
  simp [TwoPointDiagram.ExternalVacuumDecomposition,
    TwoPointDiagram.externalVacuumDecompositionEquiv_apply,
    TwoPointDiagram.decomposeExternalVacuum,
    TwoPointDiagram.reassembleExternalVacuumData,
    Fintype.sum_sigma]

/-- If a full-diagram weight factors under binary reassembly, its total sum is the subset convolution
of the externally connected and vacuum diagram sums. -/
theorem sum_twoPointDiagram_eq_sum_external_mul_vacuum
    [Fintype ExternalLabel] [Fintype InternalLabel]
    {S : Finset (Fin N)}
    (F : TwoPointDiagram ExternalLabel InternalLabel N S → ℂ)
    (Fexternal : ∀ E : {E : Finset (Fin N) // E ⊆ S},
      ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E.1 → ℂ)
    (Fvacuum : ∀ E : {E : Finset (Fin N) // E ⊆ S},
      QuarticDiagram InternalLabel N (S \ E.1) → ℂ)
    (hfactor : ∀ E external vacuum,
      F (TwoPointDiagram.reassembleExternalVacuum E.2 external vacuum) =
        Fexternal E external * Fvacuum E vacuum) :
    (∑ d : TwoPointDiagram ExternalLabel InternalLabel N S, F d) =
      ∑ E : {E : Finset (Fin N) // E ⊆ S},
        (∑ external : ExternallyConnectedTwoPointDiagram
            ExternalLabel InternalLabel N E.1, Fexternal E external) *
          (∑ vacuum : QuarticDiagram InternalLabel N (S \ E.1), Fvacuum E vacuum) := by
  rw [sum_twoPointDiagram_eq_sum_externalVacuum F]
  apply Finset.sum_congr rfl
  intro E _
  calc
    (∑ external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E.1,
        ∑ vacuum : QuarticDiagram InternalLabel N (S \ E.1),
          F (TwoPointDiagram.reassembleExternalVacuum E.2 external vacuum)) =
      ∑ external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E.1,
        ∑ vacuum : QuarticDiagram InternalLabel N (S \ E.1),
          Fexternal E external * Fvacuum E vacuum := by
        apply Finset.sum_congr rfl
        intro external _
        apply Finset.sum_congr rfl
        intro vacuum _
        exact hfactor E external vacuum
    _ = _ := by
      simp_rw [Finset.mul_sum]
      rw [← Finset.sum_mul]

end Common
end SecondQuantization
