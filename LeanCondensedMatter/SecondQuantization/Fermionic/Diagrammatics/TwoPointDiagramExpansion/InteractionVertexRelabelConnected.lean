import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.InteractionVertexRelabel

set_option linter.style.header false

/-!
# Connected fixed-diagram sums under interaction relabeling

The full interaction-slot relabel equivalence restricts to the externally connected subtype. This
is the finite-sum form used by the external-leg linked-cluster theorem; no orbit or stabilizer is
introduced.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*}

/-- Fixed-external explicit-slot diagrams with no vacuum component. -/
abbrev ExternallyConnectedFixedExternalTwoPointWickDiagram
    (Mode : Type*) (n : ℕ) (i j : Mode) :=
  {d : FixedExternalTwoPointWickDiagram Mode n i j // d.1.IsExternallyConnected}

/-- Interaction-slot relabeling restricts to externally connected fixed diagrams. -/
noncomputable def externallyConnectedFixedExternalTwoPointWickDiagramRelabelEquiv
    {n : ℕ} (i j : Mode) (π : Equiv.Perm (Fin n)) :
    ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j ≃
      ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j where
  toFun d := ⟨d.1.relabelInteractionVertices π,
    (d.1.relabelInteractionVertices_isExternallyConnected_iff π).2 d.2⟩
  invFun d := ⟨d.1.relabelInteractionVertices π.symm,
    (d.1.relabelInteractionVertices_isExternallyConnected_iff π.symm).2 d.2⟩
  left_inv d := by
    apply Subtype.ext
    exact d.1.relabelInteractionVertices_symm π
  right_inv d := by
    apply Subtype.ext
    exact d.1.relabelInteractionVertices_symm_relabel π

/-- A finite sum over connected fixed-external diagrams is invariant under interaction relabeling. -/
theorem sum_relabelInteractionVertices_externallyConnected
    [Fintype Mode] {n : ℕ} (i j : Mode) (π : Equiv.Perm (Fin n))
    (F : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j → ℂ) :
    ∑ d : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j,
        F ((externallyConnectedFixedExternalTwoPointWickDiagramRelabelEquiv i j π) d) =
      ∑ d : ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j, F d := by
  classical
  letI : Fintype (ExternallyConnectedFixedExternalTwoPointWickDiagram Mode n i j) :=
    Fintype.ofFinite _
  exact Equiv.sum_comp
    (externallyConnectedFixedExternalTwoPointWickDiagramRelabelEquiv i j π) F

end Fermionic
end SecondQuantization
