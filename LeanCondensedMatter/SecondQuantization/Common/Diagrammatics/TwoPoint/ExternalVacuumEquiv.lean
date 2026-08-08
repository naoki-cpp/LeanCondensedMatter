import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumDecomposition

set_option linter.style.header false

/-!
# Binary external/vacuum decomposition equivalence

The connected external core and arbitrary vacuum remainder determine the full two-point diagram
uniquely. Together with the restriction/reassembly inverse law this packages the exact finite
reindexing used by the normalized linked-cluster theorem.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

private theorem TwoPointDiagram.reassembleExternalVacuum_injective_fixed
    {S E : Finset (Fin N)} (hE : E ⊆ S) :
    Function.Injective (fun p :
      ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E ×
        QuarticDiagram InternalLabel N (S \ E) =>
      TwoPointDiagram.reassembleExternalVacuum hE p.1 p.2) := by
  rintro ⟨external₁, vacuum₁⟩ ⟨external₂, vacuum₂⟩ hfull
  apply Prod.ext
  · apply Subtype.ext
    apply TwoPointDiagram.ext
    · have h := congrArg TwoPointDiagram.externalLabel hfull
      simpa [TwoPointDiagram.reassembleExternalVacuum] using h
    · funext v
      let vS : ↥S :=
        (TwoPointDiagram.interactionExternalVacuumEquiv hE).symm (Sum.inl v)
      have h := congrArg (fun d => d.vertexLabel vS) hfull
      simpa [vS, TwoPointDiagram.reassembleExternalVacuum] using h
    · apply Pairing.ext
      apply Equiv.ext
      intro leg
      let split := TwoPointDiagram.externalVacuumLegEquiv hE
      have h := congrArg
        (fun d => d.pairing.partner (split.symm (Sum.inl leg))) hfull
      simpa [split] using h
  · apply QuarticDiagram.ext
    · funext v
      let vS : ↥S :=
        (TwoPointDiagram.interactionExternalVacuumEquiv hE).symm (Sum.inr v)
      have h := congrArg (fun d => d.vertexLabel vS) hfull
      simpa [vS, TwoPointDiagram.reassembleExternalVacuum] using h
    · apply Pairing.ext
      apply Equiv.ext
      intro leg
      let split := TwoPointDiagram.externalVacuumLegEquiv hE
      have h := congrArg
        (fun d => d.pairing.partner (split.symm (Sum.inr leg))) hfull
      simpa [split] using h

/-- Reassemble binary external/vacuum decomposition data. -/
noncomputable def TwoPointDiagram.reassembleExternalVacuumData
    {S : Finset (Fin N)}
    (x : TwoPointDiagram.ExternalVacuumDecomposition ExternalLabel InternalLabel N S) :
    TwoPointDiagram ExternalLabel InternalLabel N S :=
  TwoPointDiagram.reassembleExternalVacuum x.1.2 x.2.1 x.2.2

/-- Reassembly of binary decomposition data is injective. -/
theorem TwoPointDiagram.reassembleExternalVacuumData_injective
    {S : Finset (Fin N)} :
    Function.Injective
      (TwoPointDiagram.reassembleExternalVacuumData
        (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) (N := N) (S := S)) := by
  intro x y hxy
  have hE : x.1.1 = y.1.1 := by
    calc
      x.1.1 = (TwoPointDiagram.reassembleExternalVacuumData x).externalInteractionPart := by
        symm
        exact TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
          x.1.2 x.2.1 x.2.2
      _ = (TwoPointDiagram.reassembleExternalVacuumData y).externalInteractionPart :=
        congrArg TwoPointDiagram.externalInteractionPart hxy
      _ = y.1.1 :=
        TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
          y.1.2 y.2.1 y.2.2
  have hEsub : x.1 = y.1 := Subtype.ext hE
  cases hEsub
  apply Sigma.ext rfl
  apply heq_of_eq
  exact TwoPointDiagram.reassembleExternalVacuum_injective_fixed x.1.2 hxy

/-- Every full two-point diagram is in the image of binary external/vacuum reassembly. -/
theorem TwoPointDiagram.reassembleExternalVacuumData_surjective
    {S : Finset (Fin N)} :
    Function.Surjective
      (TwoPointDiagram.reassembleExternalVacuumData
        (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) (N := N) (S := S)) := by
  intro d
  refine ⟨d.decomposeExternalVacuum, ?_⟩
  exact d.reassemble_restrictExternal_restrictVacuumRemainder

/-- Full two-point diagrams are equivalent to one connected external core on a subset of interaction
vertices together with one arbitrary quartic vacuum diagram on the complement. -/
noncomputable def TwoPointDiagram.externalVacuumDecompositionEquiv
    (S : Finset (Fin N)) :
    TwoPointDiagram ExternalLabel InternalLabel N S ≃
      TwoPointDiagram.ExternalVacuumDecomposition ExternalLabel InternalLabel N S :=
  (Equiv.ofBijective
    (TwoPointDiagram.reassembleExternalVacuumData
      (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) (N := N) (S := S))
    ⟨TwoPointDiagram.reassembleExternalVacuumData_injective,
      TwoPointDiagram.reassembleExternalVacuumData_surjective⟩).symm

/-- The explicit restriction map is the forward direction of the binary decomposition equivalence. -/
theorem TwoPointDiagram.externalVacuumDecompositionEquiv_apply
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S) :
    TwoPointDiagram.externalVacuumDecompositionEquiv S d = d.decomposeExternalVacuum := by
  apply TwoPointDiagram.reassembleExternalVacuumData_injective
  change TwoPointDiagram.reassembleExternalVacuumData
      (TwoPointDiagram.externalVacuumDecompositionEquiv S d) =
    TwoPointDiagram.reassembleExternalVacuumData d.decomposeExternalVacuum
  calc
    TwoPointDiagram.reassembleExternalVacuumData
        (TwoPointDiagram.externalVacuumDecompositionEquiv S d) = d := by
      exact (Equiv.ofBijective
        (TwoPointDiagram.reassembleExternalVacuumData
          (ExternalLabel := ExternalLabel) (InternalLabel := InternalLabel) (N := N) (S := S))
        ⟨TwoPointDiagram.reassembleExternalVacuumData_injective,
          TwoPointDiagram.reassembleExternalVacuumData_surjective⟩).apply_symm_apply d
    _ = TwoPointDiagram.reassembleExternalVacuumData d.decomposeExternalVacuum :=
      d.reassemble_restrictExternal_restrictVacuumRemainder.symm

end Common
end SecondQuantization
