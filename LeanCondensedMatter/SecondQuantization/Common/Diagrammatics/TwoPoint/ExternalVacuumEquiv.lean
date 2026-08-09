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

/-- With the external interaction subset fixed, binary external/vacuum reassembly is injective in
the connected external core and vacuum remainder. -/
theorem TwoPointDiagram.reassembleExternalVacuum_injective_fixed
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
  rintro ⟨E, xdata⟩ ⟨F, ydata⟩ hxy
  have hEFval : E.1 = F.1 := by
    calc
      E.1 = (TwoPointDiagram.reassembleExternalVacuumData ⟨E, xdata⟩).externalInteractionPart := by
        symm
        exact TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
          E.2 xdata.1 xdata.2
      _ = (TwoPointDiagram.reassembleExternalVacuumData ⟨F, ydata⟩).externalInteractionPart :=
        congrArg TwoPointDiagram.externalInteractionPart hxy
      _ = F.1 :=
        TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
          F.2 ydata.1 ydata.2
  have hEF : E = F := Subtype.ext hEFval
  subst F
  have hdata : xdata = ydata :=
    TwoPointDiagram.reassembleExternalVacuum_injective_fixed E.2 hxy
  exact Sigma.ext rfl (heq_of_eq hdata)

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

/-- Decomposing a reassembled binary external/vacuum diagram recovers the source data exactly. -/
theorem TwoPointDiagram.decomposeExternalVacuum_reassembleExternalVacuumData
    {S : Finset (Fin N)}
    (x : TwoPointDiagram.ExternalVacuumDecomposition ExternalLabel InternalLabel N S) :
    (TwoPointDiagram.reassembleExternalVacuumData x).decomposeExternalVacuum = x := by
  rw [← TwoPointDiagram.externalVacuumDecompositionEquiv_apply]
  change TwoPointDiagram.externalVacuumDecompositionEquiv S
      ((TwoPointDiagram.externalVacuumDecompositionEquiv S).symm x) = x
  exact (TwoPointDiagram.externalVacuumDecompositionEquiv S).apply_symm_apply x

end Common
end SecondQuantization
