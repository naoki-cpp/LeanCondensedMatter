import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonConnectedDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment

set_option linter.style.header false

/-!
# Normalized two-point linked-cluster theorem

This is the final owner for the finite-mode imaginary-time two-point LCT.  The structural input is
one connected component carrying the two distinguished external legs plus an arbitrary quartic
vacuum remainder.  The analytic input is the a.e. interaction-relabel covariance and integrated
component-shuffle factorization.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- Externally connected two-point diagrams on an arbitrary finite interaction set, with the two
external labels fixed to `T c_i c_j†`. -/
abbrev ConnectedFixedExternalTwoPointWickDiagramOn
    (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :=
  {d : Common.ExternallyConnectedTwoPointDiagram
      (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) N S //
    d.1.externalLabel = twoPointExternalLabels i j}

/-- Binary decomposition data for a fixed-external two-point diagram: a connected external core on
`E` and an arbitrary quartic vacuum diagram on the complementary interaction vertices. -/
abbrev FixedExternalVacuumDecomposition
    (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :=
  Σ E : {E : Finset (Fin N) // E ⊆ S},
    ConnectedFixedExternalTwoPointWickDiagramOn Mode N E.1 i j ×
      QuarticWickDiagram Mode N (S \ E.1)

/-- Forget only the proof that the external labels are fixed. -/
noncomputable def FixedExternalVacuumDecomposition.toCommon
    {S : Finset (Fin N)} {i j : Mode}
    (x : FixedExternalVacuumDecomposition Mode N S i j) :
    Common.TwoPointDiagram.ExternalVacuumDecomposition
      (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) N S :=
  ⟨x.1, x.2.1.1, x.2.2⟩

private theorem FixedExternalVacuumDecomposition.toCommon_injective
    {S : Finset (Fin N)} {i j : Mode} :
    Function.Injective
      (FixedExternalVacuumDecomposition.toCommon
        (Mode := Mode) (N := N) (S := S) (i := i) (j := j)) := by
  rintro ⟨E, external, vacuum⟩ ⟨F, external', vacuum'⟩ h
  dsimp [FixedExternalVacuumDecomposition.toCommon] at h
  cases h
  rfl

/-- Reassemble fixed-external binary decomposition data. -/
noncomputable def reassembleFixedExternalVacuumData
    {S : Finset (Fin N)} {i j : Mode}
    (x : FixedExternalVacuumDecomposition Mode N S i j) :
    FixedExternalTwoPointWickDiagramOn Mode N S i j :=
  ⟨Common.TwoPointDiagram.reassembleExternalVacuum x.1.2 x.2.1.1 x.2.2, by
    simpa using x.2.1.2⟩

private theorem reassembleFixedExternalVacuumData_injective
    {S : Finset (Fin N)} {i j : Mode} :
    Function.Injective
      (reassembleFixedExternalVacuumData
        (Mode := Mode) (N := N) (S := S) (i := i) (j := j)) := by
  intro x y h
  apply FixedExternalVacuumDecomposition.toCommon_injective
  apply Common.TwoPointDiagram.reassembleExternalVacuumData_injective
  exact congrArg Subtype.val h

private theorem reassembleFixedExternalVacuumData_surjective
    {S : Finset (Fin N)} {i j : Mode} :
    Function.Surjective
      (reassembleFixedExternalVacuumData
        (Mode := Mode) (N := N) (S := S) (i := i) (j := j)) := by
  intro d
  let external : ConnectedFixedExternalTwoPointWickDiagramOn Mode N
      d.1.externalInteractionPart i j :=
    ⟨⟨d.1.restrictExternalComponent,
      d.1.restrictExternalComponent_isExternallyConnected⟩, by
        simpa using d.2⟩
  let x : FixedExternalVacuumDecomposition Mode N S i j :=
    ⟨⟨d.1.externalInteractionPart, d.1.externalInteractionPart_subset⟩,
      external, d.1.restrictVacuumRemainder⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact d.1.reassemble_restrictExternal_restrictVacuumRemainder

/-- Fixed-external diagrams are exactly a connected external core on a subset of the interaction
vertices together with an arbitrary quartic vacuum remainder on the complement. -/
noncomputable def fixedExternalVacuumDecompositionEquiv
    (S : Finset (Fin N)) (i j : Mode) :
    FixedExternalTwoPointWickDiagramOn Mode N S i j ≃
      FixedExternalVacuumDecomposition Mode N S i j :=
  (Equiv.ofBijective
    (reassembleFixedExternalVacuumData
      (Mode := Mode) (N := N) (S := S) (i := i) (j := j))
    ⟨reassembleFixedExternalVacuumData_injective,
      reassembleFixedExternalVacuumData_surjective⟩).symm

/-- Reindex a finite sum over fixed-external two-point diagrams by the unique connected external
core and arbitrary vacuum remainder. -/
theorem sum_fixedExternalTwoPointWickDiagramOn_eq_sum_externalVacuum
    {S : Finset (Fin N)} (i j : Mode)
    (F : FixedExternalTwoPointWickDiagramOn Mode N S i j → ℂ) :
    (∑ d : FixedExternalTwoPointWickDiagramOn Mode N S i j, F d) =
      ∑ x : FixedExternalVacuumDecomposition Mode N S i j,
        F (reassembleFixedExternalVacuumData x) := by
  rw [← Equiv.sum_comp (fixedExternalVacuumDecompositionEquiv S i j).symm F]
  rfl

end Fermionic
end SecondQuantization
