import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumComponentCorrespondence
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ComponentDecomposition

set_option linter.style.header false

/-!
# Vacuum-component equivalence for binary reassembly

Connected components of the quartic vacuum remainder are exactly the vacuum components of the
reassembled two-point diagram.  We identify them through their common interaction-vertex finsets.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The interaction part of the ambient component containing a vacuum vertex is its quartic vacuum
component block. -/
theorem TwoPointDiagram.interactionPart_componentBlock_vacuumEmbed
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    (v : ↥(S \ E)) :
    TwoPointDiagram.interactionPart
        ((TwoPointDiagram.reassembleExternalVacuum hE external vacuum).componentBlock
          (TwoPointDiagram.vacuumVertexEmbed hE v)) =
      vacuum.componentBlock v := by
  let full := TwoPointDiagram.reassembleExternalVacuum hE external vacuum
  ext x
  constructor
  · intro hx
    rw [TwoPointDiagram.mem_interactionPart] at hx
    rcases hx with ⟨hxS, hxBlock⟩
    have hreach : full.vertexGraph.Reachable
        (Sum.inr ⟨x, hxS⟩) (TwoPointDiagram.vacuumVertexEmbed hE v) :=
      (full.mem_componentBlock (TwoPointDiagram.vacuumVertexEmbed hE v)).1 hxBlock |>.2
    have hxNotE : x ∉ E := by
      intro hxE
      have hside := (TwoPointDiagram.reassembleExternalVacuum_reachable_preserves_externalPart
        hE external vacuum hreach)
      have hleft : TwoPointDiagram.VertexInExternalPart (E := E)
          (Sum.inr ⟨x, hxS⟩ : TwoPointVertex S) := hxE
      have hright := hside.mp hleft
      exact (TwoPointDiagram.not_vertexInExternalPart_vacuumEmbed hE v) hright
    let xv : ↥(S \ E) := ⟨x, Finset.mem_sdiff.mpr ⟨hxS, hxNotE⟩⟩
    have hq : vacuum.vertexGraph.Reachable xv v :=
      (TwoPointDiagram.reassembleExternalVacuum_vacuum_reachable_iff
        hE external vacuum xv v).mp (by simpa [xv] using hreach)
    exact (vacuum.mem_componentBlock v).2 ⟨xv.2, hq⟩
  · intro hx
    rcases (vacuum.mem_componentBlock v).1 hx with ⟨hxV, hreach⟩
    have hxS : x ∈ S := (Finset.mem_sdiff.mp hxV).1
    let xv : ↥(S \ E) := ⟨x, hxV⟩
    have hfull : full.vertexGraph.Reachable
        (TwoPointDiagram.vacuumVertexEmbed hE xv)
        (TwoPointDiagram.vacuumVertexEmbed hE v) :=
      (TwoPointDiagram.reassembleExternalVacuum_vacuum_reachable_iff
        hE external vacuum xv v).2 (by simpa [xv] using hreach)
    rw [TwoPointDiagram.mem_interactionPart]
    refine ⟨hxS, ?_⟩
    apply (full.mem_componentBlock (TwoPointDiagram.vacuumVertexEmbed hE v)).2
    refine ⟨hxS, ?_⟩
    simpa [xv, TwoPointDiagram.vacuumVertexEmbed] using hfull

private theorem TwoPointDiagram.vacuumPart_eq_of_interactionPart_eq
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (B C : d.componentPartition.parts)
    (hB : d.ComponentIsVacuum B) (hC : d.ComponentIsVacuum C)
    (h : TwoPointDiagram.interactionPart (B : Finset (TwoPointVertex S)) =
      TwoPointDiagram.interactionPart (C : Finset (TwoPointVertex S))) : B = C := by
  apply Subtype.ext
  ext x
  rcases x with e | v
  · constructor <;> intro hx
    · exact False.elim (hB ⟨e, hx⟩)
    · exact False.elim (hC ⟨e, hx⟩)
  · change (Sum.inr v : TwoPointVertex S) ∈ (B : Finset (TwoPointVertex S)) ↔ _
    rw [← TwoPointDiagram.mem_interactionPart_subtype,
      ← TwoPointDiagram.mem_interactionPart_subtype, h]

/-- Turn one ambient vacuum component into the corresponding quartic-vacuum component. -/
noncomputable def TwoPointDiagram.reassembledVacuumPartToQuarticPart
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E)) :
    (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vacuumComponentParts →
      vacuum.componentPartition.parts := by
  intro B
  let full := TwoPointDiagram.reassembleExternalVacuum hE external vacuum
  have hVac : full.ComponentIsVacuum B.1 := (full.mem_vacuumComponentParts B.1).1 B.2
  obtain ⟨x, hx⟩ := full.componentPartition.nonempty_of_mem_parts B.1.2
  have hxNoExt : ∀ e : Fin 2, x ≠ Sum.inl e := by
    intro e heq
    apply hVac
    exact ⟨e, by simpa [heq] using hx⟩
  cases hxval : x with
  | inl e => exact False.elim (hxNoExt e hxval)
  | inr v =>
      have hvB : (Sum.inr v : TwoPointVertex S) ∈ (B.1 : Finset (TwoPointVertex S)) := by
        simpa [hxval] using hx
      have hvNotE : v.1 ∉ E := by
        intro hvE
        have hBext : B.1 = full.externalComponentPart := by
          apply full.interactionPart_component_unique v B.1 full.externalComponentPart
          · exact (TwoPointDiagram.mem_interactionPart_subtype (B.1 : Finset _) v).2 hvB
          · rw [TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
              hE external vacuum]
            exact hvE
        exact hVac ((full.componentMeetsExternal_iff_eq_externalComponentPart B.1).2 hBext)
      let vv : ↥(S \ E) := ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, hvNotE⟩⟩
      exact ⟨vacuum.componentBlock vv, vacuum.componentBlock_mem_componentPartition vv⟩

/-- The preceding map preserves the interaction-vertex finset literally. -/
theorem TwoPointDiagram.interactionPart_reassembledVacuumPartToQuarticPart
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    (B : (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vacuumComponentParts) :
    TwoPointDiagram.interactionPart (B.1 : Finset (TwoPointVertex S)) =
      (TwoPointDiagram.reassembledVacuumPartToQuarticPart hE external vacuum B :
        Finset (Fin N)) := by
  let full := TwoPointDiagram.reassembleExternalVacuum hE external vacuum
  unfold TwoPointDiagram.reassembledVacuumPartToQuarticPart
  simp only
  split
  next e h => exact False.elim (by simpa using h)
  next v hvCase =>
    let vv : ↥(S \ E) :=
      ⟨v.1, Finset.mem_sdiff.mpr ⟨v.2, by
        intro hvE
        have hVac : full.ComponentIsVacuum B.1 := (full.mem_vacuumComponentParts B.1).1 B.2
        have hvB : (Sum.inr v : TwoPointVertex S) ∈ (B.1 : Finset (TwoPointVertex S)) := by
          simpa [hvCase] using Classical.choose_spec
            (full.componentPartition.nonempty_of_mem_parts B.1.2)
        have hEq : B.1 = full.externalComponentPart := by
          apply full.interactionPart_component_unique v B.1 full.externalComponentPart
          · exact (TwoPointDiagram.mem_interactionPart_subtype (B.1 : Finset _) v).2 hvB
          · rw [TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
              hE external vacuum]
            exact hvE
        exact hVac ((full.componentMeetsExternal_iff_eq_externalComponentPart B.1).2 hEq)⟩⟩
    have hvB : (Sum.inr v : TwoPointVertex S) ∈ (B.1 : Finset (TwoPointVertex S)) := by
      simpa [hvCase] using Classical.choose_spec
        (full.componentPartition.nonempty_of_mem_parts B.1.2)
    have hblock : full.componentBlock (Sum.inr v) = (B.1 : Finset (TwoPointVertex S)) :=
      (full.componentBlock_eq_iff_mem B.1.2 (Sum.inr v)).2 hvB
    have h := TwoPointDiagram.interactionPart_componentBlock_vacuumEmbed
      hE external vacuum vv
    change TwoPointDiagram.interactionPart (B.1 : Finset (TwoPointVertex S)) =
      vacuum.componentBlock vv
    rw [← hblock]
    simpa [vv, TwoPointDiagram.vacuumVertexEmbed] using h

/-- Vacuum components of the reassembled two-point diagram are equivalent to connected components
of the quartic vacuum remainder. -/
noncomputable def TwoPointDiagram.reassembledVacuumComponentEquiv
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E)) :
    (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vacuumComponentParts ≃
      vacuum.componentPartition.parts :=
  Equiv.ofBijective
    (TwoPointDiagram.reassembledVacuumPartToQuarticPart hE external vacuum)
    ⟨by
      intro B C hBC
      let full := TwoPointDiagram.reassembleExternalVacuum hE external vacuum
      apply Subtype.ext
      apply full.vacuumPart_eq_of_interactionPart_eq B.1 C.1
      · exact (full.mem_vacuumComponentParts B.1).1 B.2
      · exact (full.mem_vacuumComponentParts C.1).1 C.2
      rw [full.interactionPart_reassembledVacuumPartToQuarticPart hE external vacuum B,
        full.interactionPart_reassembledVacuumPartToQuarticPart hE external vacuum C]
      exact congrArg Subtype.val hBC,
    by
      intro Q
      obtain ⟨v, hv⟩ := vacuum.exists_componentBlock_eq_of_mem Q.2
      let full := TwoPointDiagram.reassembleExternalVacuum hE external vacuum
      let Bfin := full.componentBlock (TwoPointDiagram.vacuumVertexEmbed hE v)
      have hBpart : Bfin ∈ full.componentPartition.parts :=
        full.componentBlock_mem_componentPartition (TwoPointDiagram.vacuumVertexEmbed hE v)
      let B : full.componentPartition.parts := ⟨Bfin, hBpart⟩
      have hBVac : full.ComponentIsVacuum B := by
        apply (full.componentIsVacuum_iff_ne_externalComponentPart B).2
        intro hEq
        have hvInt : (v.1 : Fin N) ∈ TwoPointDiagram.interactionPart
            (B : Finset (TwoPointVertex S)) := by
          rw [show (B : Finset (TwoPointVertex S)) = Bfin by rfl]
          rw [full.interactionPart_componentBlock_vacuumEmbed hE external vacuum v]
          exact vacuum.self_mem_componentBlock v
        rw [hEq, TwoPointDiagram.interactionPart_externalComponent_reassembleExternalVacuum
          hE external vacuum] at hvInt
        exact (Finset.mem_sdiff.mp v.2).2 hvInt
      let Bsub : full.vacuumComponentParts :=
        ⟨B, (full.mem_vacuumComponentParts B).2 hBVac⟩
      refine ⟨Bsub, ?_⟩
      apply Subtype.ext
      rw [← hv]
      exact (full.interactionPart_reassembledVacuumPartToQuarticPart
        hE external vacuum Bsub).symm.trans
        (full.interactionPart_componentBlock_vacuumEmbed hE external vacuum v)⟩

end Common
end SecondQuantization
