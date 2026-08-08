import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumReassembleLaws
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.ComponentPartition

set_option linter.style.header false

/-!
# Vacuum graph inside an external/vacuum reassembly

The right summand of a binary reassembly is an induced copy of the quartic vacuum graph.  In
particular, its adjacency and reachability agree exactly with the original vacuum diagram.  This is
the structural bridge used to identify full-diagram vacuum components with the ordinary quartic
components already handled by the vacuum LCT.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

private theorem vacuumVertexEmbed_injective {S E : Finset (Fin N)} (hE : E ⊆ S) :
    Function.Injective (TwoPointDiagram.vacuumVertexEmbed hE) := by
  intro v w h
  exact Subtype.ext (Sum.inr.inj h)

/-- Quartic vacuum adjacency is preserved by binary reassembly. -/
theorem TwoPointDiagram.reassembleExternalVacuum_vacuum_adj
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    {v w : ↥(S \ E)} (hvw : vacuum.vertexGraph.Adj v w) :
    (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Adj
      (TwoPointDiagram.vacuumVertexEmbed hE v)
      (TwoPointDiagram.vacuumVertexEmbed hE w) := by
  rcases hvw with ⟨hne, leg, hv, hw⟩
  refine ⟨vacuumVertexEmbed_injective hE hne,
    (TwoPointDiagram.externalVacuumLegEquiv hE).symm (Sum.inr leg), ?_, ?_⟩
  · rw [TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_vacuum]
    exact congrArg (TwoPointDiagram.vacuumVertexEmbed hE) hv
  · rw [TwoPointDiagram.reassembleExternalVacuum_partner_vacuum,
      TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_vacuum]
    exact congrArg (TwoPointDiagram.vacuumVertexEmbed hE) hw

/-- Every ambient edge between vacuum-side vertices comes from the original quartic vacuum graph. -/
theorem TwoPointDiagram.reassembleExternalVacuum_vacuum_adj_iff
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    (v w : ↥(S \ E)) :
    (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Adj
        (TwoPointDiagram.vacuumVertexEmbed hE v)
        (TwoPointDiagram.vacuumVertexEmbed hE w) ↔
      vacuum.vertexGraph.Adj v w := by
  constructor
  · rintro ⟨hne, leg, hv, hw⟩
    let split := TwoPointDiagram.externalVacuumLegEquiv hE
    cases hsplit : split leg with
    | inl a =>
        have hleg : leg = split.symm (Sum.inl a) := by
          rw [← hsplit]
          exact split.symm_apply_apply leg
        have hvertex := TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_external
          hE a
        rw [← hleg, hv] at hvertex
        have hside : TwoPointDiagram.VertexInExternalPart (E := E)
            (TwoPointDiagram.vacuumVertexEmbed hE v) := by
          rw [hvertex]
          simp
        exact False.elim ((TwoPointDiagram.not_vertexInExternalPart_vacuumEmbed hE v) hside)
    | inr a =>
        have hleg : leg = split.symm (Sum.inr a) := by
          rw [← hsplit]
          exact split.symm_apply_apply leg
        have hv' := TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_vacuum hE a
        rw [← hleg, hv] at hv'
        have hva : vertexOfLeg a = v := vacuumVertexEmbed_injective hE hv'
        have hp := TwoPointDiagram.reassembleExternalVacuum_partner_vacuum
          hE external vacuum a
        have hw' := TwoPointDiagram.vertexOfLeg_externalVacuumLegEquiv_symm_vacuum
          hE (vacuum.pairing.partner a)
        rw [← hp, ← hleg, hw] at hw'
        have hwa : vertexOfLeg (vacuum.pairing.partner a) = w :=
          vacuumVertexEmbed_injective hE hw'
        exact ⟨by
          intro hvweq
          apply hne
          exact congrArg (TwoPointDiagram.vacuumVertexEmbed hE) hvweq,
          a, hva, hwa⟩
  · exact TwoPointDiagram.reassembleExternalVacuum_vacuum_adj hE external vacuum

/-- Vacuum-side reachability is exactly quartic-vacuum reachability. -/
theorem TwoPointDiagram.reassembleExternalVacuum_vacuum_reachable_iff
    {S E : Finset (Fin N)} (hE : E ⊆ S)
    (external : ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N E)
    (vacuum : QuarticDiagram InternalLabel N (S \ E))
    (v w : ↥(S \ E)) :
    (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Reachable
        (TwoPointDiagram.vacuumVertexEmbed hE v)
        (TwoPointDiagram.vacuumVertexEmbed hE w) ↔
      vacuum.vertexGraph.Reachable v w := by
  rw [SimpleGraph.reachable_iff_reflTransGen, SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y z hxy hyz ih =>
        have hzVac : ¬ TwoPointDiagram.VertexInExternalPart (E := E) z := by
          have hxVac : ¬ TwoPointDiagram.VertexInExternalPart (E := E)
              (TwoPointDiagram.vacuumVertexEmbed hE v) :=
            TwoPointDiagram.not_vertexInExternalPart_vacuumEmbed hE v
          intro hzExt
          apply hxVac
          have hreach :
              (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Reachable
                (TwoPointDiagram.vacuumVertexEmbed hE v) z := by
            rw [SimpleGraph.reachable_iff_reflTransGen]
            exact Relation.ReflTransGen.tail hxy hyz
          exact (TwoPointDiagram.reassembleExternalVacuum_reachable_preserves_externalPart
            hE external vacuum hreach).mpr hzExt
        rcases z with e | zint
        · exact False.elim (hzVac trivial)
        · have hznot : zint.1 ∉ E := hzVac
          let zVac : ↥(S \ E) :=
            ⟨zint.1, Finset.mem_sdiff.mpr ⟨zint.2, hznot⟩⟩
          -- Recover the predecessor as a vacuum vertex from the already translated prefix.
          have hyVac : y = TwoPointDiagram.vacuumVertexEmbed hE
              ((Classical.choose (show ∃ yv : ↥(S \ E),
                y = TwoPointDiagram.vacuumVertexEmbed hE yv from by
                  have hySide : ¬ TwoPointDiagram.VertexInExternalPart (E := E) y := by
                    intro hyExt
                    have hxVac := TwoPointDiagram.not_vertexInExternalPart_vacuumEmbed hE v
                    apply hxVac
                    have hreach :
                        (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Reachable
                          (TwoPointDiagram.vacuumVertexEmbed hE v) y := by
                      rw [SimpleGraph.reachable_iff_reflTransGen]
                      exact hxy
                    exact (TwoPointDiagram.reassembleExternalVacuum_reachable_preserves_externalPart
                      hE external vacuum hreach).mpr hyExt
                  rcases y with ey | yint
                  · exact False.elim (hySide trivial)
                  · exact ⟨⟨yint.1, Finset.mem_sdiff.mpr ⟨yint.2, hySide⟩⟩, rfl⟩))) :=
            Classical.choose_spec (show ∃ yv : ↥(S \ E),
                y = TwoPointDiagram.vacuumVertexEmbed hE yv from by
              have hySide : ¬ TwoPointDiagram.VertexInExternalPart (E := E) y := by
                intro hyExt
                have hxVac := TwoPointDiagram.not_vertexInExternalPart_vacuumEmbed hE v
                apply hxVac
                have hreach :
                    (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Reachable
                      (TwoPointDiagram.vacuumVertexEmbed hE v) y := by
                  rw [SimpleGraph.reachable_iff_reflTransGen]
                  exact hxy
                exact (TwoPointDiagram.reassembleExternalVacuum_reachable_preserves_externalPart
                  hE external vacuum hreach).mpr hyExt
              rcases y with ey | yint
              · exact False.elim (hySide trivial)
              · exact ⟨⟨yint.1, Finset.mem_sdiff.mpr ⟨yint.2, hySide⟩⟩, rfl⟩)
          let yVac : ↥(S \ E) := Classical.choose (show ∃ yv : ↥(S \ E),
                y = TwoPointDiagram.vacuumVertexEmbed hE yv from by
            have hySide : ¬ TwoPointDiagram.VertexInExternalPart (E := E) y := by
              intro hyExt
              have hxVac := TwoPointDiagram.not_vertexInExternalPart_vacuumEmbed hE v
              apply hxVac
              have hreach :
                  (TwoPointDiagram.reassembleExternalVacuum hE external vacuum).vertexGraph.Reachable
                    (TwoPointDiagram.vacuumVertexEmbed hE v) y := by
                rw [SimpleGraph.reachable_iff_reflTransGen]
                exact hxy
              exact (TwoPointDiagram.reassembleExternalVacuum_reachable_preserves_externalPart
                hE external vacuum hreach).mpr hyExt
            rcases y with ey | yint
            · exact False.elim (hySide trivial)
            · exact ⟨⟨yint.1, Finset.mem_sdiff.mpr ⟨yint.2, hySide⟩⟩, rfl⟩)
          have hedge : vacuum.vertexGraph.Adj yVac zVac := by
            apply (TwoPointDiagram.reassembleExternalVacuum_vacuum_adj_iff
              hE external vacuum yVac zVac).mp
            simpa [yVac, zVac, hyVac] using hyz
          exact Relation.ReflTransGen.tail ih hedge
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hxy hyz ih =>
        exact Relation.ReflTransGen.tail ih
          ((TwoPointDiagram.reassembleExternalVacuum_vacuum_adj_iff
            hE external vacuum _ _).2 hyz)

end Common
end SecondQuantization
