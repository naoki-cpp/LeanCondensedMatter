import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedConnectivity

set_option linter.style.header false

/-!
# Two-point components under interaction-vertex ordering

Interaction-vertex ordering is a graph isomorphism, so it transports the connected-component
partition canonically.  This is the structural bridge used when the external-leg LCT reindexes a
global interaction order by component-local orders and one component shuffle.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

noncomputable section

/-- A component block of the explicit ordered diagram maps to the corresponding ambient component
block. -/
theorem TwoPointDiagram.image_componentBlock_inInteractionOrder
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S)
    (v : TwoPointVertex (Finset.univ : Finset (Fin S.card))) :
    ((d.inInteractionOrder order).componentBlock v).image
        (twoPointInteractionOrderVertexEquiv order) =
      d.componentBlock (twoPointInteractionOrderVertexEquiv order v) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx, hxw⟩ := Finset.mem_image.mp hw
    subst w
    apply (d.mem_componentBlock
      (twoPointInteractionOrderVertexEquiv order v)
      (twoPointInteractionOrderVertexEquiv order x)).2
    exact (d.inInteractionOrder_vertexGraph_reachable_iff order x v).1
      (((d.inInteractionOrder order).mem_componentBlock v x).1 hx)
  · intro hw
    let x := (twoPointInteractionOrderVertexEquiv order).symm w
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, by simp [x]⟩
    apply ((d.inInteractionOrder order).mem_componentBlock v x).2
    apply (d.inInteractionOrder_vertexGraph_reachable_iff order x v).2
    simpa [x] using
      ((d.mem_componentBlock
        (twoPointInteractionOrderVertexEquiv order v) w).1 hw)

/-- Pulling an ambient component block back through the ordering vertex equivalence gives the
corresponding component block of the explicit ordered diagram. -/
theorem TwoPointDiagram.image_componentBlock_inInteractionOrder_symm
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) (v : TwoPointVertex S) :
    (d.componentBlock v).image (twoPointInteractionOrderVertexEquiv order).symm =
      (d.inInteractionOrder order).componentBlock
        ((twoPointInteractionOrderVertexEquiv order).symm v) := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨x, hx, hxw⟩ := Finset.mem_image.mp hw
    subst w
    apply ((d.inInteractionOrder order).mem_componentBlock
      ((twoPointInteractionOrderVertexEquiv order).symm v)
      ((twoPointInteractionOrderVertexEquiv order).symm x)).2
    apply (d.inInteractionOrder_vertexGraph_reachable_iff order
      ((twoPointInteractionOrderVertexEquiv order).symm x)
      ((twoPointInteractionOrderVertexEquiv order).symm v)).2
    simpa using ((d.mem_componentBlock v x).1 hx)
  · intro hw
    let x := twoPointInteractionOrderVertexEquiv order w
    apply Finset.mem_image.mpr
    refine ⟨x, ?_, by simp [x]⟩
    apply (d.mem_componentBlock v x).2
    have hreach :=
      ((d.inInteractionOrder order).mem_componentBlock
        ((twoPointInteractionOrderVertexEquiv order).symm v) w).1 hw
    have hambient :=
      (d.inInteractionOrder_vertexGraph_reachable_iff order w
        ((twoPointInteractionOrderVertexEquiv order).symm v)).1 hreach
    simpa [x] using hambient

/-- Connected components of a diagram and of any explicit interaction ordering of it are canonically
equivalent. -/
def TwoPointDiagram.inInteractionOrderComponentPartEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S) :
    (d.inInteractionOrder order).componentPartition.parts ≃ d.componentPartition.parts where
  toFun B := by
    refine ⟨B.1.image (twoPointInteractionOrderVertexEquiv order), ?_⟩
    obtain ⟨v, hv⟩ :=
      (d.inInteractionOrder order).componentPartition.nonempty_of_mem_parts B.2
    have hB : (d.inInteractionOrder order).componentBlock v = B.1 :=
      ((d.inInteractionOrder order).componentBlock_eq_iff_mem B.2 v).2 hv
    rw [← hB, d.image_componentBlock_inInteractionOrder order v]
    exact d.componentBlock_mem_componentPartition
      (twoPointInteractionOrderVertexEquiv order v)
  invFun B := by
    refine ⟨B.1.image (twoPointInteractionOrderVertexEquiv order).symm, ?_⟩
    obtain ⟨v, hv⟩ := d.componentPartition.nonempty_of_mem_parts B.2
    have hB : d.componentBlock v = B.1 :=
      (d.componentBlock_eq_iff_mem B.2 v).2 hv
    rw [← hB, d.image_componentBlock_inInteractionOrder_symm order v]
    exact (d.inInteractionOrder order).componentBlock_mem_componentPartition
      ((twoPointInteractionOrderVertexEquiv order).symm v)
  left_inv B := by
    apply Subtype.ext
    simp [Finset.image_image, Function.comp_def]
  right_inv B := by
    apply Subtype.ext
    simp [Finset.image_image, Function.comp_def]

end

end Common
end SecondQuantization
