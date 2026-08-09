import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.OrderedConnectivity

set_option linter.style.header false

/-!
# Two-point components under interaction-vertex ordering

Interaction-vertex ordering is a graph isomorphism, so it transports the connected-component
partition canonically. This is the structural bridge used when the external-leg LCT reindexes a
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

/-- Interaction vertices of a component of the explicit ordered diagram are canonically the
interaction vertices of the corresponding ambient component. -/
def TwoPointDiagram.inInteractionOrderComponentInteractionEquiv
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S)
    (B : (d.inInteractionOrder order).componentPartition.parts) :
    ↥(TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin S.card))))) ≃
    ↥(TwoPointDiagram.interactionPart
      ((d.inInteractionOrderComponentPartEquiv order B : d.componentPartition.parts) :
        Finset (TwoPointVertex S))) where
  toFun v := by
    let vExplicit : ↥(Finset.univ : Finset (Fin S.card)) := ⟨v.1, Finset.mem_univ _⟩
    let vAmbient : ↥S := order v.1
    refine ⟨vAmbient.1, ?_⟩
    apply (TwoPointDiagram.mem_interactionPart_subtype
      ((d.inInteractionOrderComponentPartEquiv order B : d.componentPartition.parts) :
        Finset (TwoPointVertex S)) vAmbient).2
    change (Sum.inr vAmbient : TwoPointVertex S) ∈
      B.1.image (twoPointInteractionOrderVertexEquiv order)
    apply Finset.mem_image.mpr
    refine ⟨Sum.inr vExplicit, ?_, ?_⟩
    · exact (TwoPointDiagram.mem_interactionPart_subtype
        (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin S.card)))) vExplicit).1 v.2
    · rfl
  invFun v := by
    let vAmbient : ↥S :=
      ⟨v.1, TwoPointDiagram.interactionPart_subset
        ((d.inInteractionOrderComponentPartEquiv order B : d.componentPartition.parts) :
          Finset (TwoPointVertex S)) v.2⟩
    let vExplicit : ↥(Finset.univ : Finset (Fin S.card)) :=
      ⟨(order.symm vAmbient), Finset.mem_univ _⟩
    refine ⟨vExplicit.1, ?_⟩
    apply (TwoPointDiagram.mem_interactionPart_subtype
      (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin S.card)))) vExplicit).2
    have hvAmbient : (Sum.inr vAmbient : TwoPointVertex S) ∈
        ((d.inInteractionOrderComponentPartEquiv order B : d.componentPartition.parts) :
          Finset (TwoPointVertex S)) :=
      (TwoPointDiagram.mem_interactionPart_subtype
        ((d.inInteractionOrderComponentPartEquiv order B : d.componentPartition.parts) :
          Finset (TwoPointVertex S)) vAmbient).1 v.2
    change (Sum.inr vExplicit : TwoPointVertex (Finset.univ : Finset (Fin S.card))) ∈ B.1
    change (Sum.inr vAmbient : TwoPointVertex S) ∈
      B.1.image (twoPointInteractionOrderVertexEquiv order) at hvAmbient
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hvAmbient
    have hx' : x = Sum.inr vExplicit := by
      apply (twoPointInteractionOrderVertexEquiv order).injective
      rw [hxeq]
      rfl
    simpa [hx'] using hx
  left_inv v := by
    apply Subtype.ext
    simp [TwoPointDiagram.inInteractionOrderComponentInteractionEquiv]
  right_inv v := by
    apply Subtype.ext
    simp [TwoPointDiagram.inInteractionOrderComponentInteractionEquiv]

@[simp]
theorem TwoPointDiagram.inInteractionOrderComponentInteractionEquiv_val
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S)
    (B : (d.inInteractionOrder order).componentPartition.parts)
    (v : ↥(TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin S.card)))))) :
    (d.inInteractionOrderComponentInteractionEquiv order B v : Fin N) =
      (order v.1 : Fin N) :=
  rfl

/-- Corresponding components before and after interaction ordering contain the same number of
interaction vertices. -/
theorem TwoPointDiagram.interactionComponentSize_inInteractionOrder_eq
    {S : Finset (Fin N)} (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (order : QuarticVertexOrder S)
    (B : (d.inInteractionOrder order).componentPartition.parts) :
    (TwoPointDiagram.interactionPart
      (B : Finset (TwoPointVertex (Finset.univ : Finset (Fin S.card))))).card =
      (TwoPointDiagram.interactionPart
        ((d.inInteractionOrderComponentPartEquiv order B : d.componentPartition.parts) :
          Finset (TwoPointVertex S))).card := by
  exact Fintype.card_congr (d.inInteractionOrderComponentInteractionEquiv order B)

end

end Common
end SecondQuantization
