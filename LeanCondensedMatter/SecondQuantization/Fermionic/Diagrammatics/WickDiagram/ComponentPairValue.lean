import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentOrderedSimplex
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.ComponentOrder
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.Amplitude

set_option linter.style.header false

/-!
# Component-local ordered legs and pair values

A component shuffle embeds every component-local ordered flattened leg into the flattened-leg
enumeration of the assembled global vertex order. This file proves that the associated fermionic leg
operators and normalized pair values agree exactly with those of the restricted component diagram.
These coordinate lemmas are the first part of the contraction-integrand factorization milestone.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} {N : ℕ}

/-- Embed a component-local ordered flattened leg into the assembled global ordered-leg
enumeration. -/
noncomputable def QuarticWickDiagram.componentOrderedLeg {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) → Fin (2 * (2 * S.card)) :=
  fun p => (Common.orderedQuarticLegEquiv S.card).symm
    (shuffle.slotEquiv ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩,
      (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2)

@[simp]
theorem QuarticWickDiagram.orderedQuarticLegEquiv_componentOrderedLeg
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (shuffle : d.ComponentShuffle) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    Common.orderedQuarticLegEquiv S.card (d.componentOrderedLeg shuffle B p) =
      (shuffle.slotEquiv ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩,
        (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2) := by
  simp [QuarticWickDiagram.componentOrderedLeg]

/-- Recover the flattened ordered-leg value from its vertex slot and local leg. -/
theorem orderedQuarticLegEquiv_reconstruct_val (n : ℕ) (p : Fin (2 * (2 * n))) :
    p.val = (Common.orderedQuarticLegEquiv n p).2.val + 4 * (Common.orderedQuarticLegEquiv n p).1.val := by
  have h := congrArg (fun q => q.val) ((Common.orderedQuarticLegEquiv n).symm_apply_apply p)
  simpa [Common.orderedQuarticLegEquiv, finProdFinEquiv] using h.symm

/-- Flattened quartic legs in distinct vertex-slot blocks are ordered exactly by their slots. -/
theorem orderedQuarticLegEquiv_symm_lt_symm_iff_fst_lt_of_ne
    (n : ℕ) (i j : Fin n) (a b : Fin 4) (hij : i ≠ j) :
    (Common.orderedQuarticLegEquiv n).symm (i, a) <
        (Common.orderedQuarticLegEquiv n).symm (j, b) ↔ i < j := by
  have hp := orderedQuarticLegEquiv_reconstruct_val n
    ((Common.orderedQuarticLegEquiv n).symm (i, a))
  have hq := orderedQuarticLegEquiv_reconstruct_val n
    ((Common.orderedQuarticLegEquiv n).symm (j, b))
  have hp' : ((Common.orderedQuarticLegEquiv n).symm (i, a)).val = a.val + 4 * i.val := by
    simpa using hp
  have hq' : ((Common.orderedQuarticLegEquiv n).symm (j, b)).val = b.val + 4 * j.val := by
    simpa using hq
  change ((Common.orderedQuarticLegEquiv n).symm (i, a)).val <
      ((Common.orderedQuarticLegEquiv n).symm (j, b)).val ↔ i.val < j.val
  rw [hp', hq']
  have ha : a.val < 4 := a.isLt
  have hb : b.val < 4 := b.isLt
  have hij' : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  omega

/-- Numeric form of the component ordered-leg embedding. -/
@[simp]
theorem QuarticWickDiagram.componentOrderedLeg_val {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    (d.componentOrderedLeg shuffle B p).val =
      (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).2.val +
        4 * (shuffle.slotEquiv
          ⟨B, (Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card p).1⟩).val := by
  simp [QuarticWickDiagram.componentOrderedLeg, Common.orderedQuarticLegEquiv, finProdFinEquiv]

/-- The component ordered-leg embedding preserves the flattened-leg order. -/
theorem QuarticWickDiagram.componentOrderedLeg_strictMono {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    StrictMono (d.componentOrderedLeg shuffle B) := by
  intro a b hab
  let pa := Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card a
  let pb := Common.orderedQuarticLegEquiv (B : Finset (Fin N)).card b
  have ha := orderedQuarticLegEquiv_reconstruct_val (B : Finset (Fin N)).card a
  have hb := orderedQuarticLegEquiv_reconstruct_val (B : Finset (Fin N)).card b
  change a.val = pa.2.val + 4 * pa.1.val at ha
  change b.val = pb.2.val + 4 * pb.1.val at hb
  change a.val < b.val at hab
  have hpa : pa.2.val < 4 := pa.2.isLt
  have hpb : pb.2.val < 4 := pb.2.isLt
  change (d.componentOrderedLeg shuffle B a).val <
    (d.componentOrderedLeg shuffle B b).val
  simp only [d.componentOrderedLeg_val]
  change pa.2.val + 4 * (shuffle.slotEquiv ⟨B, pa.1⟩).val <
    pb.2.val + 4 * (shuffle.slotEquiv ⟨B, pb.1⟩).val
  by_cases hslot : pa.1 < pb.1
  · have hg : (shuffle.slotEquiv ⟨B, pa.1⟩).val <
        (shuffle.slotEquiv ⟨B, pb.1⟩).val := shuffle.strictMono B hslot
    omega
  · have hpb_le : pb.1 ≤ pa.1 := le_of_not_gt hslot
    have hs : pa.1 = pb.1 := by
      by_contra hne
      have hrev : pb.1 < pa.1 := lt_of_le_of_ne hpb_le (Ne.symm hne)
      have hrev_val : pb.1.val < pa.1.val := hrev
      omega
    have hs_val : pa.1.val = pb.1.val := congrArg (fun q => q.val) hs
    have hlocal : pa.2.val < pb.2.val := by omega
    have hg_eq : shuffle.slotEquiv ⟨B, pa.1⟩ =
        shuffle.slotEquiv ⟨B, pb.1⟩ := by rw [hs]
    have hg_val := congrArg (fun q => q.val) hg_eq
    omega

/-- The canonical order embedding of one component's flattened legs into the assembled order. -/
noncomputable def QuarticWickDiagram.componentOrderedLegOrderEmbedding {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) ↪o Fin (2 * (2 * S.card)) :=
  OrderEmbedding.ofStrictMono (d.componentOrderedLeg shuffle B)
    (d.componentOrderedLeg_strictMono shuffle B)

@[simp]
theorem QuarticWickDiagram.componentOrderedLegOrderEmbedding_apply {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    d.componentOrderedLegOrderEmbedding shuffle B p = d.componentOrderedLeg shuffle B p :=
  rfl

/-- The component-local ordered-leg map is injective. -/
theorem QuarticWickDiagram.componentOrderedLeg_injective {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Function.Injective (d.componentOrderedLeg shuffle B) :=
  (d.componentOrderedLegOrderEmbedding shuffle B).injective

/-- The component-local ordered-leg map as an embedding. -/
noncomputable def QuarticWickDiagram.componentOrderedLegEmbedding {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) :
    Fin (2 * (2 * (B : Finset (Fin N)).card)) ↪ Fin (2 * (2 * S.card)) :=
  (d.componentOrderedLegOrderEmbedding shuffle B).toEmbedding

/-- The assembled global order sends a component slot to the same underlying labelled vertex as its
component-local order. -/
theorem QuarticWickDiagram.assembleVertexOrder_componentSlot_val
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) (i : Fin (B : Finset (Fin N)).card) :
    ((d.assembleVertexOrder orders shuffle (shuffle.slotEquiv ⟨B, i⟩) : ↥S) : Fin N) =
      ((orders B i : ↥(B : Finset (Fin N))) : Fin N) := by
  simp [QuarticWickDiagram.assembleVertexOrder, Common.QuarticDiagram.assembleVertexOrder,
    Common.QuarticDiagram.componentVertexEquiv, Finpartition.equivSigmaParts]

/-- Vertex labels agree between the assembled global diagram and a restricted component. -/
theorem QuarticWickDiagram.restrictComponent_vertexLabel_componentOrder
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (B : d.componentPartition.parts) (i : Fin (B : Finset (Fin N)).card) :
    (d.restrictComponent B.2).vertexLabel (orders B i) =
      d.vertexLabel (d.assembleVertexOrder orders shuffle (shuffle.slotEquiv ⟨B, i⟩)) := by
  unfold QuarticWickDiagram.restrictComponent Common.QuarticDiagram.restrictComponent
  apply congrArg d.vertexLabel
  apply Subtype.ext
  simpa using (d.assembleVertexOrder_componentSlot_val orders shuffle B i).symm

section Fermionic

variable [DecidableEq Mode] [LinearOrder Mode]

/-- A global ordered leg at a component-embedded position equals the corresponding ordered leg of
its restricted component diagram. -/
theorem orderedQuarticLegOperator_componentOrderedLeg
    (ε : Mode → ℝ) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (p : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticLegOperator ε d (d.assembleVertexOrder orders shuffle) τ
        (d.componentOrderedLeg shuffle B p) =
      orderedQuarticLegOperator ε (d.restrictComponent B.2) (orders B)
        (d.componentTimeAssignment shuffle τ B) p := by
  unfold orderedQuarticLegOperator quarticLegOperatorForSequence
  simp only [d.orderedQuarticLegEquiv_componentOrderedLeg,
    Common.QuarticDiagram.componentTimeAssignment_apply]
  rw [d.restrictComponent_vertexLabel_componentOrder orders shuffle B]

variable [Fintype Mode]

/-- Pair values agree after embedding both component-local ordered legs into the assembled global
ordered-leg enumeration. -/
theorem orderedQuarticPairValue_componentOrderedLeg (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S)
    (orders : d.ComponentVertexOrders) (shuffle : d.ComponentShuffle)
    (τ : Fin S.card → ℝ) (B : d.componentPartition.parts)
    (a b : Fin (2 * (2 * (B : Finset (Fin N)).card))) :
    orderedQuarticPairValue ε β d (d.assembleVertexOrder orders shuffle) τ
        (d.componentOrderedLeg shuffle B a) (d.componentOrderedLeg shuffle B b) =
      orderedQuarticPairValue ε β (d.restrictComponent B.2) (orders B)
        (d.componentTimeAssignment shuffle τ B) a b := by
  unfold orderedQuarticPairValue
  rw [orderedQuarticLegOperator_componentOrderedLeg,
    orderedQuarticLegOperator_componentOrderedLeg]

end Fermionic

end Fermionic
end SecondQuantization
