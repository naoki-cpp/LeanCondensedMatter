import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Amplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Reindexing
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel
import LeanCondensedMatter.Combinatorics.PerfectPairing.VertexGraphRelabel

set_option linter.style.header false

/-!
# Interaction-vertex relabeling for fixed-external two-point diagrams

This is the structural owner for interaction-slot relabeling. A permutation of the interaction slots
relabels standard two-point legs, the stored perfect pairing, and quartic vertex labels while fixing
the two external legs. Relabeling is packaged as an equivalence of the finite fixed-diagram type, so
full diagram sums can be reindexed without orbit/stabilizer bookkeeping. The quartic coupling
product is invariant under the same relabeling.

The convention is that `π` maps a new interaction slot to the old interaction slot whose data it
inherits. Thus the relabeled vertex sequence satisfies `q_new v = q_old (π v)`.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

noncomputable section

/-- Relabel the standard two-point leg type by an interaction-slot permutation, leaving the two
external legs fixed. The permutation maps new leg identities to old leg identities. -/
def interactionVertexLegRelabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    OrderedTwoPointLeg n ≃ OrderedTwoPointLeg n where
  toFun
    | Sum.inl e => Sum.inl e
    | Sum.inr p => Sum.inr (⟨π p.1.1, Finset.mem_univ _⟩, p.2)
  invFun
    | Sum.inl e => Sum.inl e
    | Sum.inr p => Sum.inr (⟨π.symm p.1.1, Finset.mem_univ _⟩, p.2)
  left_inv x := by
    rcases x with e | ⟨v, l⟩
    · rfl
    · simp
  right_inv x := by
    rcases x with e | ⟨v, l⟩
    · rfl
    · simp

@[simp]
theorem interactionVertexLegRelabel_external {n : ℕ} (π : Equiv.Perm (Fin n)) (e : Fin 2) :
    interactionVertexLegRelabel π (Sum.inl e) = (Sum.inl e : OrderedTwoPointLeg n) :=
  rfl

@[simp]
theorem interactionVertexLegRelabel_interaction {n : ℕ} (π : Equiv.Perm (Fin n))
    (v : Fin n) (l : Fin 4) :
    interactionVertexLegRelabel π
        (Sum.inr (⟨v, Finset.mem_univ v⟩, l)) =
      (Sum.inr (⟨π v, Finset.mem_univ (π v)⟩, l) : OrderedTwoPointLeg n) :=
  rfl

/-- The flattened standard-leg permutation induced by an interaction-slot permutation. -/
def interactionVertexPositionRelabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) :=
  (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).trans
    ((interactionVertexLegRelabel π).trans
      (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm)

/-- Relabel full two-point vertices by the same interaction-slot permutation, fixing the external
vertices. -/
def interactionVertexVertexRelabel {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Common.TwoPointVertex (Finset.univ : Finset (Fin n)) ≃
      Common.TwoPointVertex (Finset.univ : Finset (Fin n)) :=
  Equiv.sumCongr (Equiv.refl (Fin 2))
    { toFun := fun v => ⟨π v.1, Finset.mem_univ _⟩
      invFun := fun v => ⟨π.symm v.1, Finset.mem_univ _⟩
      left_inv := by intro v; apply Subtype.ext; simp
      right_inv := by intro v; apply Subtype.ext; simp }

@[simp]
theorem interactionVertexVertexRelabel_external {n : ℕ} (π : Equiv.Perm (Fin n))
    (e : Fin 2) :
    interactionVertexVertexRelabel π
        (Sum.inl e : Common.TwoPointVertex (Finset.univ : Finset (Fin n))) = Sum.inl e :=
  rfl

@[simp]
theorem interactionVertexVertexRelabel_interaction {n : ℕ} (π : Equiv.Perm (Fin n))
    (v : ↥(Finset.univ : Finset (Fin n))) :
    interactionVertexVertexRelabel π (Sum.inr v) =
      (Sum.inr ⟨π v.1, Finset.mem_univ _⟩ :
        Common.TwoPointVertex (Finset.univ : Finset (Fin n))) :=
  rfl

/-- The leg relabeling commutes with the leg-to-vertex incidence map. -/
theorem twoPointVertexOfLeg_interactionVertexPositionRelabel {n : ℕ}
    (π : Equiv.Perm (Fin n))
    (leg : Fin (2 * (2 * (Finset.univ : Finset (Fin n)).card + 1))) :
    Common.twoPointVertexOfLeg (interactionVertexPositionRelabel π leg) =
      interactionVertexVertexRelabel π (Common.twoPointVertexOfLeg leg) := by
  change Common.twoPointVertexOfLeg
      ((Common.twoPointLegEquiv (Finset.univ : Finset (Fin n))).symm
        (interactionVertexLegRelabel π
          (Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)) leg))) = _
  rcases hleg : Common.twoPointLegEquiv (Finset.univ : Finset (Fin n)) leg with e | ⟨v, l⟩
  · rw [hleg]
    simp [Common.twoPointVertexOfLeg]
  · rw [hleg]
    simp [Common.twoPointVertexOfLeg]

/-- Relabel the interaction vertices of a fixed-external two-point Wick diagram. -/
def FixedExternalTwoPointWickDiagram.relabelInteractionVertices
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) : FixedExternalTwoPointWickDiagram Mode n i j :=
  ⟨{
    externalLabel := d.1.externalLabel
    vertexLabel := fun v => d.1.vertexLabel ⟨π v.1, Finset.mem_univ _⟩
    pairing := d.1.pairing.relabel (interactionVertexPositionRelabel π)
  }, d.2⟩

@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_externalLabel
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).1.externalLabel = d.1.externalLabel :=
  rfl

@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_vertexLabelSequence
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) (v : Fin n) :
    (d.relabelInteractionVertices π).vertexLabelSequence v = d.vertexLabelSequence (π v) :=
  rfl

@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_pairing
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).1.pairing =
      d.1.pairing.relabel (interactionVertexPositionRelabel π) :=
  rfl

/-- Reachability in the full vertex graph is transported by interaction relabeling. -/
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_reachable_iff
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n))
    (v w : Common.TwoPointVertex (Finset.univ : Finset (Fin n))) :
    (d.relabelInteractionVertices π).1.vertexGraph.Reachable v w ↔
      d.1.vertexGraph.Reachable
        (interactionVertexVertexRelabel π v)
        (interactionVertexVertexRelabel π w) := by
  exact d.1.pairing.vertexGraph_relabel_reachable_iff
    (interactionVertexPositionRelabel π) (interactionVertexVertexRelabel π)
    Common.twoPointVertexOfLeg Common.twoPointVertexOfLeg
    (twoPointVertexOfLeg_interactionVertexPositionRelabel π) v w

/-- External connectedness is invariant under interaction-slot relabeling. -/
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_isExternallyConnected_iff
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).1.IsExternallyConnected ↔ d.1.IsExternallyConnected := by
  constructor
  · rintro ⟨hNoVac, hExt⟩
    constructor
    · intro v
      obtain ⟨e, he⟩ := hNoVac ⟨π.symm v.1, Finset.mem_univ _⟩
      refine ⟨e, ?_⟩
      have h := ((d.relabelInteractionVertices_reachable_iff π
        (Sum.inl e) (Sum.inr ⟨π.symm v.1, Finset.mem_univ _⟩)).1 he)
      simpa [interactionVertexVertexRelabel] using h
    · change (d.relabelInteractionVertices π).1.vertexGraph.Reachable
        (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) at hExt
      change d.1.vertexGraph.Reachable
        (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))
      have h := ((d.relabelInteractionVertices_reachable_iff π
        (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))).1 hExt)
      simpa using h
  · rintro ⟨hNoVac, hExt⟩
    constructor
    · intro v
      obtain ⟨e, he⟩ := hNoVac ⟨π v.1, Finset.mem_univ _⟩
      refine ⟨e, ?_⟩
      apply (d.relabelInteractionVertices_reachable_iff π (Sum.inl e) (Sum.inr v)).2
      simpa [interactionVertexVertexRelabel] using he
    · change (d.relabelInteractionVertices π).1.vertexGraph.Reachable
        (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))
      change d.1.vertexGraph.Reachable
        (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2)) at hExt
      apply (d.relabelInteractionVertices_reachable_iff π
        (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))).2
      simpa using hExt

/-- Relabeling standard two-point legs by the inverse slot permutation is the inverse leg
relabeling. -/
@[simp]
theorem interactionVertexLegRelabel_symm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    interactionVertexLegRelabel π.symm = (interactionVertexLegRelabel π).symm := by
  ext leg
  rcases leg with e | ⟨v, l⟩
  · rfl
  · rfl

/-- The flattened position relabeling induced by the inverse slot permutation is the inverse
flattened position relabeling. -/
@[simp]
theorem interactionVertexPositionRelabel_symm {n : ℕ} (π : Equiv.Perm (Fin n)) :
    interactionVertexPositionRelabel π.symm =
      (interactionVertexPositionRelabel π).symm := by
  unfold interactionVertexPositionRelabel
  rw [interactionVertexLegRelabel_symm]
  rfl

/-- Relabeling by `π` and then by `π⁻¹` recovers the original fixed-external diagram. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_symm
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π).relabelInteractionVertices π.symm = d := by
  apply Subtype.ext
  apply Common.TwoPointDiagram.ext
  · rfl
  · funext v
    change d.1.vertexLabel ⟨π (π.symm v.1), Finset.mem_univ _⟩ = d.1.vertexLabel v
    congr 1
    apply Subtype.ext
    simp
  · change (d.1.pairing.relabel (interactionVertexPositionRelabel π)).relabel
      (interactionVertexPositionRelabel π.symm) = d.1.pairing
    rw [interactionVertexPositionRelabel_symm]
    exact Pairing.relabel_symm_relabel d.1.pairing (interactionVertexPositionRelabel π)

/-- Relabeling by `π⁻¹` and then by `π` also recovers the original fixed-external diagram. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_symm_relabel
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (π : Equiv.Perm (Fin n)) :
    (d.relabelInteractionVertices π.symm).relabelInteractionVertices π = d := by
  simpa using d.relabelInteractionVertices_symm π.symm

/-- Interaction-vertex relabeling as an automorphism of the finite type of fixed-external diagrams. -/
noncomputable def fixedExternalTwoPointWickDiagramRelabelEquiv
    {n : ℕ} (i j : Mode) (π : Equiv.Perm (Fin n)) :
    FixedExternalTwoPointWickDiagram Mode n i j ≃
      FixedExternalTwoPointWickDiagram Mode n i j where
  toFun d := d.relabelInteractionVertices π
  invFun d := d.relabelInteractionVertices π.symm
  left_inv d := d.relabelInteractionVertices_symm π
  right_inv d := d.relabelInteractionVertices_symm_relabel π

/-- A finite sum over all fixed-external diagrams is invariant under interaction-vertex relabeling. -/
theorem sum_relabelInteractionVertices
    [Fintype Mode] {n : ℕ} (i j : Mode) (π : Equiv.Perm (Fin n))
    (F : FixedExternalTwoPointWickDiagram Mode n i j → ℂ) :
    ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
        F (d.relabelInteractionVertices π) =
      ∑ d : FixedExternalTwoPointWickDiagram Mode n i j, F d :=
  Equiv.sum_comp (fixedExternalTwoPointWickDiagramRelabelEquiv i j π) F

/-- The product of quartic vertex weights is invariant under a permutation of interaction slots. -/
theorem orderedTwoPointVertexWeight_comp_perm
    {n : ℕ} (g : QuarticVertexLabel Mode → ℂ)
    (q : Fin n → QuarticVertexLabel Mode) (π : Equiv.Perm (Fin n)) :
    orderedTwoPointVertexWeight g (fun v => q (π v)) =
      orderedTwoPointVertexWeight g q := by
  unfold orderedTwoPointVertexWeight
  exact Equiv.prod_comp π (fun v => g (q v))

/-- Relabeling interaction vertices does not change the product of quartic coupling weights. -/
theorem FixedExternalTwoPointWickDiagram.relabelInteractionVertices_vertexWeight
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (g : QuarticVertexLabel Mode → ℂ) (π : Equiv.Perm (Fin n)) :
    orderedTwoPointVertexWeight g
        (d.relabelInteractionVertices π).vertexLabelSequence =
      orderedTwoPointVertexWeight g d.vertexLabelSequence := by
  rw [show (d.relabelInteractionVertices π).vertexLabelSequence =
      fun v => d.vertexLabelSequence (π v) by
    funext v
    exact d.relabelInteractionVertices_vertexLabelSequence π v]
  exact orderedTwoPointVertexWeight_comp_perm g d.vertexLabelSequence π

end

end Fermionic
end SecondQuantization
