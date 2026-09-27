import LeanCondensedMatter.Combinatorics.FinpartitionProduct
import LeanCondensedMatter.Combinatorics.SimpleGraphComponentPartition
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum

set_option linter.style.header false

/-!
# Interaction sectors of external-plus-interaction vertex sets

A diagram component is represented as a finite subset of a sum whose right summand is the subtype of
ambient interaction vertices. This module extracts those interaction vertices back into the ambient
finite vertex type.

This module owns the diagrammatic interpretation while keeping the filtered ambient-vertex normal
form used by the existing component APIs.
-/

namespace SecondQuantization
namespace Common

variable {External Vertex : Type*}

open Classical in
/-- Ambient interaction vertices represented in the right summand of `B`. -/
noncomputable def interactionSector {S : Finset Vertex}
    (B : Finset (External ⊕ ↥S)) : Finset Vertex :=
  S.filter fun v =>
    ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : External ⊕ ↥S) ∈ B

/-- Membership in the interaction sector is membership of the corresponding right-summand vertex. -/
theorem mem_interactionSector {S : Finset Vertex}
    (B : Finset (External ⊕ ↥S)) (v : Vertex) :
    v ∈ interactionSector B ↔
      ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : External ⊕ ↥S) ∈ B := by
  classical
  unfold interactionSector
  rw [Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.choose, h⟩

/-- Membership form for a vertex already carrying its ambient-membership proof. -/
@[simp]
theorem mem_interactionSector_subtype {S : Finset Vertex}
    (B : Finset (External ⊕ ↥S)) (v : ↥S) :
    (v : Vertex) ∈ interactionSector B ↔
      (Sum.inr v : External ⊕ ↥S) ∈ B := by
  rw [mem_interactionSector]
  constructor
  · rintro ⟨hv, h⟩
    have hvEq : (⟨(v : Vertex), hv⟩ : ↥S) = v := Subtype.ext (by rfl)
    simpa only [hvEq] using h
  · intro h
    refine ⟨v.2, ?_⟩
    have hvEq : (⟨(v : Vertex), v.2⟩ : ↥S) = v := Subtype.ext (by rfl)
    simpa only [hvEq] using h

/-- The interaction sector is contained in the ambient interaction-vertex set. -/
theorem interactionSector_subset {S : Finset Vertex}
    (B : Finset (External ⊕ ↥S)) :
    interactionSector B ⊆ S := by
  intro v hv
  exact (mem_interactionSector B v).1 hv |>.choose


/-- The ambient interaction vertices are the dependent disjoint union of the interaction sectors of
the connected components of an external-plus-interaction graph. -/
noncomputable def interactionSectorComponentEquiv
    [DecidableEq External] [Fintype External] [DecidableEq Vertex]
    {S : Finset Vertex} (G : SimpleGraph (External ⊕ ↥S)) :
    ↥S ≃ Σ B : G.componentPartition.parts,
      ↥(interactionSector (B : Finset (External ⊕ ↥S))) :=
  G.componentPartition.equivSigmaSubfinsets S
    (fun v => (Sum.inr v : External ⊕ ↥S))
    (fun _ => Finset.mem_univ _)
    (fun B => interactionSector (B : Finset (External ⊕ ↥S)))
    (fun B => interactionSector_subset (B : Finset (External ⊕ ↥S)))
    (fun B v => mem_interactionSector_subtype
      (B : Finset (External ⊕ ↥S)) v)

/-- The inverse component decomposition preserves the underlying ambient interaction vertex. -/
@[simp]
theorem interactionSectorComponentEquiv_symm_val
    [DecidableEq External] [Fintype External] [DecidableEq Vertex]
    {S : Finset Vertex} (G : SimpleGraph (External ⊕ ↥S))
    (x : Σ B : G.componentPartition.parts,
      ↥(interactionSector (B : Finset (External ⊕ ↥S)))) :
    ((interactionSectorComponentEquiv G).symm x : ↥S).1 = x.2.1 :=
  rfl


/-- The interaction sectors of all graph components exhaust the ambient interaction vertices. -/
theorem sum_interactionSector_card_eq
    [DecidableEq External] [Fintype External] [DecidableEq Vertex]
    {S : Finset Vertex} (G : SimpleGraph (External ⊕ ↥S)) :
    (∑ B : G.componentPartition.parts,
      (interactionSector (B : Finset (External ⊕ ↥S))).card) = S.card := by
  have hcard := Fintype.card_congr (interactionSectorComponentEquiv G)
  simpa [Fintype.card_sigma] using hcard.symm

/-- A commutative product over ambient interaction vertices factors over the interaction sectors of
the graph components. -/
theorem prod_eq_prod_interactionSectors
    {M : Type*} [CommMonoid M]
    [DecidableEq External] [Fintype External] [DecidableEq Vertex]
    {S : Finset Vertex} (G : SimpleGraph (External ⊕ ↥S)) (f : ↥S → M) :
    (∏ v : ↥S, f v) =
      ∏ B : G.componentPartition.parts,
        ∏ v : ↥(interactionSector (B : Finset (External ⊕ ↥S))),
          f ⟨v.1, interactionSector_subset
            (B : Finset (External ⊕ ↥S)) v.2⟩ := by
  classical
  let e := interactionSectorComponentEquiv G
  calc
    (∏ v : ↥S, f v) =
        ∏ B : G.componentPartition.parts,
          ∏ v : ↥(interactionSector (B : Finset (External ⊕ ↥S))),
            f (e.symm ⟨B, v⟩) :=
      Fintype.prod_equiv_sigma e f
    _ = ∏ B : G.componentPartition.parts,
        ∏ v : ↥(interactionSector (B : Finset (External ⊕ ↥S))),
          f ⟨v.1, interactionSector_subset
            (B : Finset (External ⊕ ↥S)) v.2⟩ := by
      apply Fintype.prod_congr
      intro B
      apply Fintype.prod_congr
      intro v
      apply congrArg f
      apply Subtype.ext
      exact interactionSectorComponentEquiv_symm_val G ⟨B, v⟩

/-- A fixed ambient interaction vertex belongs to the interaction sector of at most one graph
component. -/
theorem interactionSector_component_unique
    [DecidableEq External] [Fintype External] [DecidableEq Vertex]
    {S : Finset Vertex} (G : SimpleGraph (External ⊕ ↥S))
    (v : ↥S) (B C : G.componentPartition.parts)
    (hvB : (v : Vertex) ∈ interactionSector
      (B : Finset (External ⊕ ↥S)))
    (hvC : (v : Vertex) ∈ interactionSector
      (C : Finset (External ⊕ ↥S))) :
    B = C := by
  have h :
      (interactionSectorComponentEquiv G).symm ⟨B, ⟨v.1, hvB⟩⟩ =
        (interactionSectorComponentEquiv G).symm ⟨C, ⟨v.1, hvC⟩⟩ := by
    apply Subtype.ext
    simp
  exact congrArg Sigma.fst ((interactionSectorComponentEquiv G).symm.injective h)

end Common
end SecondQuantization
