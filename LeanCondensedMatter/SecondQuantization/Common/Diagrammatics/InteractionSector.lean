import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Sum

set_option linter.style.header false

/-!
# Interaction sectors of external-plus-interaction vertex sets

A diagram component is represented as a finite subset of a sum whose right summand is the subtype of
ambient interaction vertices. This module extracts those interaction vertices back into the ambient
finite vertex type.

The sum-side filtering itself is provided by Mathlib's `Finset.toRight`; this module owns only the
diagrammatic interpretation and the ambient-`Finset` reindexing used by common diagram families.
-/

namespace SecondQuantization
namespace Common

variable {External Vertex : Type*}

/-- Ambient interaction vertices represented in the right summand of `B`. -/
noncomputable def interactionSector {S : Finset Vertex}
    (B : Finset (External ⊕ ↥S)) : Finset Vertex :=
  B.toRight.map (Function.Embedding.subtype (fun v => v ∈ S))

/-- Membership in the interaction sector is membership of the corresponding right-summand vertex. -/
theorem mem_interactionSector {S : Finset Vertex}
    (B : Finset (External ⊕ ↥S)) (v : Vertex) :
    v ∈ interactionSector B ↔
      ∃ hv : v ∈ S, (Sum.inr ⟨v, hv⟩ : External ⊕ ↥S) ∈ B := by
  classical
  constructor
  · intro hv
    rcases Finset.mem_map.1 hv with ⟨w, hw, rfl⟩
    exact ⟨w.2, Finset.mem_toRight.1 hw⟩
  · rintro ⟨hv, hB⟩
    exact Finset.mem_map.2
      ⟨⟨v, hv⟩, Finset.mem_toRight.2 hB, rfl⟩

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

end Common
end SecondQuantization
