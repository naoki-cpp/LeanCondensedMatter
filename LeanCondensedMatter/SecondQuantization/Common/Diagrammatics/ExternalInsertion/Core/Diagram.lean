import LeanCondensedMatter.Combinatorics.PerfectPairing.VertexGraph
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Diagrams with finitely many external insertions

This module owns the statistics-independent diagram syntax for an even external sector with quartic
interaction vertices.  The parameter `E` represents `2 * E` one-legged external insertions, so the
total number of legs is automatically even and the existing ordered `Pairing` API applies without
an additional parity witness.

At `E = 1`, this core has two external insertions and therefore the same external/interaction
shape as the established two-point diagram data; the two representations remain independent.
Odd external sectors are not represented by this paired-diagram type; a fermionic application that
needs them should prove the corresponding vanishing statement separately rather than weakening the
pairing invariant.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {E N : ℕ}

/-- Vertices with `2 * E` distinguished external insertions and quartic interaction vertices. -/
abbrev ExternalInsertionVertex (E : ℕ) (S : Finset (Fin N)) : Type :=
  Fin (2 * E) ⊕ ↥S

/-- One leg for each external insertion and four legs for each quartic interaction vertex. -/
abbrev ExternalInsertionLeg (E : ℕ) (S : Finset (Fin N)) : Type :=
  Fin (2 * E) ⊕ (↥S × Fin 4)

/-- Flatten all external and quartic interaction legs into the ordered finite type used by
`Pairing`. -/
noncomputable def externalInsertionLegEquiv (E : ℕ) (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card + E)) ≃ ExternalInsertionLeg E S :=
  Fintype.equivOfCardEq (by
    simp [ExternalInsertionLeg]
    omega)

/-- The flattened leg belonging to external insertion `e`. -/
noncomputable def externalInsertionExternalLeg (E : ℕ) (S : Finset (Fin N))
    (e : Fin (2 * E)) : Fin (2 * (2 * S.card + E)) :=
  (externalInsertionLegEquiv E S).symm (Sum.inl e)

/-- The flattened local leg `l` belonging to interaction vertex `v`. -/
noncomputable def externalInsertionInteractionLeg {E : ℕ} {S : Finset (Fin N)}
    (v : ↥S) (l : Fin 4) : Fin (2 * (2 * S.card + E)) :=
  (externalInsertionLegEquiv E S).symm (Sum.inr (v, l))

/-- The vertex incident to a flattened external-insertion diagram leg. -/
noncomputable def externalInsertionVertexOfLeg {E : ℕ} {S : Finset (Fin N)}
    (leg : Fin (2 * (2 * S.card + E))) : ExternalInsertionVertex E S :=
  match externalInsertionLegEquiv E S leg with
  | Sum.inl e => Sum.inl e
  | Sum.inr p => Sum.inr p.1

@[simp]
theorem externalInsertionVertexOfLeg_externalLeg (E : ℕ) (S : Finset (Fin N))
    (e : Fin (2 * E)) :
    externalInsertionVertexOfLeg (externalInsertionExternalLeg E S e) =
      (Sum.inl e : ExternalInsertionVertex E S) := by
  simp [externalInsertionVertexOfLeg, externalInsertionExternalLeg]

@[simp]
theorem externalInsertionVertexOfLeg_interactionLeg {E : ℕ} {S : Finset (Fin N)}
    (v : ↥S) (l : Fin 4) :
    externalInsertionVertexOfLeg (externalInsertionInteractionLeg (E := E) v l) =
      (Sum.inr v : ExternalInsertionVertex E S) := by
  simp [externalInsertionVertexOfLeg, externalInsertionInteractionLeg]

/-- A diagram with `2 * E` labelled one-legged external insertions, labelled quartic interaction
vertices, and a perfect pairing of all `2 * E + 4 |S|` legs. -/
structure ExternalInsertionDiagram (ExternalLabel InternalLabel : Type*) (E N : ℕ)
    (S : Finset (Fin N)) where
  /-- Labels attached to the distinguished external insertions. -/
  externalLabel : Fin (2 * E) → ExternalLabel
  /-- Labels attached to quartic interaction vertices. -/
  vertexLabel : ↥S → InternalLabel
  /-- Perfect pairing of all external and interaction legs. -/
  pairing : Pairing (2 * S.card + E)

@[ext]
theorem ExternalInsertionDiagram.ext {S : Finset (Fin N)}
    {d₁ d₂ : ExternalInsertionDiagram ExternalLabel InternalLabel E N S}
    (he : d₁.externalLabel = d₂.externalLabel)
    (hv : d₁.vertexLabel = d₂.vertexLabel) (hp : d₁.pairing = d₂.pairing) : d₁ = d₂ := by
  cases d₁
  cases d₂
  cases he
  cases hv
  cases hp
  rfl

/-- An external-insertion diagram as its two label functions and pairing. -/
private def ExternalInsertionDiagram.equivData {S : Finset (Fin N)} :
    ExternalInsertionDiagram ExternalLabel InternalLabel E N S ≃
      (Fin (2 * E) → ExternalLabel) ×
        (↥S → InternalLabel) × Pairing (2 * S.card + E) where
  toFun d := (d.externalLabel, d.vertexLabel, d.pairing)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance ExternalInsertionDiagram.instDecidableEq [DecidableEq ExternalLabel]
    [DecidableEq InternalLabel] {S : Finset (Fin N)} :
    DecidableEq (ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :=
  ExternalInsertionDiagram.equivData.decidableEq

noncomputable instance ExternalInsertionDiagram.instFintype [Fintype ExternalLabel]
    [Fintype InternalLabel] {S : Finset (Fin N)} :
    Fintype (ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :=
  Fintype.ofEquiv _ ExternalInsertionDiagram.equivData.symm

/-- The graph joining distinct external or interaction vertices whose legs are paired. -/
noncomputable def ExternalInsertionDiagram.vertexGraph {S : Finset (Fin N)}
    (d : ExternalInsertionDiagram ExternalLabel InternalLabel E N S) :
    SimpleGraph (ExternalInsertionVertex E S) :=
  d.pairing.vertexGraph (externalInsertionVertexOfLeg (E := E))

end Common
end SecondQuantization
