import LeanCondensedMatter.Combinatorics.PerfectPairing
import LeanCondensedMatter.Combinatorics.PerfectPairing.VertexGraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fintype.EquivFin

set_option linter.style.header false

/-!
# Two-point diagrams with external legs

This module adds the statistics-independent combinatorial data needed for a two-point correlation
function with quartic interaction vertices.  There are two distinguished one-legged external
vertices and four legs at every interaction vertex.

Two connectedness notions are deliberately separated:

* `HasNoVacuumComponent` says that every interaction vertex lies in a component meeting the
  external sector.  This is the condition produced by cancellation of vacuum bubbles in a
  normalized correlation function.
* `IsExternallyConnected` additionally requires the two external vertices to lie in the same
  component.  This is the connected two-point Green-function condition.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {ExternalLabel InternalLabel : Type*} {N : ℕ}

/-- The vertices of a two-point diagram: two external vertices and the interaction vertices. -/
abbrev TwoPointVertex (S : Finset (Fin N)) : Type := Fin 2 ⊕ ↥S

/-- The legs of a two-point diagram: one leg at each external vertex and four at each interaction
vertex. -/
abbrev TwoPointLeg (S : Finset (Fin N)) : Type := Fin 2 ⊕ (↥S × Fin 4)

/-- Flatten the two external legs and all quartic interaction legs into the ordered finite type used
by `Pairing`. -/
noncomputable def twoPointLegEquiv (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card + 1)) ≃ TwoPointLeg S :=
  Fintype.equivOfCardEq (by
    simp [TwoPointLeg]
    omega)

/-- The flattened leg belonging to external vertex `e`. -/
noncomputable def twoPointExternalLeg (S : Finset (Fin N)) (e : Fin 2) :
    Fin (2 * (2 * S.card + 1)) :=
  (twoPointLegEquiv S).symm (Sum.inl e)

/-- The flattened local leg `l` belonging to interaction vertex `v`. -/
noncomputable def twoPointInteractionLeg {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    Fin (2 * (2 * S.card + 1)) :=
  (twoPointLegEquiv S).symm (Sum.inr (v, l))

/-- The vertex incident to a flattened two-point leg. -/
noncomputable def twoPointVertexOfLeg {S : Finset (Fin N)}
    (leg : Fin (2 * (2 * S.card + 1))) : TwoPointVertex S :=
  match twoPointLegEquiv S leg with
  | Sum.inl e => Sum.inl e
  | Sum.inr p => Sum.inr p.1

@[simp]
theorem twoPointVertexOfLeg_externalLeg (S : Finset (Fin N)) (e : Fin 2) :
    twoPointVertexOfLeg (twoPointExternalLeg S e) = (Sum.inl e : TwoPointVertex S) := by
  simp [twoPointVertexOfLeg, twoPointExternalLeg]

@[simp]
theorem twoPointVertexOfLeg_interactionLeg {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    twoPointVertexOfLeg (twoPointInteractionLeg v l) = (Sum.inr v : TwoPointVertex S) := by
  simp [twoPointVertexOfLeg, twoPointInteractionLeg]

/-- A two-point diagram with labelled external fields, labelled quartic interaction vertices, and a
perfect pairing of all `4 |S| + 2` legs. -/
structure TwoPointDiagram (ExternalLabel InternalLabel : Type*) (N : ℕ)
    (S : Finset (Fin N)) where
  /-- Labels attached to the two distinguished external vertices. -/
  externalLabel : Fin 2 → ExternalLabel
  /-- Labels attached to the quartic interaction vertices. -/
  vertexLabel : ↥S → InternalLabel
  /-- Perfect pairing of all external and interaction legs. -/
  pairing : Pairing (2 * S.card + 1)

@[ext]
theorem TwoPointDiagram.ext {S : Finset (Fin N)}
    {d₁ d₂ : TwoPointDiagram ExternalLabel InternalLabel N S}
    (he : d₁.externalLabel = d₂.externalLabel)
    (hv : d₁.vertexLabel = d₂.vertexLabel) (hp : d₁.pairing = d₂.pairing) : d₁ = d₂ := by
  cases d₁
  cases d₂
  cases he
  cases hv
  cases hp
  rfl

/-- A two-point diagram as its two label functions and pairing. -/
def TwoPointDiagram.equivData {S : Finset (Fin N)} :
    TwoPointDiagram ExternalLabel InternalLabel N S ≃
      (Fin 2 → ExternalLabel) × (↥S → InternalLabel) × Pairing (2 * S.card + 1) where
  toFun d := (d.externalLabel, d.vertexLabel, d.pairing)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance TwoPointDiagram.instDecidableEq [DecidableEq ExternalLabel]
    [DecidableEq InternalLabel] {S : Finset (Fin N)} :
    DecidableEq (TwoPointDiagram ExternalLabel InternalLabel N S) :=
  TwoPointDiagram.equivData.decidableEq

noncomputable instance TwoPointDiagram.instFintype [Fintype ExternalLabel]
    [Fintype InternalLabel] {S : Finset (Fin N)} :
    Fintype (TwoPointDiagram ExternalLabel InternalLabel N S) :=
  Fintype.ofEquiv _ TwoPointDiagram.equivData.symm

/-- The graph joining distinct external or interaction vertices whose legs are paired. -/
noncomputable def TwoPointDiagram.vertexGraph {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) : SimpleGraph (TwoPointVertex S) :=
  d.pairing.vertexGraph twoPointVertexOfLeg

/-- Every interaction component meets at least one of the two external vertices.  Equivalently, the
diagram has no vacuum component. -/
def TwoPointDiagram.HasNoVacuumComponent {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) : Prop :=
  ∀ v : ↥S, ∃ e : Fin 2,
    d.vertexGraph.Reachable (Sum.inl e : TwoPointVertex S) (Sum.inr v)

/-- The two external vertices belong to the same graph component. -/
def TwoPointDiagram.ExternalVerticesConnected {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) : Prop :=
  d.vertexGraph.Reachable
    (Sum.inl (0 : Fin 2) : TwoPointVertex S)
    (Sum.inl (1 : Fin 2) : TwoPointVertex S)

/-- A connected two-point diagram: no vacuum component remains, and the two external vertices are
connected to one another. -/
def TwoPointDiagram.IsExternallyConnected {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) : Prop :=
  d.HasNoVacuumComponent ∧ d.ExternalVerticesConnected

/-- A globally preconnected two-point graph has no vacuum component. -/
theorem TwoPointDiagram.hasNoVacuumComponent_of_preconnected {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (h : d.vertexGraph.Preconnected) :
    d.HasNoVacuumComponent := by
  intro v
  exact ⟨0, h _ _⟩

/-- Global preconnectedness implies connectedness relative to the two external vertices. -/
theorem TwoPointDiagram.isExternallyConnected_of_preconnected {S : Finset (Fin N)}
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) (h : d.vertexGraph.Preconnected) :
    d.IsExternallyConnected :=
  ⟨d.hasNoVacuumComponent_of_preconnected h, h _ _⟩

/-- Two-point diagrams with no vacuum component. -/
def VacuumFreeTwoPointDiagram (ExternalLabel InternalLabel : Type*) (N : ℕ)
    (S : Finset (Fin N)) : Type _ :=
  {d : TwoPointDiagram ExternalLabel InternalLabel N S // d.HasNoVacuumComponent}

/-- Two-point diagrams connected relative to both external vertices. -/
def ExternallyConnectedTwoPointDiagram (ExternalLabel InternalLabel : Type*) (N : ℕ)
    (S : Finset (Fin N)) : Type _ :=
  {d : TwoPointDiagram ExternalLabel InternalLabel N S // d.IsExternallyConnected}

noncomputable instance VacuumFreeTwoPointDiagram.instFintype [Fintype ExternalLabel]
    [Fintype InternalLabel] {S : Finset (Fin N)} :
    Fintype (VacuumFreeTwoPointDiagram ExternalLabel InternalLabel N S) :=
  Fintype.ofFinite {d : TwoPointDiagram ExternalLabel InternalLabel N S // d.HasNoVacuumComponent}

noncomputable instance ExternallyConnectedTwoPointDiagram.instFintype [Fintype ExternalLabel]
    [Fintype InternalLabel] {S : Finset (Fin N)} :
    Fintype (ExternallyConnectedTwoPointDiagram ExternalLabel InternalLabel N S) :=
  Fintype.ofFinite {d : TwoPointDiagram ExternalLabel InternalLabel N S // d.IsExternallyConnected}

end Common
end SecondQuantization
