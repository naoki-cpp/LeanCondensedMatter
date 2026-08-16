import LeanCondensedMatter.Combinatorics.PerfectPairing.VertexGraph
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction

set_option linter.style.header false

/-!
# Restricting perfect pairings by pairing-graph components

A pairing-induced vertex graph assigns every leg to an incident vertex.  Whenever a component
classifier is constant along graph reachability, the fiber of legs incident to one component is
invariant under the pairing partner permutation.  This module packages that generic component-fiber
restriction so diagrammatic users only need to provide their vertex classifier and its reachability
compatibility.

The construction is independent of diagram labels, particle statistics, and the concrete
representation of connected components.
-/

namespace Combinatorics

/-- A leg belongs to component `B` when the component classifier of its incident vertex is `B`. -/
def Pairing.legInComponent {n : ℕ} {Vertex Component : Type*} (_pairing : Pairing n)
    (vertexOfLeg : Fin (2 * n) → Vertex) (component : Vertex → Component)
    (B : Component) (leg : Fin (2 * n)) : Prop :=
  component (vertexOfLeg leg) = B

/-- Pairing partners have incident vertices with the same component classification whenever the
classifier is constant along pairing-graph reachability. -/
theorem Pairing.component_vertex_partner_eq {n : ℕ} {Vertex Component : Type*}
    (pairing : Pairing n) (vertexOfLeg : Fin (2 * n) → Vertex)
    (component : Vertex → Component)
    (hcomponent : ∀ {v w}, (pairing.vertexGraph vertexOfLeg).Reachable v w →
      component v = component w)
    (leg : Fin (2 * n)) :
    component (vertexOfLeg (pairing.partner leg)) = component (vertexOfLeg leg) :=
  hcomponent (pairing.vertexGraph_reachable_partner vertexOfLeg leg)

/-- Membership in one component-leg fiber is invariant under the pairing partner permutation. -/
theorem Pairing.legInComponent_partner_iff {n : ℕ} {Vertex Component : Type*}
    (pairing : Pairing n) (vertexOfLeg : Fin (2 * n) → Vertex)
    (component : Vertex → Component)
    (hcomponent : ∀ {v w}, (pairing.vertexGraph vertexOfLeg).Reachable v w →
      component v = component w)
    (B : Component) (leg : Fin (2 * n)) :
    pairing.legInComponent vertexOfLeg component B leg ↔
      pairing.legInComponent vertexOfLeg component B (pairing.partner leg) := by
  unfold Pairing.legInComponent
  rw [pairing.component_vertex_partner_eq vertexOfLeg component hcomponent leg]

/-- The pairing partner permutation restricted to the legs classified into one component. -/
noncomputable def Pairing.componentPartnerSubtypePerm
    {n : ℕ} {Vertex Component : Type*} (pairing : Pairing n)
    (vertexOfLeg : Fin (2 * n) → Vertex) (component : Vertex → Component)
    (hcomponent : ∀ {v w}, (pairing.vertexGraph vertexOfLeg).Reachable v w →
      component v = component w)
    (B : Component) :
    Equiv.Perm {leg : Fin (2 * n) // pairing.legInComponent vertexOfLeg component B leg} :=
  pairing.partnerSubtypePerm (pairing.legInComponent vertexOfLeg component B) fun leg =>
    pairing.legInComponent_partner_iff vertexOfLeg component hcomponent B leg

@[simp]
theorem Pairing.componentPartnerSubtypePerm_val
    {n : ℕ} {Vertex Component : Type*} (pairing : Pairing n)
    (vertexOfLeg : Fin (2 * n) → Vertex) (component : Vertex → Component)
    (hcomponent : ∀ {v w}, (pairing.vertexGraph vertexOfLeg).Reachable v w →
      component v = component w)
    (B : Component)
    (leg : {leg : Fin (2 * n) // pairing.legInComponent vertexOfLeg component B leg}) :
    ((pairing.componentPartnerSubtypePerm vertexOfLeg component hcomponent B leg :
        {leg : Fin (2 * n) // pairing.legInComponent vertexOfLeg component B leg}) :
      Fin (2 * n)) = pairing.partner leg := by
  simpa only [Pairing.componentPartnerSubtypePerm] using
    pairing.partnerSubtypePerm_val (pairing.legInComponent vertexOfLeg component B)
      (fun i => pairing.legInComponent_partner_iff vertexOfLeg component hcomponent B i) leg

/-- The component-restricted partner permutation is itself a fixed-point-free involution. -/
theorem Pairing.isPairing_componentPartnerSubtypePerm
    {n : ℕ} {Vertex Component : Type*} (pairing : Pairing n)
    (vertexOfLeg : Fin (2 * n) → Vertex) (component : Vertex → Component)
    (hcomponent : ∀ {v w}, (pairing.vertexGraph vertexOfLeg).Reachable v w →
      component v = component w)
    (B : Component) :
    IsPairing (pairing.componentPartnerSubtypePerm vertexOfLeg component hcomponent B) := by
  simpa only [Pairing.componentPartnerSubtypePerm] using
    pairing.isPairing_partnerSubtypePerm (pairing.legInComponent vertexOfLeg component B)
      (fun i => pairing.legInComponent_partner_iff vertexOfLeg component hcomponent B i)

/-- Restrict a pairing to one component-leg fiber and reindex that fiber by `Fin (2 * m)`. -/
noncomputable def Pairing.restrictComponentAlongEquiv
    {n m : ℕ} {Vertex Component : Type*} (pairing : Pairing n)
    (vertexOfLeg : Fin (2 * n) → Vertex) (component : Vertex → Component)
    (hcomponent : ∀ {v w}, (pairing.vertexGraph vertexOfLeg).Reachable v w →
      component v = component w)
    (B : Component)
    (e : {leg : Fin (2 * n) // pairing.legInComponent vertexOfLeg component B leg} ≃ Fin (2 * m)) :
    Pairing m :=
  pairing.restrictAlongEquiv (pairing.legInComponent vertexOfLeg component B)
    (fun leg => pairing.legInComponent_partner_iff vertexOfLeg component hcomponent B leg) e

/-- The component-restricted pairing partner agrees with the ambient partner through the chosen
component-leg reindexing. -/
@[simp]
theorem Pairing.restrictComponentAlongEquiv_partner
    {n m : ℕ} {Vertex Component : Type*} (pairing : Pairing n)
    (vertexOfLeg : Fin (2 * n) → Vertex) (component : Vertex → Component)
    (hcomponent : ∀ {v w}, (pairing.vertexGraph vertexOfLeg).Reachable v w →
      component v = component w)
    (B : Component)
    (e : {leg : Fin (2 * n) // pairing.legInComponent vertexOfLeg component B leg} ≃ Fin (2 * m))
    (leg : {leg : Fin (2 * n) // pairing.legInComponent vertexOfLeg component B leg}) :
    (pairing.restrictComponentAlongEquiv vertexOfLeg component hcomponent B e).partner (e leg) =
      e (pairing.componentPartnerSubtypePerm vertexOfLeg component hcomponent B leg) := by
  simpa only [Pairing.restrictComponentAlongEquiv, Pairing.componentPartnerSubtypePerm] using
    pairing.restrictAlongEquiv_partner (pairing.legInComponent vertexOfLeg component B)
      (fun i => pairing.legInComponent_partner_iff vertexOfLeg component hcomponent B i) e leg

end Combinatorics
