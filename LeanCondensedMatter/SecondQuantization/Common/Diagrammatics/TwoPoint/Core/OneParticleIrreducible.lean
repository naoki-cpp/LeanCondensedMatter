import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.Core.Diagram

set_option linter.style.header false

/-!
# One-particle irreducibility of two-point pairing diagrams

A propagator is a paired pair of legs. Cutting one propagator must therefore remove that
*particular pair*, rather than deleting an edge of the induced simple vertex graph: several
different propagators may join the same two vertices.

For a vacuum-free two-point diagram with quartic interaction vertices, a one-particle-reducible
(1PR) cut is an internal-to-internal propagator whose removal separates the two distinguished
external vertices. The external propagators themselves are not candidates for this cut: they
represent the external legs that are amputated in the usual proper self-energy convention.

A one-particle-irreducible (1PI) diagram has at least one interaction vertex, is externally
connected, and has no such internal cut. The nonempty condition excludes the bare external-to-
external propagator. This is a purely combinatorial predicate, not an assertion that amplitudes
of 1PI diagrams already sum to the Dyson self-energy.

Convention: Fetter and Walecka, *Quantum Theory of Many-Particle Systems* (1971), the
one-particle-irreducible/proper self-energy expansion.
-/

namespace SecondQuantization
namespace Common

variable {ExternalLabel InternalLabel : Type*} {N : ℕ} {S : Finset (Fin N)}

/-- The vertex graph after removing exactly the propagator paired with `cut`.

Excluding both legs in the selected pair keeps any other propagators between the same
vertices intact, unlike deleting an edge from the simple `vertexGraph`. -/
noncomputable def TwoPointDiagram.vertexGraphWithoutPropagator
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (cut : Fin (2 * (2 * S.card + 1))) : SimpleGraph (TwoPointVertex S) where
  Adj v w := v ≠ w ∧
    ∃ leg : Fin (2 * (2 * S.card + 1)),
      leg ≠ cut ∧ d.pairing.partner leg ≠ cut ∧
        twoPointVertexOfLeg leg = v ∧
        twoPointVertexOfLeg (d.pairing.partner leg) = w
  symm := ⟨by
    rintro v w ⟨hne, leg, hleg, hpartner, hv, hw⟩
    refine ⟨hne.symm, d.pairing.partner leg, hpartner, ?_, hw, ?_⟩
    · simpa only [d.pairing.partner_involutive] using hleg
    · simpa only [d.pairing.partner_involutive] using hv⟩
  loopless := ⟨by
    rintro v ⟨hvv, -⟩
    exact hvv rfl⟩

/-- Cutting a single paired propagator cannot introduce a new vertex adjacency. -/
theorem TwoPointDiagram.vertexGraphWithoutPropagator_le_vertexGraph
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (cut : Fin (2 * (2 * S.card + 1))) :
    d.vertexGraphWithoutPropagator cut ≤ d.vertexGraph := by
  intro v w h
  rcases h with ⟨hne, leg, _, _, hv, hw⟩
  exact ⟨hne, leg, hv, hw⟩

/-- A propagator is internal when both of its endpoints are interaction vertices. -/
def TwoPointDiagram.IsInternalPropagator
    (d : TwoPointDiagram ExternalLabel InternalLabel N S)
    (leg : Fin (2 * (2 * S.card + 1))) : Prop :=
  (∃ v : ↥S, twoPointVertexOfLeg leg = Sum.inr v) ∧
    (∃ w : ↥S, twoPointVertexOfLeg (d.pairing.partner leg) = Sum.inr w)

/-- A connected two-point diagram is one-particle reducible when cutting one internal
propagator disconnects its external vertices. -/
def TwoPointDiagram.IsOneParticleReducible
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) : Prop :=
  d.IsExternallyConnected ∧
    ∃ cut : Fin (2 * (2 * S.card + 1)),
      d.IsInternalPropagator cut ∧
        ¬ (d.vertexGraphWithoutPropagator cut).Reachable
          (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))

/-- A proper one-particle-irreducible two-point diagram: a nontrivial externally connected
diagram that stays externally connected after cutting *any internal propagator*. -/
def TwoPointDiagram.IsOneParticleIrreducible
    (d : TwoPointDiagram ExternalLabel InternalLabel N S) : Prop :=
  S.Nonempty ∧ d.IsExternallyConnected ∧
    ∀ cut : Fin (2 * (2 * S.card + 1)),
      d.IsInternalPropagator cut →
        (d.vertexGraphWithoutPropagator cut).Reachable
          (Sum.inl (0 : Fin 2)) (Sum.inl (1 : Fin 2))

/-- Every proper 1PI two-point diagram is externally connected and hence vacuum-free. -/
theorem TwoPointDiagram.IsOneParticleIrreducible.isExternallyConnected
    {d : TwoPointDiagram ExternalLabel InternalLabel N S}
    (h : d.IsOneParticleIrreducible) : d.IsExternallyConnected :=
  h.2.1

/-- Proper one-particle-irreducible two-point diagrams, with vertex labels and pairing retained. -/
def OneParticleIrreducibleTwoPointDiagram
    (ExternalLabel InternalLabel : Type*) (N : ℕ) (S : Finset (Fin N)) : Type _ :=
  {d : TwoPointDiagram ExternalLabel InternalLabel N S // d.IsOneParticleIrreducible}

noncomputable instance OneParticleIrreducibleTwoPointDiagram.instFintype
    [Fintype ExternalLabel] [Fintype InternalLabel] :
    Fintype (OneParticleIrreducibleTwoPointDiagram ExternalLabel InternalLabel N S) :=
  Fintype.ofFinite _

end Common
end SecondQuantization
