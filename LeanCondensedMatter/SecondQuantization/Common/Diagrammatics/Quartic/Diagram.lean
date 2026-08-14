import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Leg
import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# Labelled quartic diagrams

A `QuarticDiagram Label N S` assigns an arbitrary label to each vertex of `S` and perfectly pairs
its four legs. The structure contains no operator algebra, exchange sign, or particle statistics.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

variable {Label : Type*} {N : ℕ}

/-- A labelled four-legged diagram on a finite vertex set. -/
structure QuarticDiagram (Label : Type*) (N : ℕ) (S : Finset (Fin N)) where
  /-- Label attached to each diagram vertex. -/
  vertexLabel : ↥S → Label
  /-- Perfect pairing of all quartic legs. -/
  pairing : Pairing (2 * S.card)

/-- Product of a commutative vertex-local weight over all vertices of a quartic diagram. -/
noncomputable def QuarticDiagram.vertexWeight {M : Type*} [CommMonoid M]
    {S : Finset (Fin N)} (d : QuarticDiagram Label N S) (w : Label → M) : M :=
  ∏ v : ↥S, w (d.vertexLabel v)

@[ext]
theorem QuarticDiagram.ext {S : Finset (Fin N)}
    {d₁ d₂ : QuarticDiagram Label N S} (hv : d₁.vertexLabel = d₂.vertexLabel)
    (hp : d₁.pairing = d₂.pairing) : d₁ = d₂ := by
  cases d₁
  cases d₂
  cases hv
  cases hp
  rfl

/-- A quartic diagram as its vertex-label function and pairing. -/
def QuarticDiagram.equivPair {S : Finset (Fin N)} :
    QuarticDiagram Label N S ≃
      (↥S → Label) × Pairing (2 * S.card) where
  toFun d := (d.vertexLabel, d.pairing)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Labelled quartic diagrams have decidable equality when their labels do. -/
instance QuarticDiagram.instDecidableEq [DecidableEq Label]
    {S : Finset (Fin N)} : DecidableEq (QuarticDiagram Label N S) :=
  QuarticDiagram.equivPair.decidableEq

/-- Labelled quartic diagrams form a finite type when their labels do. -/
noncomputable instance QuarticDiagram.instFintype [Fintype Label]
    {S : Finset (Fin N)} : Fintype (QuarticDiagram Label N S) :=
  Fintype.ofEquiv _ QuarticDiagram.equivPair.symm

end Common
end SecondQuantization
