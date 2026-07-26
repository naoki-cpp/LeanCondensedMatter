import LeanCondensedMatter.SecondQuantization.Common.QuarticLeg
import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# Labelled quartic diagrams

A `QuarticDiagram Label N S` assigns an arbitrary label to each vertex of `S` and perfectly pairs
its four legs. The structure contains no operator algebra, exchange sign, or particle statistics.
-/

namespace SecondQuantization
namespace Common

variable {Label : Type*} {N : ℕ}

/-- A labelled four-legged diagram on a finite vertex set. -/
structure QuarticDiagram (Label : Type*) (N : ℕ) (S : Finset (Fin N)) where
  vertexLabel : ↥S → Label
  pairing : BlochDeDominicis.Pairing (2 * S.card)

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
      (↥S → Label) × BlochDeDominicis.Pairing (2 * S.card) where
  toFun d := (d.vertexLabel, d.pairing)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Labelled quartic diagrams have decidable equality when their labels do. Statistics-specific
aliases may provide higher-priority compatibility instances. -/
instance (priority := 100) QuarticDiagram.instDecidableEq [DecidableEq Label]
    {S : Finset (Fin N)} : DecidableEq (QuarticDiagram Label N S) :=
  QuarticDiagram.equivPair.decidableEq

/-- Labelled quartic diagrams form a finite type when their labels do. Statistics-specific aliases
may provide higher-priority compatibility instances. -/
noncomputable instance (priority := 100) QuarticDiagram.instFintype [Fintype Label]
    {S : Finset (Fin N)} : Fintype (QuarticDiagram Label N S) :=
  Fintype.ofEquiv _ QuarticDiagram.equivPair.symm

end Common
end SecondQuantization
