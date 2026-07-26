import LeanCondensedMatter.SecondQuantization.Fermionic.QuarticInteraction
import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# Quartic Wick diagrams

A quartic Wick diagram on a finite vertex set `S : Finset (Fin N)` assigns a
`QuarticVertexLabel Mode` to each vertex and perfectly pairs the resulting `4 * S.card` legs.
The pairing is purely combinatorial; creation and annihilation semantics come from the fixed local
leg convention of `QuarticVertexLabel`.

`orderedQuarticLegEquiv` identifies a flattened leg position with a vertex slot and one of four
local legs. `quarticVertexEquiv` chooses an arbitrary fixed enumeration of `S`, and
`quarticLegEquiv` uses that enumeration to identify flattened positions with `↥S × Fin 4`.
All downstream restriction and relabeling constructions should use these named equivalences rather
than reconstructing an enumeration independently.

The local-leg convention is

`0 ↦ create₁`, `1 ↦ create₂`, `2 ↦ annihilate₂`, `3 ↦ annihilate₁`,

matching the operator order in `quarticVertexOperator`.

`QuarticWickDiagram` itself imposes no finiteness constraint on `Mode`. Decidable equality and
finite enumeration are supplied separately when `Mode` has the required instances.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- The flattened-leg/local-leg equivalence for an abstract vertex count `n`. -/
noncomputable def orderedQuarticLegEquiv (n : ℕ) : Fin (2 * (2 * n)) ≃ Fin n × Fin 4 :=
  (finCongr (by ring)).trans (finProdFinEquiv (m := n) (n := 4)).symm

/-- The fixed vertex enumeration used by `quarticLegEquiv`. -/
noncomputable def quarticVertexEquiv (S : Finset (Fin N)) : Fin S.card ≃ (↥S) :=
  (finCongr (Fintype.card_coe S)).symm.trans (Fintype.equivFin (↥S)).symm

/-- A flattened leg position is equivalent to a vertex of `S` and a local leg. -/
noncomputable def quarticLegEquiv (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card)) ≃ (↥S) × Fin 4 :=
  (orderedQuarticLegEquiv S.card).trans ((quarticVertexEquiv S).prodCongr (Equiv.refl (Fin 4)))

/-- The vertex containing a flattened leg position. -/
noncomputable def vertexOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : ↥S :=
  (quarticLegEquiv S leg).1

/-- The local leg selected by a flattened leg position. -/
noncomputable def localLegOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : Fin 4 :=
  (quarticLegEquiv S leg).2

/-- The flattened leg position corresponding to a vertex and local leg. -/
noncomputable def legOfVertexLocal {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    Fin (2 * (2 * S.card)) :=
  (quarticLegEquiv S).symm (v, l)

@[simp]
theorem vertexOfLeg_legOfVertexLocal {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    vertexOfLeg (legOfVertexLocal v l) = v := by
  simp [vertexOfLeg, legOfVertexLocal]

@[simp]
theorem localLegOfLeg_legOfVertexLocal {S : Finset (Fin N)} (v : ↥S) (l : Fin 4) :
    localLegOfLeg (legOfVertexLocal v l) = l := by
  simp [localLegOfLeg, legOfVertexLocal]

/-- A quartic Wick diagram on vertex set `S`. -/
structure QuarticWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) where
  /-- Each vertex's quartic interaction label. -/
  vertexLabel : ↥S → QuarticVertexLabel Mode
  /-- The perfect pairing of the diagram's `4 * S.card` legs. -/
  pairing : Common.BlochDeDominicis.Pairing (2 * S.card)

@[ext]
theorem QuarticWickDiagram.ext {S : Finset (Fin N)}
    {d₁ d₂ : QuarticWickDiagram Mode N S} (hv : d₁.vertexLabel = d₂.vertexLabel)
    (hp : d₁.pairing = d₂.pairing) : d₁ = d₂ := by
  cases d₁
  cases d₂
  cases hv
  cases hp
  rfl

/-- A quartic Wick diagram as a pair of its vertex-label function and pairing. -/
def QuarticWickDiagram.equivPair {S : Finset (Fin N)} :
    QuarticWickDiagram Mode N S ≃
      (↥S → QuarticVertexLabel Mode) × Common.BlochDeDominicis.Pairing (2 * S.card) where
  toFun d := (d.vertexLabel, d.pairing)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `QuarticWickDiagram Mode N S` has decidable equality when `Mode` does. -/
instance QuarticWickDiagram.instDecidableEq [DecidableEq Mode] {S : Finset (Fin N)} :
    DecidableEq (QuarticWickDiagram Mode N S) :=
  QuarticWickDiagram.equivPair.decidableEq

/-- `QuarticWickDiagram Mode N S` is finite when `Mode` is finite. -/
noncomputable instance QuarticWickDiagram.instFintype [DecidableEq Mode] [Fintype Mode]
    {S : Finset (Fin N)} : Fintype (QuarticWickDiagram Mode N S) :=
  Fintype.ofEquiv _ QuarticWickDiagram.equivPair.symm

end SecondQuantization
