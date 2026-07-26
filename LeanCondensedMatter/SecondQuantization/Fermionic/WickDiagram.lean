import LeanCondensedMatter.SecondQuantization.Common.QuarticLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.QuarticInteraction
import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# Quartic Wick diagrams

A quartic Wick diagram on a finite vertex set `S : Finset (Fin N)` assigns a
`QuarticVertexLabel Mode` to each vertex and perfectly pairs the resulting `4 * S.card` legs.
The pairing is combinatorial; creation and annihilation semantics come from the fixed local-leg
convention

`0 ↦ create₁`, `1 ↦ create₂`, `2 ↦ annihilate₂`, `3 ↦ annihilate₁`,

matching the operator order in `quarticVertexOperator`. Statistics-independent flattened-leg
bookkeeping is provided by `SecondQuantization.Common.QuarticLeg`.

`QuarticWickDiagram` imposes no finiteness constraint on `Mode`. Decidable equality and finite
enumeration are supplied separately when `Mode` has the required instances.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

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
