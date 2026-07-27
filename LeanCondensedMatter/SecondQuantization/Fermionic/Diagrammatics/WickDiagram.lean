import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Diagram
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.QuarticInteraction

set_option linter.style.header false

/-!
# Fermionic quartic Wick diagrams

`QuarticWickDiagram Mode N S` specializes the statistics-independent
`Common.QuarticDiagram` to fermionic `QuarticVertexLabel Mode` labels. Creation and annihilation
semantics remain in the label and amplitude layers; the stored diagram data are only vertex labels
and a perfect pairing of the four legs per vertex.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- A quartic diagram whose vertex labels describe fermionic interaction vertices. -/
abbrev QuarticWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) :=
  Common.QuarticDiagram (QuarticVertexLabel Mode) N S

@[ext]
theorem QuarticWickDiagram.ext {S : Finset (Fin N)}
    {d₁ d₂ : QuarticWickDiagram Mode N S} (hv : d₁.vertexLabel = d₂.vertexLabel)
    (hp : d₁.pairing = d₂.pairing) : d₁ = d₂ :=
  Common.QuarticDiagram.ext hv hp

/-- A fermionic quartic Wick diagram as its vertex-label function and pairing. -/
def QuarticWickDiagram.equivPair {S : Finset (Fin N)} :
    QuarticWickDiagram Mode N S ≃
      (↥S → QuarticVertexLabel Mode) × Common.BlochDeDominicis.Pairing (2 * S.card) :=
  Common.QuarticDiagram.equivPair

/-- `QuarticWickDiagram Mode N S` has decidable equality when `Mode` does. -/
instance QuarticWickDiagram.instDecidableEq [DecidableEq Mode] {S : Finset (Fin N)} :
    DecidableEq (QuarticWickDiagram Mode N S) :=
  QuarticWickDiagram.equivPair.decidableEq

/-- `QuarticWickDiagram Mode N S` is finite when `Mode` is finite. -/
noncomputable instance QuarticWickDiagram.instFintype [DecidableEq Mode] [Fintype Mode]
    {S : Finset (Fin N)} : Fintype (QuarticWickDiagram Mode N S) :=
  Fintype.ofEquiv _ QuarticWickDiagram.equivPair.symm

end SecondQuantization
