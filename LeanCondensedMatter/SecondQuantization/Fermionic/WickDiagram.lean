import LeanCondensedMatter.SecondQuantization.Fermionic.QuarticInteraction
import LeanCondensedMatter.Combinatorics.PerfectPairing

set_option linter.style.header false

/-!
# Quartic Wick diagrams: leg indexing and the diagram structure (core)

Step 6 (PR 4a) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`): the
first piece of `Fermionic/WickDiagram.lean`, split per the plan's own fallback ("if this PR grows
too large, split into `WickDiagram/Core.lean`/`WickDiagram/ConnectedComponents.lean`") — this file
covers leg indexing and the bare `QuarticWickDiagram` structure only. Connected-component
partitioning, the derived `SimpleGraph`, and `IsConnected` are deliberately deferred to a
follow-up file/PR, not included here.

A quartic Wick diagram on a finite vertex set `S : Finset (Fin N)` (each vertex labelled by a
`QuarticVertexLabel Mode`) has `4 * S.card` "legs" — one per ladder operator across all vertices —
and a perfect pairing of those legs (`Common.BlochDeDominicis.Pairing (2 * S.card)`, since
`Pairing n` pairs `Fin (2 * n)` positions, so `Pairing (2 * S.card)` pairs `Fin (2 * (2 *
S.card))`, i.e. exactly `4 * S.card` legs). This file does **not** distinguish leg *kinds*
(creation vs. annihilation) at the pairing level — see `Fermionic/QuarticInteraction.lean`'s fixed
vertex operator order for that; a pairing here is purely combinatorial, matching `Pairing`'s own
scope.

**Vertex/leg/position bookkeeping, kept separate per the plan's explicit warning against
conflating them**:
- *vertex*: an element of `↥S` (a `Fintype` of cardinality `S.card`)
- *local leg*: an element of `Fin 4` (which of the vertex's four ladder operators)
- *flattened leg position*: an element of `Fin (2 * (2 * S.card))`, the index `Pairing (2 *
  S.card)` pairs

`quarticLegEquiv` is the one named equivalence translating between the flattened position and the
`(vertex, local leg)` pair; `vertexOfLeg`/`localLegOfLeg` are its two projections. No raw
`Fin.cast`/arithmetic rewriting of leg positions should be needed outside this equivalence.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **The leg-indexing equivalence**: a flattened leg position is the same data as a choice of
vertex in `S` together with a local leg `Fin 4` (which of that vertex's four ladder operators). -/
noncomputable def quarticLegEquiv (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card)) ≃ (↥S) × Fin 4 :=
  (finCongr (by ring)).trans
    ((finProdFinEquiv (m := S.card) (n := 4)).symm.trans
      (((finCongr (Fintype.card_coe S)).symm.trans (Fintype.equivFin (↥S)).symm).prodCongr
        (Equiv.refl (Fin 4))))

/-- **The vertex a flattened leg position belongs to.** -/
noncomputable def vertexOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : ↥S :=
  (quarticLegEquiv S leg).1

/-- **Which of its vertex's four ladder operators a flattened leg position picks out.** -/
noncomputable def localLegOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : Fin 4 :=
  (quarticLegEquiv S leg).2

/-- **A quartic Wick diagram** on vertex set `S`: a `QuarticVertexLabel Mode` assignment to each
vertex, together with a perfect pairing of the resulting `4 * S.card` legs. Purely combinatorial —
no connectivity/graph structure yet (see the module docstring). -/
structure QuarticWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) where
  /-- Each vertex's quartic interaction label. -/
  vertexLabel : ↥S → QuarticVertexLabel Mode
  /-- The perfect pairing of the diagram's `4 * S.card` legs. -/
  pairing : Common.BlochDeDominicis.Pairing (2 * S.card)

end SecondQuantization
