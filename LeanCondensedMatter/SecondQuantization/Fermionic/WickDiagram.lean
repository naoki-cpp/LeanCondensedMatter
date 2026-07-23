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
`(vertex, local leg)` pair; `vertexOfLeg`/`localLegOfLeg`/`legOfVertexLocal` are its projections
and inverse. No raw `Fin.cast`/arithmetic rewriting of leg positions should be needed outside this
equivalence.

**The local-leg `Fin 4` convention, fixed here and required to match
`QuarticInteraction.lean`'s vertex operator order exactly** (since `Pairing` acts on *ordered*
positions and the fermionic crossing sign downstream depends on that order):

`0 ↦ create₁`, `1 ↦ create₂`, `2 ↦ annihilate₂`, `3 ↦ annihilate₁`

matching `quarticVertexOperator q = c_{q.create₁}† c_{q.create₂}† c_{q.annihilate₂}
c_{q.annihilate₁}` position-by-position.

**Vertex enumeration is not `Fin N`-order-preserving.** `quarticLegEquiv` builds its `↥S`
component from `Fintype.equivFin (↥S)`, an arbitrary (if fixed) enumeration of `S`'s elements —
not necessarily the order induced by `S`'s ambient `Fin N` order. This is harmless as long as
every downstream construction (component restriction, relabeling, ...) consistently goes through
this same `quarticLegEquiv`, rather than re-deriving its own enumeration of `↥S`.

**`QuarticWickDiagram` itself imposes no finiteness constraint on `Mode`** — its two fields
(`vertexLabel : ↥S → QuarticVertexLabel Mode`, `pairing : Pairing (2 * S.card)`) make sense for
any `Mode : Type*`, and downstream connectivity (`WickDiagramConnected.lean`) never touches
`Mode`'s cardinality at all. `[DecidableEq Mode] [Fintype Mode]` is needed only to *derive*
`DecidableEq`/`Fintype` instances on `QuarticWickDiagram Mode N S` itself (so PR 6's sum over all
diagrams on a fixed vertex set makes sense) — those instances are supplied separately, below,
rather than baked into the structure's own parameter list, so callers that don't need to
enumerate diagrams (e.g. `WickDiagramConnected.lean`) aren't forced to assume `Mode` is finite.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **The flattened-leg/local-leg equivalence, generic over an abstract vertex count `n`**: a
flattened leg position among `n` vertices' worth of legs is the same data as a choice of vertex
slot `Fin n` together with a local leg `Fin 4`. Vertex-set-independent (unlike `quarticLegEquiv`
below, which composes this with `quarticVertexEquiv` to land on `↥S`) — used directly by the
vertex-order API (`WickDiagram/Ordered.lean`), where the vertex slot is filled by an arbitrary
order `Fin S.card ≃ ↥S` rather than the fixed enumeration `quarticVertexEquiv` picks. -/
noncomputable def orderedQuarticLegEquiv (n : ℕ) : Fin (2 * (2 * n)) ≃ Fin n × Fin 4 :=
  (finCongr (by ring)).trans (finProdFinEquiv (m := n) (n := 4)).symm

/-- **The fixed vertex enumeration** `quarticLegEquiv` uses for `↥S` — an arbitrary (if fixed)
choice, not necessarily respecting `S`'s ambient `Fin N` order (see the module docstring's
"Vertex enumeration is not `Fin N`-order-preserving" note). -/
noncomputable def quarticVertexEquiv (S : Finset (Fin N)) : Fin S.card ≃ (↥S) :=
  (finCongr (Fintype.card_coe S)).symm.trans (Fintype.equivFin (↥S)).symm

/-- **The leg-indexing equivalence**: a flattened leg position is the same data as a choice of
vertex in `S` together with a local leg `Fin 4` (which of that vertex's four ladder operators). -/
noncomputable def quarticLegEquiv (S : Finset (Fin N)) :
    Fin (2 * (2 * S.card)) ≃ (↥S) × Fin 4 :=
  (orderedQuarticLegEquiv S.card).trans ((quarticVertexEquiv S).prodCongr (Equiv.refl (Fin 4)))

/-- **The vertex a flattened leg position belongs to.** -/
noncomputable def vertexOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : ↥S :=
  (quarticLegEquiv S leg).1

/-- **Which of its vertex's four ladder operators a flattened leg position picks out.** -/
noncomputable def localLegOfLeg {S : Finset (Fin N)} (leg : Fin (2 * (2 * S.card))) : Fin 4 :=
  (quarticLegEquiv S leg).2

/-- **The flattened leg position for a given vertex and local leg** — `quarticLegEquiv`'s
inverse, spelled out for callers that build a position from `(vertex, local leg)` data rather than
decomposing one. -/
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

/-- **A quartic Wick diagram** on vertex set `S`: a `QuarticVertexLabel Mode` assignment to each
vertex, together with a perfect pairing of the resulting `4 * S.card` legs. Purely combinatorial —
no connectivity/graph structure yet (see the module docstring), and no finiteness constraint on
`Mode` (see the module docstring's "`QuarticWickDiagram` itself imposes no finiteness constraint"
note) — `DecidableEq`/`Fintype` instances requiring `[DecidableEq Mode] [Fintype Mode]` are
supplied separately below, via `QuarticWickDiagram.equivPair`, rather than by a `deriving` clause
here. -/
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

/-- **A quartic Wick diagram, as a pair of its two fields** — the equivalence
`DecidableEq`/`Fintype` on `QuarticWickDiagram Mode N S` are transported along, once `Mode` is
finite (see the module docstring). -/
def QuarticWickDiagram.equivPair {S : Finset (Fin N)} :
    QuarticWickDiagram Mode N S ≃
      (↥S → QuarticVertexLabel Mode) × Common.BlochDeDominicis.Pairing (2 * S.card) where
  toFun d := (d.vertexLabel, d.pairing)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`QuarticWickDiagram Mode N S` has decidable equality**, once `Mode` does — transported along
`QuarticWickDiagram.equivPair` rather than a `deriving` clause on the structure itself (see the
module docstring). -/
instance QuarticWickDiagram.instDecidableEq [DecidableEq Mode] {S : Finset (Fin N)} :
    DecidableEq (QuarticWickDiagram Mode N S) :=
  QuarticWickDiagram.equivPair.decidableEq

/-- **`QuarticWickDiagram Mode N S` is finite**, once `Mode` is — transported along
`QuarticWickDiagram.equivPair` rather than a `deriving` clause on the structure itself (needed for
PR 6's sum over all diagrams on a fixed vertex set; see the module docstring). -/
noncomputable instance QuarticWickDiagram.instFintype [DecidableEq Mode] [Fintype Mode]
    {S : Finset (Fin N)} : Fintype (QuarticWickDiagram Mode N S) :=
  Fintype.ofEquiv _ QuarticWickDiagram.equivPair.symm

end SecondQuantization
