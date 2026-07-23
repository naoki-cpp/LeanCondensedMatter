import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option linter.style.header false

/-!
# Quartic Wick diagram connectivity

Step 6 (PR 4b) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`):
connected-component structure on top of `WickDiagram.lean`'s bare `QuarticWickDiagram`, deferred
from PR 4a per the plan's own explicit fallback.

`QuarticWickDiagram.vertexGraph` is the derived `SimpleGraph` on the diagram's vertex set: two
*distinct* vertices are adjacent iff some leg of one is paired (by the diagram's `pairing`) to some
leg of the other. Same-vertex contractions ("tadpoles") are part of a vertex's own data — they are
deliberately **not** turned into edges (a `SimpleGraph` is irreflexive), matching the plan's
explicit instruction. `IsConnected` is stated as `Preconnected ∧ S.Nonempty` rather than via
`SimpleGraph.Connected` directly, since the latter needs a `Nonempty ↥S` *instance*, awkward for a
`Prop` that must also make sense (as `False`) for the empty vertex set — an equivalent formulation
of `SimpleGraph.Connected` itself, with an explicit empty/singleton convention, per the original
design's own allowance ("または、空集合・singletonの規約を明示した同値な定義にします").

**`ConnectedQuarticWickDiagram` is a genuinely separate, smaller deliverable than the abstract
`WeightedDiagramFamily.decompose` equivalence still needs.** `IsConnected` only lets a diagram be
*classified* as connected or not — `ConnectedQuarticWickDiagram` below is its subtype. It is
*not* a substitute for `componentPartition : Finpartition S` (mapping
`SimpleGraph.ConnectedComponent` fibers back to `Finset (Fin N)` blocks), vertex-label/pairing
*restriction* to each component, component-diagram *reassembly*, or the proof that restriction and
reassembly are mutually inverse — all of that remains future work, planned for a dedicated PR once
a concrete `WeightedDiagramFamily Mode N` instantiation is being built (after PR 6's
`dysonVertexMoment_eq_sum_quarticWickDiagram`; see `notes/roadmaps/second-quantization.md`).
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **The derived connectivity graph** of a quartic Wick diagram: distinct vertices `v ≠ w` are
adjacent iff some leg at `v` is paired to some leg at `w`. -/
noncomputable def QuarticWickDiagram.vertexGraph {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) : SimpleGraph (↥S) where
  Adj v w := v ≠ w ∧ ∃ leg : Fin (2 * (2 * S.card)),
    vertexOfLeg leg = v ∧ vertexOfLeg (d.pairing.partner leg) = w
  symm := ⟨by
    rintro v w ⟨hvw, leg, hv, hw⟩
    refine ⟨hvw.symm, d.pairing.partner leg, hw, ?_⟩
    rw [d.pairing.partner_involutive leg, hv]⟩
  loopless := ⟨by
    rintro v ⟨hvv, -⟩
    exact hvv rfl⟩

/-- **A quartic Wick diagram is connected** iff its vertex graph is preconnected and its vertex
set is nonempty — spelled out this way (rather than via `SimpleGraph.Connected`, which needs a
`Nonempty ↥S` instance) so it makes sense, as `False`, on the empty vertex set too. -/
def QuarticWickDiagram.IsConnected {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) : Prop :=
  d.vertexGraph.Preconnected ∧ S.Nonempty

/-- **The subtype of connected quartic Wick diagrams** on vertex set `S`. No finiteness constraint
on `Mode` — connectivity never touches `Mode`'s cardinality (see `WickDiagram.lean`'s module
docstring). -/
def ConnectedQuarticWickDiagram (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) : Type _ :=
  {d : QuarticWickDiagram Mode N S // d.IsConnected}

end SecondQuantization
