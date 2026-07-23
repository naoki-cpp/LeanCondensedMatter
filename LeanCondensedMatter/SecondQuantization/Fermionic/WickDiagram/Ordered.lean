import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram
import LeanCondensedMatter.Combinatorics.PerfectPairing.Relabel

set_option linter.style.header false

/-!
# Vertex orders and the ordered-data equivalence for quartic Wick diagrams

Step 6 (PR 5b) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`): the
second sub-piece of PR 5's design, transporting a `QuarticWickDiagram`'s pairing onto the leg
enumeration induced by an arbitrary **vertex order** — a bijection `Fin S.card ≃ ↥S` assigning a
time slot `0, 1, …, S.card - 1` to each vertex, needed so PR 5c's ordered-simplex amplitude
(indexed by `Fin S.card`, not `↥S`) can be built.

`quarticWickDiagramEquivOrderedData` is the resulting equivalence between `QuarticWickDiagram Mode
N S` (for the *fixed* vertex set `S`) and `OrderedQuarticWickData Mode S.card` (a vertex-label
sequence indexed by `Fin S.card` together with a pairing already transported onto that same slot
enumeration) — this is all PR 6 needs to reindex its diagram sum. **Deliberately excluded**:
relabeling between `QuarticWickDiagram Mode N S` and `QuarticWickDiagram Mode N T` for *different*
vertex sets `S ≠ T` — that mixes cardinality equalities, dependent-subtype casts, and pairing
position casts in a way that risks the same kernel-timeout failure mode `notes/caveats.md`
documents for dependent-`Sigma`-type reindexing, and is not needed until a future component
restriction/reassembly PR.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [Fintype Mode] {N : ℕ}

/-- **A vertex order**: a bijection between time slots `Fin S.card` and the diagram's vertex set
`↥S`. -/
abbrev QuarticVertexOrder (S : Finset (Fin N)) := Fin S.card ≃ (↥S)

/-- **The leg relabeling induced by a vertex order**: translates a flattened leg position from
the ordered-data enumeration (`orderedQuarticLegEquiv`, built on `Fin S.card`-indexed slots) to
the diagram's own fixed leg enumeration (`quarticLegEquiv`, built on `quarticVertexEquiv`'s
enumeration of `↥S`), by routing through `order` on the vertex component and leaving the local leg
untouched. -/
noncomputable def orderedLegToDiagramLeg (S : Finset (Fin N)) (order : QuarticVertexOrder S) :
    Equiv.Perm (Fin (2 * (2 * S.card))) :=
  (orderedQuarticLegEquiv S.card).trans
    ((order.prodCongr (Equiv.refl (Fin 4))).trans (quarticLegEquiv S).symm)

/-- **A diagram's pairing, transported onto a vertex order's slot enumeration.** -/
noncomputable def QuarticWickDiagram.pairingInOrder {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : QuarticVertexOrder S) :
    Common.BlochDeDominicis.Pairing (2 * S.card) :=
  d.pairing.relabel (orderedLegToDiagramLeg S order)

/-- **Ordered Wick-diagram data**: a vertex-label sequence indexed by time slot `Fin n`, together
with a pairing of the resulting `4 * n` legs already stated in that same slot enumeration
(`orderedQuarticLegEquiv`'s enumeration, not `quarticLegEquiv`'s). -/
abbrev OrderedQuarticWickData (Mode : Type*) (n : ℕ) :=
  (Fin n → QuarticVertexLabel Mode) × Common.BlochDeDominicis.Pairing (2 * n)

/-- **The ordered-data equivalence**: for a *fixed* vertex set `S` and vertex order `order`, a
`QuarticWickDiagram Mode N S` is the same data as an `OrderedQuarticWickData Mode S.card` —
relabel the vertex-indexed data along `order`, and transport the pairing via
`orderedLegToDiagramLeg`. -/
noncomputable def quarticWickDiagramEquivOrderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) :
    QuarticWickDiagram Mode N S ≃ OrderedQuarticWickData Mode S.card where
  toFun d := (fun i => d.vertexLabel (order i), d.pairingInOrder order)
  invFun x :=
    { vertexLabel := fun v => x.1 (order.symm v)
      pairing := x.2.relabel (orderedLegToDiagramLeg S order).symm }
  left_inv d := by
    apply QuarticWickDiagram.ext
    · funext v
      simp
    · simp [QuarticWickDiagram.pairingInOrder]
  right_inv x := by
    obtain ⟨labels, pairing⟩ := x
    refine Prod.ext ?_ ?_
    · funext i
      simp
    · simp [QuarticWickDiagram.pairingInOrder]

/-- **PR 6's reindexing lemma**: summing an arbitrary function of the ordered data over all
diagrams on `S` (via `quarticWickDiagramEquivOrderedData`) is the same as summing it directly over
all ordered data — a direct instance of `Equiv.sum_comp`. -/
theorem sum_quarticWickDiagram_eq_sum_orderedData {S : Finset (Fin N)}
    (order : QuarticVertexOrder S) (F : OrderedQuarticWickData Mode S.card → ℂ) :
    ∑ d : QuarticWickDiagram Mode N S, F (quarticWickDiagramEquivOrderedData order d) =
      ∑ x : OrderedQuarticWickData Mode S.card, F x :=
  Equiv.sum_comp (quarticWickDiagramEquivOrderedData order) F

end SecondQuantization
