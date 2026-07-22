import LeanCondensedMatter.Combinatorics.MomentCumulant

set_option linter.style.header false

/-!
# Generic diagram connectedness, via the moment-cumulant relation

Step 6 of Phase 9's plan (`notes/roadmaps/second-quantization.md`): the abstract combinatorial
fact underlying "a cumulant only sees connected diagrams" — for *any* weighted family of diagrams
indexed by a finite vertex set `S`, that decomposes uniquely into a choice of connected-component
partition of `S` plus a connected diagram on each block (`WeightedDiagramFamily.decompose`), the
total (moment-level) sum of diagram weights equals `Finpartition.momentFromCumulant` applied to
the connected-diagram weight sum. Möbius-inverting
(`Finpartition.cumulantFromMoment_momentFromCumulant`, already proved in `MomentCumulant.lean`)
then recovers the connected-diagram sum directly from the cumulant of the moment, for any
nonempty vertex set.

This file is purely combinatorial — no `SecondQuantization` import, no physics, fully proved — and
does not construct any concrete diagram type itself; `Fermionic/`'s later files instantiate
`WeightedDiagramFamily` with genuine Wick pairing diagrams.

**What this file does not do.** It does not compute `WeightedDiagramFamily.diagramWeight`'s
factorization across components — that is a property of a *specific* diagram family
(`weight_decompose` already assumes it holds), not derived here. It also does not relate any of
this to `PowerSeries.log`'s coefficients, or to `CumulantFactorization.lean`'s cross-region
independence corollary (`IsIndependentAcross`) — both remain future work built on top of this
file.
-/

namespace Combinatorics

variable {α : Type*} [DecidableEq α]

/-- **A weighted family of diagrams on finite vertex sets**, decomposing uniquely into a
connected-component partition plus a connected diagram per block. `Diagram`/`ConnectedDiagram`
are arbitrary `Fintype`-valued families (the `fintypeDiagram`/`fintypeConnectedDiagram` fields
supply the instances, since a bare `structure` field cannot itself be registered as a typeclass
instance); `diagramWeight`/`connectedWeight` are `ℂ`-valued weight functions, related by
`weight_decompose`: an (arbitrary) diagram's weight is the product, over the blocks of its
component partition, of its restriction's connected weight. -/
structure WeightedDiagramFamily (α : Type*) [DecidableEq α] where
  /-- The type of diagrams on vertex set `S`. -/
  Diagram : Finset α → Type*
  /-- The type of *connected* diagrams on vertex set `S`. -/
  ConnectedDiagram : Finset α → Type*
  fintypeDiagram : ∀ S, Fintype (Diagram S)
  fintypeConnectedDiagram : ∀ S, Fintype (ConnectedDiagram S)
  /-- **Every diagram decomposes uniquely** into a connected-component partition of its vertex
  set, together with a connected diagram on each block. -/
  decompose : ∀ S : Finset α,
    Diagram S ≃ Σ π : Finpartition S, ∀ B : π.parts, ConnectedDiagram (B : Finset α)
  diagramWeight : ∀ {S : Finset α}, Diagram S → ℂ
  connectedWeight : ∀ {S : Finset α}, ConnectedDiagram S → ℂ
  /-- **A diagram's weight is the product of its connected components' weights.** -/
  weight_decompose : ∀ {S : Finset α} (d : Diagram S),
    diagramWeight d =
      ∏ B : (decompose S d).1.parts, connectedWeight ((decompose S d).2 B)

namespace WeightedDiagramFamily

variable (D : WeightedDiagramFamily α)

attribute [local instance] fintypeDiagram fintypeConnectedDiagram

/-- **The total (moment-level) sum of diagram weights** on vertex set `S`. -/
noncomputable def diagramMoment (S : Finset α) : ℂ :=
  ∑ d : D.Diagram S, D.diagramWeight d

/-- **The total sum of connected-diagram weights** on vertex set `S`. -/
noncomputable def connectedDiagramContribution (S : Finset α) : ℂ :=
  ∑ d : D.ConnectedDiagram S, D.connectedWeight d

/-- **The central decomposition theorem**: `diagramMoment` is exactly the moment-cumulant-style
sum, over every partition of `S`, of the product of `connectedDiagramContribution` over that
partition's blocks — i.e. `Finpartition.momentFromCumulant D.connectedDiagramContribution S`.
Proved by reindexing the diagram sum along `decompose` (`Equiv.sum_comp`), splitting the resulting
`Σ`-sum into a sum over partitions of a sum over connected-diagram choices per block
(`Fintype.sum_sigma`), and distributing that sum of products of independent per-block choices into
a product of per-block sums (`Finset.prod_univ_sum`), mirroring `MomentCumulant.lean`'s
`sum_Iic_partitionProduct_eq` proof pattern. -/
theorem diagramMoment_eq_momentFromCumulant (S : Finset α) :
    D.diagramMoment S =
      Finpartition.momentFromCumulant D.connectedDiagramContribution S := by
  classical
  have hreindex : D.diagramMoment S =
      ∑ x : Σ π : Finpartition S, ∀ B : π.parts, D.ConnectedDiagram (B : Finset α),
        ∏ B : x.1.parts, D.connectedWeight (x.2 B) := by
    rw [diagramMoment, ← Equiv.sum_comp (D.decompose S)
      (fun x : Σ π : Finpartition S, ∀ B : π.parts, D.ConnectedDiagram (B : Finset α) =>
        ∏ B : x.1.parts, D.connectedWeight (x.2 B))]
    exact Finset.sum_congr rfl fun d _ => D.weight_decompose d
  rw [hreindex, Fintype.sum_sigma, Finpartition.momentFromCumulant]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finpartition.partitionProduct, ← Finset.prod_coe_sort π.parts D.connectedDiagramContribution]
  have hdist := Finset.prod_univ_sum
    (fun B : π.parts => (Finset.univ : Finset (D.ConnectedDiagram (B : Finset α))))
    (fun B c => D.connectedWeight c)
  rw [Fintype.piFinset_univ] at hdist
  exact hdist.symm

/-- **The cumulant of a diagram family's moment is its connected-diagram contribution**, on any
nonempty vertex set — the abstract "a cumulant only sees connected diagrams" statement. Direct
consequence of `diagramMoment_eq_momentFromCumulant` and the already-proved
`Finpartition.cumulantFromMoment_momentFromCumulant`. -/
theorem cumulantFromMoment_diagramMoment {S : Finset α} (hS : S ≠ ∅) :
    Finpartition.cumulantFromMoment D.diagramMoment S = D.connectedDiagramContribution S := by
  have h := Finpartition.cumulantFromMoment_momentFromCumulant D.connectedDiagramContribution
    (S := S) hS
  have hfun : Finpartition.momentFromCumulant D.connectedDiagramContribution = D.diagramMoment :=
    funext fun T => (D.diagramMoment_eq_momentFromCumulant T).symm
  rwa [hfun] at h

end WeightedDiagramFamily

end Combinatorics
