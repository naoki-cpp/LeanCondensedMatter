import LeanCondensedMatter.SecondQuantization.Fermionic.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.DysonVertexMoment
import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.Amplitude

set_option linter.style.header false

/-!
# The Dyson-to-diagram expansion (PR 6)

Step 6 (PR 6) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`): the
final theorem this line of PRs has been building towards,

```
dysonVertexMoment ε β (quarticInteraction g) S =
  ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
```

**Status: in progress.** This file currently only bridges `normalizedDysonPartitionCoeff` (the
`Finset`-indexed moment's scalar content) to `freeGibbsExpectation ε β (dysonCoeff ε V n β)` — the
form the general Bloch–de Dominicis theorem
(`Common.BlochDeDominicis.gibbsExpectation_prodComp_eq_sum_pairing`) can actually be applied to,
once `V := quarticInteraction g` and `dysonCoeff`'s defining recursion are expanded into the
nested-integral/vertex-label-sum form the diagram sum needs. The remaining steps (expanding
`dysonCoeff`'s recursion into an `orderedSimplexIntegral` of a vertex-label sum, applying the
general theorem to the resulting `4n`-operator product, and reindexing via
`quarticWickDiagramEquivOrderedData`) are **not yet done** — see
`notes/roadmaps/second-quantization.md` for the full 9-step proof outline.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- **`normalizedDysonPartitionCoeff` is `freeGibbsExpectation` of the bare Dyson coefficient**:
`dysonPartitionCoeff ε β V n = Tr[e^{-βH₀} Dₙ(β)]` is exactly `Common.weightedTrace` of `Dₙ(β)`
against the free Boltzmann weight (`Common.traceFock_diagonalEvolution_comp_eq_weightedTrace`,
since `imaginaryTimeEvolveFree ε (-β)` unfolds to `Common.diagonalEvolution (fermionEnergy ε)
(-β)`), so dividing by `freePartitionFunction ε β = Common.weightSum (...)` gives
`Common.normalizedWeightedDiagonal`, i.e. `Common.gibbsExpectation (fermionEnergy ε) β`,
i.e. (via `freeGibbsExpectation_eq_gibbsExpectation`) `freeGibbsExpectation ε β`. This is the
bridge the general Bloch–de Dominicis theorem's own `Common.gibbsExpectation`-headed conclusion
needs to reach `dysonVertexMoment`. -/
theorem normalizedDysonPartitionCoeff_eq_freeGibbsExpectation (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ) :
    normalizedDysonPartitionCoeff ε β V n = freeGibbsExpectation ε β (dysonCoeff ε V n β) := by
  have hw : Common.boltzmannWeight (fermionEnergy ε) β = freeBoltzmannWeight ε β :=
    funext fun m => (freeBoltzmannWeight_eq_boltzmannWeight_fermionEnergy ε β m).symm
  rw [normalizedDysonPartitionCoeff, freeGibbsExpectation, normalizedWeightedDiagonal_eq_div]
  congr 1
  rw [dysonPartitionCoeff, imaginaryTimeEvolveFree]
  change Common.traceFock (Common.diagonalEvolution (fermionEnergy ε) (-β) ∘ₗ dysonCoeff ε V n β) =
    _
  rw [Common.traceFock_diagonalEvolution_comp_eq_weightedTrace, hw]
  rfl

omit [LinearOrder Mode] in
/-- **`dysonVertexMoment` is `S.card!` times `freeGibbsExpectation` of the bare Dyson coefficient
at order `S.card`** — folding `normalizedDysonPartitionCoeff_eq_freeGibbsExpectation` into
`dysonVertexMoment`'s own `S.card! * normalizedDysonPartitionCoeff ... S.card` definition. -/
theorem dysonVertexMoment_eq_freeGibbsExpectation {α : Type*} [DecidableEq α] (ε : Mode → ℝ)
    (β : ℝ) (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (S : Finset α) :
    dysonVertexMoment ε β V S =
      (S.card.factorial : ℂ) * freeGibbsExpectation ε β (dysonCoeff ε V S.card β) := by
  rw [dysonVertexMoment, normalizedDysonPartitionCoeff_eq_freeGibbsExpectation]

end SecondQuantization
