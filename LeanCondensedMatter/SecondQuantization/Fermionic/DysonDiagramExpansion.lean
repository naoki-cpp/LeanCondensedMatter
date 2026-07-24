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

**Status: in progress.** So far: `normalizedDysonPartitionCoeff`/`dysonVertexMoment` are bridged to
`freeGibbsExpectation ε β (dysonCoeff ε V n β)` — the form the general Bloch–de Dominicis theorem
(`Common.BlochDeDominicis.gibbsExpectation_prodComp_eq_sum_pairing`) can actually be applied to —
and `nestedVertexOperatorComp` (the `orderedSimplexIntegral` integrand's operator-valued
ingredient) is defined, with its recursive unfolding lemmas. Separately,
`continuous_matrixCoeff_interactionPicture_comp_dysonCoeff` supplies the matrix-coefficient
continuity needed to move the *current* Dyson recursion's integral through composition
(`Common.comp_operatorIntervalIntegral`) and `freeGibbsExpectation`
(`freeGibbsExpectation_operatorIntervalIntegral`) — it is **not** a continuity statement about
`nestedVertexOperatorComp` itself. The key induction expanding `dysonCoeff` of
`quarticInteraction` into an `orderedSimplexIntegral` of a vertex-label sum is stated but **not
yet proven** — see the `### The key induction (not yet proven)` section below for exactly what
remains and the joint continuity-in-bound fact for `orderedSimplexIntegral` it needs (likely
including continuity of `τ ↦ freeGibbsExpectation ε β (L.comp (nestedVertexOperatorComp ε n q
τ))` itself, or a parameterized version of it, as part of establishing that fact). Applying the
general theorem to the resulting `4n`-operator product and reindexing via
`quarticWickDiagramEquivOrderedData` are further steps beyond that — see
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

/-! ## Expanding `dysonCoeff` of `quarticInteraction` into a vertex-label sum -/

/-- **The nested interaction-picture vertex-operator composition**, `V_I(τ 0) ∘ V_I(τ 1) ∘ ⋯ ∘
V_I(τ (n-1))` for a fixed vertex-label sequence `q : Fin n → QuarticVertexLabel Mode` — the
operator-valued integrand `freeGibbsExpectation_comp_dysonCoeff_quarticInteraction`'s
`orderedSimplexIntegral` integrates. Coordinate `0` is the latest/outermost time, matching
`orderedSimplexIntegral`'s own convention. -/
noncomputable def nestedVertexOperatorComp (ε : Mode → ℝ) :
    (n : ℕ) → (Fin n → QuarticVertexLabel Mode) → (Fin n → ℝ) →
      FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode
  | 0, _, _ => LinearMap.id
  | _ + 1, q, τ =>
      (interactionPicture ε (quarticVertexOperator (q 0)) (τ 0)).comp
        (nestedVertexOperatorComp ε _ (fun i => q i.succ) (fun i => τ i.succ))

omit [Fintype Mode] in
@[simp]
theorem nestedVertexOperatorComp_zero (ε : Mode → ℝ) (q : Fin 0 → QuarticVertexLabel Mode)
    (τ : Fin 0 → ℝ) : nestedVertexOperatorComp ε 0 q τ = LinearMap.id := rfl

omit [Fintype Mode] in
theorem nestedVertexOperatorComp_succ (ε : Mode → ℝ) (n : ℕ)
    (q : Fin (n + 1) → QuarticVertexLabel Mode) (τ : Fin (n + 1) → ℝ) :
    nestedVertexOperatorComp ε (n + 1) q τ =
      (interactionPicture ε (quarticVertexOperator (q 0)) (τ 0)).comp
        (nestedVertexOperatorComp ε n (fun i => q i.succ) (fun i => τ i.succ)) := rfl

omit [LinearOrder Mode] in
/-- **Continuity in `σ`, at fixed `k n'`, of a matrix coefficient of `(interactionPicture ε V
σ).comp (dysonCoeff ε V n σ)`** — the finite sum of products of
`continuous_matrixCoeff_interactionPicture`/`continuous_matrixCoeff_dysonCoeff` (via
`Common.matrixCoeff_comp`), the integrability the inductive step's
`Common.comp_operatorIntervalIntegral`/`Common.normalizedWeightedDiagonal_operatorIntervalIntegral`
need. -/
theorem continuous_matrixCoeff_interactionPicture_comp_dysonCoeff (ε : Mode → ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (n : ℕ)
    (k n' : FermionOccupation Mode) :
    Continuous (fun σ : ℝ => Common.matrixCoeff
      ((interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) k n') := by
  simp_rw [Common.matrixCoeff_comp]
  exact continuous_finsetSum _ fun j _ =>
    (continuous_matrixCoeff_interactionPicture ε V k j).mul
      (continuous_matrixCoeff_dysonCoeff ε V n j n')

/-!
### The key induction (not yet proven)

The target statement is: for every `n`, `t`, and fixed prefix operator `L`,

```
freeGibbsExpectation ε β (L.comp (dysonCoeff ε (quarticInteraction g) n t)) =
  (-1 : ℂ) ^ n * ∑ q : Fin n → QuarticVertexLabel Mode,
    (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n t
      (fun τ => freeGibbsExpectation ε β (L.comp (nestedVertexOperatorComp ε n q τ)))
```

(the prefix `L` and the bound `t` both generalize the induction: the successor case absorbs the
newly-peeled-off outermost vertex factor into `L` before invoking the inductive hypothesis on the
remaining `n`-fold piece at bound `σ`, so the inner integral is exactly an instance of the same
statement, not a separate lemma). The `n = 0` base case is immediate
(`dysonCoeff_zero`/`LinearMap.comp_id`/`Fintype.sum_unique` on the singleton `Fin 0 →
QuarticVertexLabel Mode`).

**The successor case needs one more piece of analysis not yet available**: after peeling the
outermost vertex factor off via `dysonCoeff_succ`/`Common.comp_operatorIntervalIntegral`/
`freeGibbsExpectation_operatorIntervalIntegral` and expanding `quarticInteraction`'s `Finset.sum`
via `interactionPicture_quarticInteraction`/`freeGibbsExpectation_finsetSum`, the inductive
hypothesis produces, for each outer vertex label `q0` and each integration variable `σ`, an
`orderedSimplexIntegral n σ (…)` term whose *bound* `σ` is itself the outer `∫ σ in 0..t`'s
integration variable. Reindexing the resulting double sum (over `q0` and the inner label sequence
`q'`) into a single sum over `Fin (n + 1) → QuarticVertexLabel Mode` (via `Fin.consEquiv`) and
folding the result back into `orderedSimplexIntegral (n + 1) t` (via `orderedSimplexIntegral_succ`)
requires swapping the finite `q`-sum with the outer `∫ σ in 0..t`, which needs continuity of `σ ↦
orderedSimplexIntegral n σ (fun τ' => freeGibbsExpectation ε β (…))` **in the bound `σ` itself** —
not just in the integrand for a *fixed* bound, which is all `Analysis/OrderedSimplexIntegral.lean`
and `WickDiagram/Amplitude.lean`'s existing continuity lemmas establish. This joint
continuity-in-bound fact for `orderedSimplexIntegral` (an integrand that itself varies
continuously with the outer bound, iterated `n` times) is genuinely new infrastructure, not yet
added anywhere in this project — planned as the next installment.
-/

end SecondQuantization
