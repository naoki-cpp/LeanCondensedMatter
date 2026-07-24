import LeanCondensedMatter.SecondQuantization.Fermionic.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.DysonVertexMoment
import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.Amplitude
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirst
import LeanCondensedMatter.SecondQuantization.Fermionic.ExchangeAlgebra

set_option linter.style.header false

/-!
# The Dyson-to-diagram expansion (PR 6)

Step 6 (PR 6) of the diagram-connectedness plan (`notes/roadmaps/second-quantization.md`): the
final theorem this line of PRs has been building towards,

```
dysonVertexMoment ε β (quarticInteraction g) S =
  ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
```

**Status: in progress.** `normalizedDysonPartitionCoeff`/`dysonVertexMoment` are bridged to
`freeGibbsExpectation ε β (dysonCoeff ε V n β)` — the form the general Bloch–de Dominicis theorem
(`Common.BlochDeDominicis.gibbsExpectation_prodComp_eq_sum_pairing`) can actually be applied to.
`nestedVertexOperatorComp` (the `orderedSimplexIntegral` integrand's operator-valued ingredient)
is defined, with its recursive unfolding lemmas, and its own joint continuity in the full time
vector is established (`continuous_matrixCoeff_nestedVertexOperatorComp`/
`continuous_freeGibbsExpectation_comp_nestedVertexOperatorComp`).
`freeGibbsExpectation_comp_dysonCoeff_quarticInteraction` — the key induction expanding
`dysonCoeff` of `quarticInteraction`, left-composed with an arbitrary prefix operator, into a
`(-1)ⁿ`-signed sum over vertex-label sequences of an `orderedSimplexIntegral` of
`nestedVertexOperatorComp` values — is now **fully proven**, using
`Analysis/OrderedSimplexIntegral.lean`'s `continuous_orderedSimplexIntegral_of_continuous` (the
joint continuity-in-bound fact discovered missing while first attempting this induction) to swap
the finite vertex-label sum out past the outer `∫ σ in 0..t`, and a locally-defined
`QuarticVertexLabel Mode × (Fin n → QuarticVertexLabel Mode) ≃ (Fin (n + 1) → QuarticVertexLabel
Mode)` equivalence (`Fin.cons`-based) to reindex the resulting (outer label, inner label sequence)
double sum into a single `Fin (n + 1) → QuarticVertexLabel Mode` sum.

`nestedVertexOperatorComp` is further **fully flattened** into a `Common.prodComp` of its `4n`
atomic (single-mode creation/annihilation) legs
(`prodComp_ofFn_flatVertexLegOperator_eq_nestedVertexOperatorComp`), via
`orderedQuarticLegEquiv_cast_mul_add`/`flatVertexLegOperator_cast_mul_add` (the index-arithmetic
bridge tying `orderedQuarticLegEquiv`'s multiplicative domain identification to
`List.ofFn_fin_append`'s additive one) and `eq_cast_mul_add_orderedQuarticLegEquiv` (expressing an
*arbitrary* flattened position in `i * 4 + j` form, needed to match the induction's "tail" piece
at an unconstrained position, not just the specific ones the bridge lemma constructs) — combined
with `Common.prodComp_append` and `interactionPicture_quarticVertexOperator_eq_prodComp`. This is
the last purely combinatorial/index-bookkeeping step before the genuine physics content
(discharging the general theorem's eigenoperator/zeta-commutator hypotheses) is needed.

The general Bloch–de Dominicis theorem's **first hypothesis is now discharged for all `4n`
flattened legs**: `heisenbergEvolve_flatVertexLegOperator` shows every atomic leg operator
`flatVertexLegOperator` produces is an eigenoperator of `heisenbergEvolve (fermionEnergy ε) (-β)`
(the free-evolution eigenvalue shift is *independent of the dressing time* `τ` each leg carries —
`Common.heisenbergEvolve_heisenbergEvolve`, new in `Common/DiagonalEvolution.lean`, supplies the
needed one-parameter-semigroup commutativity).

The general theorem's **second hypothesis is now discharged for a single vertex's four legs**:
`zetaCommutator_quarticLocalLegOperator` (via `anticomm_quarticLocalLegOperator`, a single closed
formula covering same-vertex and cross-vertex leg pairs alike — `0` for two legs of the same kind
(CAR's `anticomm_create_create`/`anticomm_annihilate_annihilate`, always `0` even at the same
mode), `δ` on the two legs' modes otherwise (CAR's `anticomm_annihilate_create`/the new
`anticomm_create_annihilate`)). This is the *bare* (untime-evolved) commutator constant; the
general theorem's actual `c i j` hypothesis (for the evolved `flatVertexLegOperator` legs, at
fixed `τ`) still needs the corresponding `Complex.exp` eigenvalue-shift factors multiplied in, and
assembling the two-vertex/two-local-leg case analysis (via `orderedQuarticLegEquiv`) into a single
`c : Fin (2 * (2 * n)) → Fin (2 * (2 * n)) → ℂ` is not yet done.

**Still remaining**: finishing the second hypothesis for the evolved, flattened `4n`-leg family
(exponential factors plus the `orderedQuarticLegEquiv`-based two-position case analysis), the
*third* hypothesis (non-resonance, expected free for real eigenvalue shifts since `ζ = -1`), then
actually applying `Common.BlochDeDominicis.gibbsExpectation_prodComp_eq_sum_pairing` to the
resulting `4n`-operator product (`freeGibbsExpectation_comp_dysonCoeff_quarticInteraction` at `L
:= LinearMap.id`, `t := β`, composed with the flattening theorem, gives the vertex-label-sum side)
and reindexing the resulting (vertex-label sequence, pairing) sum via
`quarticWickDiagramEquivOrderedData` into a genuine sum over `QuarticWickDiagram`s — see
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

set_option linter.unusedFintypeInType false in
/-- **Joint continuity, in the full time vector `τ`, of a matrix coefficient of
`nestedVertexOperatorComp`** — by induction on `n`: the base case is constant (`nested...Comp ε 0
q τ = LinearMap.id`); the successor case's matrix coefficient is a finite sum of products of a
single-coordinate `Complex.exp` factor (`continuous_matrixCoeff_interactionPicture`, precomposed
with the coordinate-`0` projection) and the inductive hypothesis (precomposed with the "tail"
projection `fun i => τ i.succ`). `[Fintype Mode]` is genuinely used (for the finite sum
`Common.matrixCoeff_comp` needs), just not in the statement itself — the linter can't see that. -/
theorem continuous_matrixCoeff_nestedVertexOperatorComp (ε : Mode → ℝ) :
    ∀ (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (k n' : FermionOccupation Mode),
      Continuous (fun τ : Fin n → ℝ => Common.matrixCoeff (nestedVertexOperatorComp ε n q τ) k n')
  | 0, _, _, _ => continuous_const
  | n + 1, q, k, n' => by
    have heq : ∀ τ : Fin (n + 1) → ℝ, Common.matrixCoeff
        (nestedVertexOperatorComp ε (n + 1) q τ) k n' =
          ∑ j : FermionOccupation Mode, Common.matrixCoeff
            (interactionPicture ε (quarticVertexOperator (q 0)) (τ 0)) k j *
            Common.matrixCoeff
              (nestedVertexOperatorComp ε n (fun i => q i.succ) (fun i => τ i.succ)) j n' :=
      fun τ => by rw [nestedVertexOperatorComp_succ, Common.matrixCoeff_comp]
    simp_rw [heq]
    exact continuous_finsetSum _ fun j _ =>
      ((continuous_matrixCoeff_interactionPicture ε (quarticVertexOperator (q 0)) k j).comp
          (continuous_apply 0)).mul
        ((continuous_matrixCoeff_nestedVertexOperatorComp ε n (fun i => q i.succ) j n').comp
          (continuous_pi fun i => continuous_apply i.succ))

/-- **Joint continuity, in the full time vector `τ`, of `freeGibbsExpectation` of an
`L`-prefixed `nestedVertexOperatorComp`** — unfolds `freeGibbsExpectation` to its defining
`weightedTrace`/`weightSum` quotient (a `τ`-independent divisor, so `Continuous.div_const`
applies) and each diagonal matrix coefficient of `L.comp (nestedVertexOperatorComp ε n q τ)` to
`Common.matrixCoeff_comp`'s finite sum, closed by `continuous_matrixCoeff_nestedVertexOperatorComp`
— the joint continuity `continuous_orderedSimplexIntegral_of_continuous` needs to apply to the key
induction's successor-case integrand below. -/
theorem continuous_freeGibbsExpectation_comp_nestedVertexOperatorComp (ε : Mode → ℝ) (β : ℝ)
    (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (L : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    Continuous (fun τ : Fin n → ℝ =>
      freeGibbsExpectation ε β (L.comp (nestedVertexOperatorComp ε n q τ))) := by
  have heq : ∀ τ : Fin n → ℝ, freeGibbsExpectation ε β (L.comp (nestedVertexOperatorComp ε n q τ))
      = (∑ k' : FermionOccupation Mode, freeBoltzmannWeight ε β k' *
          ∑ j : FermionOccupation Mode, Common.matrixCoeff L k' j *
            Common.matrixCoeff (nestedVertexOperatorComp ε n q τ) j k') /
        freePartitionFunction ε β := fun τ => by
    change Common.normalizedWeightedDiagonal (freeBoltzmannWeight ε β)
      (L.comp (nestedVertexOperatorComp ε n q τ)) = _
    rw [Common.normalizedWeightedDiagonal, Common.weightedTrace]
    refine congrArg (· / _) (Finset.sum_congr rfl fun k' _ => ?_)
    rw [Common.matrixCoeff_comp]
  simp_rw [heq]
  refine Continuous.div_const ?_ _
  exact continuous_finsetSum _ fun k' _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => continuous_const.mul
      (continuous_matrixCoeff_nestedVertexOperatorComp ε n q j k'))

omit [Fintype Mode] in
/-- **`nestedVertexOperatorComp` at `n + 1`, on `Fin.cons`-assembled label/time data**: unfolds
`nestedVertexOperatorComp_succ` and simplifies the resulting `(Fin.cons q0 q') 0`/`(Fin.cons σ
τ') 0`/tail expressions via `Fin.cons_zero`/`Fin.cons_succ`. The form the key induction's
successor case needs to fold a peeled-off outermost vertex factor back into a single
`nestedVertexOperatorComp` term. -/
theorem nestedVertexOperatorComp_cons (ε : Mode → ℝ) (n : ℕ) (q0 : QuarticVertexLabel Mode)
    (q' : Fin n → QuarticVertexLabel Mode) (σ : ℝ) (τ' : Fin n → ℝ) :
    nestedVertexOperatorComp ε (n + 1) (Fin.cons q0 q') (Fin.cons σ τ') =
      (interactionPicture ε (quarticVertexOperator q0) σ).comp
        (nestedVertexOperatorComp ε n q' τ') := by
  rw [nestedVertexOperatorComp_succ]
  simp

/-- **The key induction: `dysonCoeff` of `quarticInteraction`, left-composed with an arbitrary
fixed prefix operator `L`, expands into a `(-1)ⁿ`-signed sum over vertex-label sequences of an
`orderedSimplexIntegral` of `L`-prefixed `nestedVertexOperatorComp` values.** The prefix `L`
generalizes the induction so the successor case can absorb the newly-peeled-off outermost vertex
factor into `L` before invoking the inductive hypothesis on the remaining `n`-fold piece; the
bound `t` likewise generalizes so the inductive step's inner integral (over `[0, σ]` for the
recursion's own integration variable `σ`) is exactly an instance of the same statement, rather
than requiring a separate lemma for non-`β` bounds. -/
theorem freeGibbsExpectation_comp_dysonCoeff_quarticInteraction (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) :
    ∀ (n : ℕ) (t : ℝ) (L : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode),
      freeGibbsExpectation ε β (L.comp (dysonCoeff ε (quarticInteraction g) n t)) =
        (-1 : ℂ) ^ n * ∑ q : Fin n → QuarticVertexLabel Mode,
          (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n t
            (fun τ => freeGibbsExpectation ε β (L.comp (nestedVertexOperatorComp ε n q τ))) := by
  intro n
  induction n with
  | zero =>
    intro t L
    have huniq : Unique (Fin 0 → QuarticVertexLabel Mode) := Pi.uniqueOfIsEmpty _
    rw [dysonCoeff_zero, LinearMap.comp_id, Fintype.sum_unique]
    simp
  | succ n ih =>
    intro t L
    set V := quarticInteraction g with hV
    -- Step 1: peel the outermost vertex factor off, pushing `L` and `freeGibbsExpectation`
    -- through `operatorIntervalIntegral`.
    have hcont : ∀ k n' : FermionOccupation Mode,
        IntervalIntegrable (fun σ => Common.matrixCoeff
          ((interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) k n') MeasureTheory.volume 0 t :=
      fun k n' =>
        (continuous_matrixCoeff_interactionPicture_comp_dysonCoeff ε V n k n').intervalIntegrable
          0 t
    rw [dysonCoeff_succ, LinearMap.comp_neg,
      Common.comp_operatorIntervalIntegral _ _ _ _ hcont, freeGibbsExpectation_neg]
    have hcont2 : ∀ n' : FermionOccupation Mode,
        IntervalIntegrable (fun σ => Common.matrixCoeff
          (L.comp ((interactionPicture ε V σ).comp (dysonCoeff ε V n σ))) n' n')
          MeasureTheory.volume 0 t := by
      intro n'
      have heq : ∀ σ : ℝ, Common.matrixCoeff
          (L.comp ((interactionPicture ε V σ).comp (dysonCoeff ε V n σ))) n' n' =
          ∑ j : FermionOccupation Mode, Common.matrixCoeff L n' j *
            Common.matrixCoeff ((interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) j n' :=
        fun σ => Common.matrixCoeff_comp L _ n' n'
      have hc : Continuous (fun σ => Common.matrixCoeff
          (L.comp ((interactionPicture ε V σ).comp (dysonCoeff ε V n σ))) n' n') := by
        simp_rw [heq]
        exact continuous_finsetSum _ fun j _ => continuous_const.mul
          (continuous_matrixCoeff_interactionPicture_comp_dysonCoeff ε V n j n')
      exact hc.intervalIntegrable 0 t
    rw [freeGibbsExpectation_operatorIntervalIntegral ε β _ 0 t hcont2]
    -- Step 2: expand `V := quarticInteraction g`, apply the inductive hypothesis to each vertex
    -- term, and reindex the resulting (outer label, inner label sequence) double sum into a
    -- single `Fin (n + 1) → QuarticVertexLabel Mode` sum via `Fin.consEquiv`.
    have hpoint : ∀ σ : ℝ, freeGibbsExpectation ε β
        (L.comp ((interactionPicture ε V σ).comp (dysonCoeff ε V n σ))) =
        (-1 : ℂ) ^ n * ∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
          (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n σ
            (fun τ' => freeGibbsExpectation ε β
              (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ')))) := by
      intro σ
      have e2 : L.comp ((interactionPicture ε V σ).comp (dysonCoeff ε V n σ)) =
          ∑ q0 : QuarticVertexLabel Mode,
            g q0 • ((L.comp (interactionPicture ε (quarticVertexOperator q0) σ)).comp
              (dysonCoeff ε V n σ)) := by
        rw [hV, interactionPicture_quarticInteraction]
        ext x
        simp [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.comp_assoc]
      rw [e2, freeGibbsExpectation_finsetSum]
      have hstep : ∀ q0 : QuarticVertexLabel Mode, freeGibbsExpectation ε β
          (g q0 • ((L.comp (interactionPicture ε (quarticVertexOperator q0) σ)).comp
            (dysonCoeff ε V n σ))) =
          (-1 : ℂ) ^ n * ∑ q' : Fin n → QuarticVertexLabel Mode,
            g q0 * (∏ i, g (q' i)) * intervalIntegral.orderedSimplexIntegral n σ
              (fun τ' => freeGibbsExpectation ε β
                (L.comp (nestedVertexOperatorComp ε (n + 1) (Fin.cons q0 q')
                  (Fin.cons σ τ')))) := by
        intro q0
        rw [freeGibbsExpectation_smul,
          ih σ (L.comp (interactionPicture ε (quarticVertexOperator q0) σ)), mul_left_comm,
          Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun q' _ => ?_
        rw [← mul_assoc]
        congr 1
      simp_rw [hstep]
      rw [← Finset.mul_sum]
      congr 1
      rw [← Fintype.sum_prod_type']
      let e : QuarticVertexLabel Mode × (Fin n → QuarticVertexLabel Mode) ≃
          (Fin (n + 1) → QuarticVertexLabel Mode) :=
        { toFun := fun p => Fin.cons p.1 p.2
          invFun := fun q => (q 0, fun i => q i.succ)
          left_inv := fun p => by simp
          right_inv := fun q => by funext i; refine Fin.cases ?_ ?_ i <;> simp }
      rw [← Equiv.sum_comp e (fun q : Fin (n + 1) → QuarticVertexLabel Mode => (∏ i, g (q i)) *
          intervalIntegral.orderedSimplexIntegral n σ
            (fun τ' => freeGibbsExpectation ε β
              (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ')))))]
      refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨q0, q'⟩ := p
      change (g q0 * ∏ i, g (q' i)) *
          intervalIntegral.orderedSimplexIntegral n σ
            (fun τ' => freeGibbsExpectation ε β
              (L.comp (nestedVertexOperatorComp ε (n + 1) (Fin.cons q0 q') (Fin.cons σ τ')))) =
        (∏ i, g (e (q0, q') i)) *
          intervalIntegral.orderedSimplexIntegral n σ
            (fun τ' => freeGibbsExpectation ε β
              (L.comp (nestedVertexOperatorComp ε (n + 1) (e (q0, q')) (Fin.cons σ τ'))))
      congr 1
      rw [Fin.prod_univ_succ]
      rfl
    -- Step 3: put `hpoint` into the outer `∫ σ in 0..t`, swap the finite label sum out (via the
    -- new `orderedSimplexIntegral` joint continuity-in-bound fact), and fold the result back into
    -- `orderedSimplexIntegral (n + 1) t` via `orderedSimplexIntegral_succ`.
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const_mul]
    have hintegrability : ∀ q : Fin (n + 1) → QuarticVertexLabel Mode,
        IntervalIntegrable (fun σ => (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n σ
          (fun τ' => freeGibbsExpectation ε β
            (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ')))))
          MeasureTheory.volume 0 t := by
      intro q
      have hcontF : Continuous (Function.uncurry
          (fun (σ : ℝ) (τ' : Fin n → ℝ) => freeGibbsExpectation ε β
            (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ'))))) :=
        (continuous_freeGibbsExpectation_comp_nestedVertexOperatorComp ε β (n + 1) q L).comp
          (Continuous.finCons continuous_fst continuous_snd)
      have hcont := intervalIntegral.continuous_orderedSimplexIntegral_of_continuous n
        (id : ℝ → ℝ) _ continuous_id hcontF
      exact (continuous_const.mul hcont).intervalIntegrable 0 t
    rw [intervalIntegral.integral_finsetSum (fun q _ => hintegrability q)]
    have hsum_eq : ∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
        ∫ σ in (0 : ℝ)..t, (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n σ
          (fun τ' => freeGibbsExpectation ε β
            (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ')))) =
        ∑ q : Fin (n + 1) → QuarticVertexLabel Mode, (∏ i, g (q i)) *
          intervalIntegral.orderedSimplexIntegral (n + 1) t
            (fun τ => freeGibbsExpectation ε β (L.comp (nestedVertexOperatorComp ε (n + 1) q τ)))
        := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [intervalIntegral.integral_const_mul]
      congr 1
    rw [hsum_eq]
    ring

/-! ## Flattening `nestedVertexOperatorComp` into a `4n`-atom `Common.prodComp` -/

omit [LinearOrder Mode] [Fintype Mode] in
/-- **`imaginaryTimeEvolve` distributes over composition** — directly
`Common.heisenbergEvolve_comp` at `energy := fermionEnergy ε`. Needed to unfold
`quarticVertexOperator`'s evolution atom-by-atom. -/
theorem imaginaryTimeEvolve_comp (ε : Mode → ℝ) (τ : ℝ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    imaginaryTimeEvolve ε τ (A.comp B) =
      (imaginaryTimeEvolve ε τ A).comp (imaginaryTimeEvolve ε τ B) :=
  Common.heisenbergEvolve_comp (fermionEnergy ε) τ A B

omit [Fintype Mode] in
/-- **A single vertex's evolved operator, flattened into a `Common.prodComp` of its four
individually-evolved atomic legs**: unfolds `quarticVertexOperator`'s own definition
(`c₁† c₂† a₂ a₁`) via `imaginaryTimeEvolve_comp`, three times, matching
`quarticLocalLegOperator`'s `0 ↦ create₁, 1 ↦ create₂, 2 ↦ annihilate₂, 3 ↦ annihilate₁`
convention exactly. -/
theorem interactionPicture_quarticVertexOperator_eq_prodComp (ε : Mode → ℝ)
    (q : QuarticVertexLabel Mode) (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      Common.prodComp
        (List.ofFn (fun l : Fin 4 => imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l))) := by
  change imaginaryTimeEvolve ε τ (quarticVertexOperator q) = _
  rw [quarticVertexOperator, imaginaryTimeEvolve_comp, imaginaryTimeEvolve_comp,
    imaginaryTimeEvolve_comp]
  simp [Common.prodComp, quarticLocalLegOperator, List.ofFn_succ]

/-- **`orderedQuarticLegEquiv`'s value at the flattened position `i * 4 + j`** (up to the numeric
cast identifying `Fin (2 * (2 * n))` with `Fin (n * 4)`) **is exactly `(i, j)`** — the fact tying
`orderedQuarticLegEquiv`'s underlying `finProdFinEquiv` to `List.ofFn_mul`'s own `i * n + j` block
indexing. Proved via `Equiv.symm_apply_eq`, reducing to the numeric identity `i * 4 + j = j + 4 *
i` `finProdFinEquiv`'s defining formula gives — avoiding any need for a named `finProdFinEquiv`
"symm" simp lemma. -/
theorem orderedQuarticLegEquiv_cast_mul_add {n : ℕ} (i : Fin n) (j : Fin 4)
    (h : 2 * (2 * n) = n * 4) :
    orderedQuarticLegEquiv n (Fin.cast h.symm ⟨(i : ℕ) * 4 + (j : ℕ), by omega⟩) = (i, j) := by
  simp only [orderedQuarticLegEquiv, Equiv.trans_apply, finCongr_apply, Fin.cast_cast,
    Fin.cast_eq_self]
  rw [Equiv.symm_apply_eq]
  apply Fin.ext
  simp only [finProdFinEquiv, Equiv.coe_fn_mk]
  ring

omit [Fintype Mode] in
/-- **The atomic operator at a flattened leg position, for a bare vertex-label sequence `q` (not
yet a `QuarticWickDiagram`)** — the same construction as `orderedQuarticLegOperator`, generalized
off a fixed diagram/order pair so the flattening lemma below can be stated for an arbitrary
`q : Fin n → QuarticVertexLabel Mode`. -/
noncomputable def flatVertexLegOperator (ε : Mode → ℝ) (n : ℕ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  imaginaryTimeEvolve ε (τ (orderedQuarticLegEquiv n p).1)
    (quarticLocalLegOperator (q (orderedQuarticLegEquiv n p).1) (orderedQuarticLegEquiv n p).2)

omit [Fintype Mode] in
theorem flatVertexLegOperator_cast_mul_add {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (i : Fin n) (j : Fin 4)
    (h : 2 * (2 * n) = n * 4) :
    flatVertexLegOperator ε n q τ (Fin.cast h.symm ⟨(i : ℕ) * 4 + (j : ℕ), by omega⟩) =
      imaginaryTimeEvolve ε (τ i) (quarticLocalLegOperator (q i) j) := by
  rw [flatVertexLegOperator, orderedQuarticLegEquiv_cast_mul_add i j h]

set_option linter.unusedFintypeInType false in
/-- **A single evolved atomic leg operator is an eigenoperator of `heisenbergEvolve (fermionEnergy
ε) (-β)`, with an eigenvalue shift *independent of the dressing time* `τ`** — the fact the general
Bloch–de Dominicis theorem's own eigenoperator hypothesis needs, for each of the `4n` legs
`flatVertexLegOperator` produces. Proved via `Common.heisenbergEvolve_heisenbergEvolve` (the two
evolutions, at `τ` and `-β`, combine into a single evolution at `τ + (-β)`) and
`imaginaryTimeEvolve_quarticLocalLegOperator` (applied twice: once at `τ + (-β)` to evaluate the
combined evolution, once at `τ` in reverse to factor the `τ`-dependent piece back out) — the two
resulting `Complex.exp`s combine via `exp_add`/`ring`, leaving only the `-β`-dependent factor. -/
theorem heisenbergEvolve_imaginaryTimeEvolve_quarticLocalLegOperator (ε : Mode → ℝ) (β : ℝ)
    (q : QuarticVertexLabel Mode) (l : Fin 4) (τ : ℝ) :
    Common.heisenbergEvolve (fermionEnergy ε) (-β)
        (imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l)) =
      Complex.exp (((quarticLocalLegEnergyShift ε q l * (-β) : ℝ)) : ℂ) •
        imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l) := by
  have step : Common.heisenbergEvolve (fermionEnergy ε) (-β)
      (imaginaryTimeEvolve ε τ (quarticLocalLegOperator q l)) =
      imaginaryTimeEvolve ε (τ + -β) (quarticLocalLegOperator q l) :=
    Common.heisenbergEvolve_heisenbergEvolve (fermionEnergy ε) τ (-β)
      (quarticLocalLegOperator q l)
  rw [step, imaginaryTimeEvolve_quarticLocalLegOperator,
    imaginaryTimeEvolve_quarticLocalLegOperator, smul_smul, ← Complex.exp_add]
  congr 2
  push_cast
  ring

set_option linter.unusedFintypeInType false in
/-- **Every atomic leg operator `flatVertexLegOperator` produces is an eigenoperator of
`heisenbergEvolve (fermionEnergy ε) (-β)`** — direct specialization of
`heisenbergEvolve_imaginaryTimeEvolve_quarticLocalLegOperator` to the flattened position `p`'s own
vertex label and time assignment. -/
theorem heisenbergEvolve_flatVertexLegOperator {n : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p : Fin (2 * (2 * n))) :
    Common.heisenbergEvolve (fermionEnergy ε) (-β) (flatVertexLegOperator ε n q τ p) =
      Complex.exp
          ((quarticLocalLegEnergyShift ε (q (orderedQuarticLegEquiv n p).1)
            (orderedQuarticLegEquiv n p).2 * (-β) : ℝ) : ℂ) •
        flatVertexLegOperator ε n q τ p :=
  heisenbergEvolve_imaginaryTimeEvolve_quarticLocalLegOperator ε β
    (q (orderedQuarticLegEquiv n p).1) (orderedQuarticLegEquiv n p).2
    (τ (orderedQuarticLegEquiv n p).1)

/-- **Every flattened position is of the `i * 4 + j` form** — the converse of
`orderedQuarticLegEquiv_cast_mul_add`: applying `(orderedQuarticLegEquiv n).symm` to both sides of
`orderedQuarticLegEquiv_cast_mul_add` and using `Equiv.symm_apply_apply` on the resulting
`(orderedQuarticLegEquiv n).symm (orderedQuarticLegEquiv n p) = p`. Lets the flattening theorem
match an *arbitrary* flattened position `p`, not just the specific ones the block-splitting lemma
above constructs. -/
theorem eq_cast_mul_add_orderedQuarticLegEquiv {n : ℕ} (p : Fin (2 * (2 * n)))
    (h : 2 * (2 * n) = n * 4) :
    p = Fin.cast h.symm ⟨(orderedQuarticLegEquiv n p).1 * 4 + (orderedQuarticLegEquiv n p).2, by
      have := (orderedQuarticLegEquiv n p).2.isLt; omega⟩ := by
  have heq := orderedQuarticLegEquiv_cast_mul_add (orderedQuarticLegEquiv n p).1
    (orderedQuarticLegEquiv n p).2 h
  rw [Prod.mk.eta] at heq
  exact ((orderedQuarticLegEquiv n).injective heq).symm

omit [Fintype Mode] in
/-- **`nestedVertexOperatorComp`, flattened into a `Common.prodComp` of its `4n` atomic legs** —
by induction on `n`: the base case is trivial (`Fin (2 * (2 * 0))` is empty); the successor case
reduces, via `nestedVertexOperatorComp_succ`,
`interactionPicture_quarticVertexOperator_eq_prodComp`, the inductive hypothesis, and
`Common.prodComp_append`, to the *pure list* equality `List.ofFn (flatVertexLegOperator ε (n + 1)
q τ) = List.ofFn (4 atoms for vertex 0) ++ List.ofFn (flatVertexLegOperator ε n (tail q) (tail
τ))`, proved via `List.ofFn_fin_append`/`Fin.addCases` splitting the domain additively into `4 + 2
* (2 * n)`: the `left` branch matches `flatVertexLegOperator_cast_mul_add` at vertex `0` directly;
the `right` branch uses `eq_cast_mul_add_orderedQuarticLegEquiv` to express an *arbitrary*
position `k` of the smaller `n`-fold piece in `i' * 4 + j'` form, then matches both sides via
`flatVertexLegOperator_cast_mul_add` (at `n` for the RHS, at `n + 1` and vertex `i'.succ` for the
LHS) — the two positions agree because `4 + (i' * 4 + j') = i'.succ * 4 + j'` as naturals. -/
theorem prodComp_ofFn_flatVertexLegOperator_eq_nestedVertexOperatorComp (ε : Mode → ℝ) :
    ∀ (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ),
      Common.prodComp (List.ofFn (flatVertexLegOperator ε n q τ)) =
        nestedVertexOperatorComp ε n q τ
  | 0, q, τ => by
    have h0 : 2 * (2 * 0) = 0 := by ring
    have : IsEmpty (Fin (2 * (2 * 0))) := h0 ▸ Fin.isEmpty
    simp [List.ofFn]
  | n + 1, q, τ => by
    have hcard : 2 * (2 * (n + 1)) = (n + 1) * 4 := by ring
    have hcard' : 2 * (2 * n) = n * 4 := by ring
    have h2 : 2 * (2 * (n + 1)) = 4 + 2 * (2 * n) := by ring
    rw [nestedVertexOperatorComp_succ, interactionPicture_quarticVertexOperator_eq_prodComp,
      ← prodComp_ofFn_flatVertexLegOperator_eq_nestedVertexOperatorComp ε n (fun i => q i.succ)
        (fun i => τ i.succ),
      ← Common.prodComp_append, List.ofFn_congr h2, ← List.ofFn_fin_append]
    refine congrArg Common.prodComp
      (congrArg List.ofFn (funext (Fin.addCases (fun j => ?_) fun k => ?_)))
    · have e1 : Fin.cast h2.symm (Fin.castAdd (2 * (2 * n)) j) =
          Fin.cast hcard.symm ⟨((0 : Fin (n + 1)) : ℕ) * 4 + (j : ℕ), by omega⟩ := by
        apply Fin.ext; simp
      change flatVertexLegOperator ε (n + 1) q τ (Fin.cast h2.symm (Fin.castAdd _ j)) =
        Fin.append (fun j : Fin 4 => imaginaryTimeEvolve ε (τ 0) (quarticLocalLegOperator (q 0) j))
          (flatVertexLegOperator ε n (fun i => q i.succ) (fun i => τ i.succ)) (Fin.castAdd _ j)
      rw [Fin.append_left, e1, flatVertexLegOperator_cast_mul_add ε q τ 0 j hcard]
    · have hk := eq_cast_mul_add_orderedQuarticLegEquiv k hcard'
      have e2 : Fin.cast h2.symm (Fin.natAdd 4 k) = Fin.cast hcard.symm
          ⟨((orderedQuarticLegEquiv n k).1.succ : ℕ) * 4 + ((orderedQuarticLegEquiv n k).2 : ℕ),
            by have := (orderedQuarticLegEquiv n k).2.isLt; omega⟩ := by
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
        have hkval : (k : ℕ) =
            (orderedQuarticLegEquiv n k).1 * 4 + (orderedQuarticLegEquiv n k).2 := by
          have := congrArg Fin.val hk
          simpa using this
        omega
      change flatVertexLegOperator ε (n + 1) q τ (Fin.cast h2.symm (Fin.natAdd 4 k)) =
        Fin.append (fun j : Fin 4 => imaginaryTimeEvolve ε (τ 0) (quarticLocalLegOperator (q 0) j))
          (flatVertexLegOperator ε n (fun i => q i.succ) (fun i => τ i.succ)) (Fin.natAdd 4 k)
      rw [Fin.append_right, e2,
        flatVertexLegOperator_cast_mul_add ε q τ (orderedQuarticLegEquiv n k).1.succ
          (orderedQuarticLegEquiv n k).2 hcard]
      have hrest := flatVertexLegOperator_cast_mul_add ε (fun i => q i.succ) (fun i => τ i.succ)
        (orderedQuarticLegEquiv n k).1 (orderedQuarticLegEquiv n k).2 hcard'
      rw [← hk] at hrest
      exact hrest.symm

/-! ## The general theorem's zeta-commutator hypothesis, for a single vertex's four legs -/

omit [Fintype Mode] in
/-- **The mode a local leg's ladder operator acts on** — companion to `quarticLocalLegOperator`'s
own `0 ↦ create₁, 1 ↦ create₂, 2 ↦ annihilate₂, 3 ↦ annihilate₁` convention. -/
def quarticLocalLegMode (q : QuarticVertexLabel Mode) : Fin 4 → Mode :=
  ![q.create₁, q.create₂, q.annihilate₂, q.annihilate₁]

/-- **Whether a local leg is a creation leg** (`0, 1`) or an annihilation leg (`2, 3`). -/
def quarticLocalLegIsCreate : Fin 4 → Bool := ![true, true, false, false]

omit [Fintype Mode] in
/-- **The bare anticommutator of two local leg operators**, at possibly different vertex labels:
`0` if both legs are the same kind (both creation or both annihilation — CAR's
`anticomm_create_create`/`anticomm_annihilate_annihilate`, *always* `0`, even at the same mode),
and otherwise `δ` on the two legs' modes (CAR's `anticomm_annihilate_create`/
`anticomm_create_annihilate`) — a single closed formula covering same-vertex ("tadpole") and
cross-vertex leg pairs alike, since `quarticLocalLegMode`/`quarticLocalLegOperator` only depend on
the vertex label supplied, not on any shared vertex identity. -/
theorem anticomm_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    anticomm (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      if quarticLocalLegIsCreate l = quarticLocalLegIsCreate l' then
        (0 : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
      else if quarticLocalLegMode q l = quarticLocalLegMode q' l' then LinearMap.id else 0 := by
  fin_cases l <;> fin_cases l' <;>
    simp [quarticLocalLegOperator, quarticLocalLegIsCreate, quarticLocalLegMode,
      anticomm_create_create, anticomm_annihilate_annihilate, anticomm_annihilate_create,
      anticomm_create_annihilate]

omit [Fintype Mode] in
/-- **The general theorem's zeta-commutator hypothesis, for a single vertex's four legs** —
`Common.zetaCommutator` at `ζ := Statistics.fermion.zetaInt` is exactly `anticomm`
(`exchangeCommutator_fermion_eq_anticomm`), so `anticomm_quarticLocalLegOperator` transfers
directly. -/
theorem zetaCommutator_quarticLocalLegOperator (q q' : QuarticVertexLabel Mode) (l l' : Fin 4) :
    Common.zetaCommutator ((Statistics.fermion.zetaInt : ℤ) : ℂ)
        (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      (if quarticLocalLegIsCreate l = quarticLocalLegIsCreate l' then (0 : ℂ)
       else if quarticLocalLegMode q l = quarticLocalLegMode q' l' then 1 else 0) •
        (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) := by
  have hbridge : Common.zetaCommutator ((Statistics.fermion.zetaInt : ℤ) : ℂ)
      (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') =
      anticomm (quarticLocalLegOperator q l) (quarticLocalLegOperator q' l') :=
    exchangeCommutator_fermion_eq_anticomm _ _
  rw [hbridge, anticomm_quarticLocalLegOperator]
  split_ifs <;> simp

end SecondQuantization
