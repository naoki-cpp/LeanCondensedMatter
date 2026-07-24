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

**Still remaining**: applying the general Bloch–de Dominicis theorem
(`Common.BlochDeDominicis.gibbsExpectation_prodComp_eq_sum_pairing`) to the `4n`-operator product
`quarticInteraction`'s expansion produces (`freeGibbsExpectation_comp_dysonCoeff_quarticInteraction`
at `L := LinearMap.id`, `t := β` gives the vertex-label-sum side; the general theorem's own
`4n`-operator eigenoperator/zeta-commutator hypotheses still need to be discharged for
`quarticVertexOperator`'s creation/annihilation legs), and reindexing the resulting
(vertex-label sequence, pairing) sum via `quarticWickDiagramEquivOrderedData` into a genuine sum
over `QuarticWickDiagram`s — see `notes/roadmaps/second-quantization.md` for the full 9-step proof
outline.
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

end SecondQuantization
