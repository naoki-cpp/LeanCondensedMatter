import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.Interaction

set_option linter.style.header false

/-!
# Dyson-to-diagram expansion

This module proves that the Dyson vertex moment of a quartic interaction equals the sum of
quartic Wick-diagram amplitudes:

```
dysonVertexMoment ε β (quarticInteraction g) S =
  ∑ d : QuarticWickDiagram Mode N S, quarticWickDiagramAmplitude ε β g d
```

(`dysonVertexMoment_quarticInteraction_eq_sum_quarticWickDiagramAmplitude`), via the general
finite-temperature Bloch–de Dominicis theorem. See `notes/roadmaps/second-quantization.md` for the
surrounding diagram-connectedness plan.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Expanding `dysonCoeff` of `quarticInteraction` into a vertex-label sum -/

/-- **The nested interaction-picture vertex-operator composition**, `V_I(τ 0) ∘ V_I(τ 1) ∘ ⋯ ∘
V_I(τ (n-1))` for a fixed vertex-label sequence `q : Fin n → QuarticVertexLabel Mode` — the
operator-valued integrand used by the density-state Dyson expansion's
`orderedSimplexIntegral` integrates. Coordinate `0` is the latest/outermost time, matching
`orderedSimplexIntegral`'s own convention. -/
noncomputable def nestedVertexOperatorComp (ε : Mode → ℝ) :
    (n : ℕ) → (Fin n → QuarticVertexLabel Mode) → (Fin n → ℝ) →
      OccupationFock Mode →ₗ[ℂ] OccupationFock Mode
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
σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ)`** — the finite sum of products of
`Common.continuous_matrixCoeff_interactionPicture`/`Common.continuous_matrixCoeff_dysonCoeff` (via
`Common.matrixCoeff_comp`), the integrability the inductive step's
`Common.comp_operatorIntervalIntegral`/`Common.normalizedWeightedDiagonal_operatorIntervalIntegral`
need. -/
theorem continuous_matrixCoeff_interactionPicture_comp_dysonCoeff (ε : Mode → ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ)
    (k n' : Occupation Mode) :
    Continuous (fun σ : ℝ => Common.matrixCoeff
      ((interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ)) k n') := by
  simp_rw [Common.matrixCoeff_comp]
  exact continuous_finsetSum _ fun j _ =>
    (Common.continuous_matrixCoeff_interactionPicture (fermionEnergy ε) V k j).mul
      (Common.continuous_matrixCoeff_dysonCoeff (fermionEnergy ε) V n j n')

set_option linter.unusedFintypeInType false in
/-- **Joint continuity, in the full time vector `τ`, of a matrix coefficient of
`nestedVertexOperatorComp`** — by induction on `n`: the base case is constant (`nested...Comp ε 0
q τ = LinearMap.id`); the successor case's matrix coefficient is a finite sum of products of a
single-coordinate `Complex.exp` factor (`Common.continuous_matrixCoeff_interactionPicture`,
precomposed with the coordinate-`0` projection) and the inductive hypothesis (precomposed with the
"tail" projection `fun i => τ i.succ`). `[Fintype Mode]` is genuinely used (for the finite sum
`Common.matrixCoeff_comp` needs), just not in the statement itself — the linter can't see that. -/
theorem continuous_matrixCoeff_nestedVertexOperatorComp (ε : Mode → ℝ) :
    ∀ (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (k n' : Occupation Mode),
      Continuous (fun τ : Fin n → ℝ => Common.matrixCoeff (nestedVertexOperatorComp ε n q τ) k n')
  | 0, _, _, _ => continuous_const
  | n + 1, q, k, n' => by
    have heq : ∀ τ : Fin (n + 1) → ℝ, Common.matrixCoeff
        (nestedVertexOperatorComp ε (n + 1) q τ) k n' =
          ∑ j : Occupation Mode, Common.matrixCoeff
            (interactionPicture ε (quarticVertexOperator (q 0)) (τ 0)) k j *
            Common.matrixCoeff
              (nestedVertexOperatorComp ε n (fun i => q i.succ) (fun i => τ i.succ)) j n' :=
      fun τ => by rw [nestedVertexOperatorComp_succ, Common.matrixCoeff_comp]
    simp_rw [heq]
    exact continuous_finsetSum _ fun j _ =>
      ((Common.continuous_matrixCoeff_interactionPicture
          (fermionEnergy ε) (quarticVertexOperator (q 0)) k j).comp
          (continuous_apply 0)).mul
        ((continuous_matrixCoeff_nestedVertexOperatorComp ε n (fun i => q i.succ) j n').comp
          (continuous_pi fun i => continuous_apply i.succ))

/-- Joint continuity, in the full time vector `τ`, of the canonical finite Gibbs expectation of
an `L`-prefixed `nestedVertexOperatorComp`. The diagonal expectation formula reduces continuity to
a finite sum of continuous matrix coefficients. -/
private theorem finiteGibbsExpectation_continuous_comp_nestedVertexOperatorComp
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (L : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Continuous (fun τ : Fin n → ℝ =>
      Common.finiteGibbsExpectation (fermionEnergy ε) β
        (L.comp (nestedVertexOperatorComp ε n q τ))) := by
  simp_rw [Common.finiteGibbsExpectation_eq_sum, Common.matrixCoeff_comp]
  exact continuous_finsetSum _ fun k' _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => continuous_const.mul
      (continuous_matrixCoeff_nestedVertexOperatorComp ε n q j k'))

/-- Joint continuity of the canonical free Gibbs density-state expectation of an
`L`-prefixed nested vertex product. The finite diagonal calculation above remains private proof machinery. -/
theorem continuous_freeGibbsDensityOperator_expectation_comp_nestedVertexOperatorComp
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (L : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Continuous (fun τ : Fin n → ℝ =>
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator
          (L.comp (nestedVertexOperatorComp ε n q τ)))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
    finiteGibbsExpectation_continuous_comp_nestedVertexOperatorComp ε β n q L

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

omit [LinearOrder Mode] in
private theorem finiteGibbsExpectation_neg_apply (ε : Mode → ℝ) (β : ℝ)
    (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β (-A) =
      -Common.finiteGibbsExpectation (fermionEnergy ε) β A := by
  change (Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β) (-A) =
    -(Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β) A
  exact map_neg _ A

omit [LinearOrder Mode] in
private theorem finiteGibbsExpectation_fintype_sum {ι : Type*} [Fintype ι]
    (ε : Mode → ℝ) (β : ℝ) (F : ι → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Common.finiteGibbsExpectation (fermionEnergy ε) β (∑ i, F i) =
      ∑ i, Common.finiteGibbsExpectation (fermionEnergy ε) β (F i) := by
  change (Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β) (∑ i, F i) = _
  simpa using map_sum (Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β) F Finset.univ

/-- **The key induction: `dysonCoeff` of `quarticInteraction`, left-composed with an arbitrary
fixed prefix operator `L`, expands into a `(-1)ⁿ`-signed sum over vertex-label sequences of an
`orderedSimplexIntegral` of `L`-prefixed `nestedVertexOperatorComp` values.** The prefix `L`
generalizes the induction so the successor case can absorb the newly-peeled-off outermost vertex
factor into `L` before invoking the inductive hypothesis on the remaining `n`-fold piece; the
bound `t` likewise generalizes so the inductive step's inner integral (over `[0, σ]` for the
recursion's own integration variable `σ`) is exactly an instance of the same statement, rather
than requiring a separate lemma for non-`β` bounds. -/
private theorem finiteGibbsExpectation_comp_dysonCoeff_quarticInteraction (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) :
    ∀ (n : ℕ) (t : ℝ) (L : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode),
      Common.finiteGibbsExpectation (fermionEnergy ε) β (L.comp (Common.dysonCoeff (fermionEnergy ε) (quarticInteraction g) n t)) =
        (-1 : ℂ) ^ n * ∑ q : Fin n → QuarticVertexLabel Mode,
          (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n t
            (fun τ => Common.finiteGibbsExpectation (fermionEnergy ε) β (L.comp (nestedVertexOperatorComp ε n q τ))) := by
  intro n
  induction n with
  | zero =>
    intro t L
    have huniq : Unique (Fin 0 → QuarticVertexLabel Mode) := Pi.uniqueOfIsEmpty _
    rw [Common.dysonCoeff_zero, LinearMap.comp_id, Fintype.sum_unique]
    simp
  | succ n ih =>
    intro t L
    set V := quarticInteraction g with hV
    have hcont : ∀ k n' : Occupation Mode,
        IntervalIntegrable (fun σ => Common.matrixCoeff
          ((interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ)) k n') MeasureTheory.volume 0 t :=
      fun k n' =>
        (continuous_matrixCoeff_interactionPicture_comp_dysonCoeff ε V n k n').intervalIntegrable
          0 t
    have hdysonSucc :
        Common.dysonCoeff (fermionEnergy ε) V (n + 1) t =
          - Common.operatorIntervalIntegral
            (fun σ => (interactionPicture ε V σ).comp
              (Common.dysonCoeff (fermionEnergy ε) V n σ)) 0 t := by
      simpa only [interactionPicture] using
        (Common.dysonCoeff_succ (fermionEnergy ε) V n t)
    rw [hdysonSucc, LinearMap.comp_neg,
      Common.comp_operatorIntervalIntegral _ _ _ _ hcont, finiteGibbsExpectation_neg_apply]
    have hcont2 : ∀ n' : Occupation Mode,
        IntervalIntegrable (fun σ => Common.matrixCoeff
          (L.comp ((interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ))) n' n')
          MeasureTheory.volume 0 t := by
      intro n'
      have heq : ∀ σ : ℝ, Common.matrixCoeff
          (L.comp ((interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ))) n' n' =
          ∑ j : Occupation Mode, Common.matrixCoeff L n' j *
            Common.matrixCoeff ((interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ)) j n' :=
        fun σ => Common.matrixCoeff_comp L _ n' n'
      have hc : Continuous (fun σ => Common.matrixCoeff
          (L.comp ((interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ))) n' n') := by
        simp_rw [heq]
        exact continuous_finsetSum _ fun j _ => continuous_const.mul
          (continuous_matrixCoeff_interactionPicture_comp_dysonCoeff ε V n j n')
      exact hc.intervalIntegrable 0 t
    rw [Common.finiteGibbsExpectation_operatorIntervalIntegral (fermionEnergy ε) β _ 0 t hcont2]
    have hpoint : ∀ σ : ℝ, Common.finiteGibbsExpectation (fermionEnergy ε) β
        (L.comp ((interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ))) =
        (-1 : ℂ) ^ n * ∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
          (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n σ
            (fun τ' => Common.finiteGibbsExpectation (fermionEnergy ε) β
              (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ')))) := by
      intro σ
      have e2 : L.comp ((interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ)) =
          ∑ q0 : QuarticVertexLabel Mode,
            g q0 • ((L.comp (interactionPicture ε (quarticVertexOperator q0) σ)).comp
              (Common.dysonCoeff (fermionEnergy ε) V n σ)) := by
        rw [hV, interactionPicture_quarticInteraction]
        ext x
        simp [LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.comp_assoc]
      rw [e2, finiteGibbsExpectation_fintype_sum]
      have hstep : ∀ q0 : QuarticVertexLabel Mode, Common.finiteGibbsExpectation (fermionEnergy ε) β
          (g q0 • ((L.comp (interactionPicture ε (quarticVertexOperator q0) σ)).comp
            (Common.dysonCoeff (fermionEnergy ε) V n σ))) =
          (-1 : ℂ) ^ n * ∑ q' : Fin n → QuarticVertexLabel Mode,
            g q0 * (∏ i, g (q' i)) * intervalIntegral.orderedSimplexIntegral n σ
              (fun τ' => Common.finiteGibbsExpectation (fermionEnergy ε) β
                (L.comp (nestedVertexOperatorComp ε (n + 1) (Fin.cons q0 q')
                  (Fin.cons σ τ')))) := by
        intro q0
        rw [Common.finiteGibbsExpectation_smul,
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
            (fun τ' => Common.finiteGibbsExpectation (fermionEnergy ε) β
              (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ')))))]
      refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨q0, q'⟩ := p
      change (g q0 * ∏ i, g (q' i)) *
          intervalIntegral.orderedSimplexIntegral n σ
            (fun τ' => Common.finiteGibbsExpectation (fermionEnergy ε) β
              (L.comp (nestedVertexOperatorComp ε (n + 1) (Fin.cons q0 q') (Fin.cons σ τ')))) =
        (∏ i, g (e (q0, q') i)) *
          intervalIntegral.orderedSimplexIntegral n σ
            (fun τ' => Common.finiteGibbsExpectation (fermionEnergy ε) β
              (L.comp (nestedVertexOperatorComp ε (n + 1) (e (q0, q')) (Fin.cons σ τ'))))
      congr 1
      rw [Fin.prod_univ_succ]
      rfl
    simp_rw [hpoint]
    rw [intervalIntegral.integral_const_mul]
    have hintegrability : ∀ q : Fin (n + 1) → QuarticVertexLabel Mode,
        IntervalIntegrable (fun σ => (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n σ
          (fun τ' => Common.finiteGibbsExpectation (fermionEnergy ε) β
            (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ')))))
          MeasureTheory.volume 0 t := by
      intro q
      have hcontF : Continuous (Function.uncurry
          (fun (σ : ℝ) (τ' : Fin n → ℝ) => Common.finiteGibbsExpectation (fermionEnergy ε) β
            (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ'))))) :=
        (finiteGibbsExpectation_continuous_comp_nestedVertexOperatorComp ε β (n + 1) q L).comp
          (Continuous.finCons continuous_fst continuous_snd)
      have hcont := intervalIntegral.continuous_orderedSimplexIntegral_of_continuous n
        (id : ℝ → ℝ) _ continuous_id hcontF
      exact (continuous_const.mul hcont).intervalIntegrable 0 t
    rw [intervalIntegral.integral_finsetSum (fun q _ => hintegrability q)]
    have hsum_eq : ∑ q : Fin (n + 1) → QuarticVertexLabel Mode,
        ∫ σ in (0 : ℝ)..t, (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n σ
          (fun τ' => Common.finiteGibbsExpectation (fermionEnergy ε) β
            (L.comp (nestedVertexOperatorComp ε (n + 1) q (Fin.cons σ τ')))) =
        ∑ q : Fin (n + 1) → QuarticVertexLabel Mode, (∏ i, g (q i)) *
          intervalIntegral.orderedSimplexIntegral (n + 1) t
            (fun τ => Common.finiteGibbsExpectation (fermionEnergy ε) β (L.comp (nestedVertexOperatorComp ε (n + 1) q τ)))
        := by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [intervalIntegral.integral_const_mul]
      congr 1
    rw [hsum_eq]
    ring

/-- The quartic Dyson coefficient expansion through the canonical free Gibbs density-state
expectation. The finite Gibbs induction above is private proof machinery. -/
theorem freeGibbsDensityOperator_expectation_comp_dysonCoeff_quarticInteraction
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ∀ (n : ℕ) (t : ℝ) (L : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode),
      (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator
            (L.comp (Common.dysonCoeff (fermionEnergy ε) (quarticInteraction g) n t))) =
        (-1 : ℂ) ^ n * ∑ q : Fin n → QuarticVertexLabel Mode,
          (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n t
            (fun τ => (freeGibbsDensityOperator ε β).expectation
              (Common.finiteHilbertOperator
                (L.comp (nestedVertexOperatorComp ε n q τ)))) := by
  intro n t L
  simpa only [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
    finiteGibbsExpectation_comp_dysonCoeff_quarticInteraction ε β g n t L

end Fermionic
end SecondQuantization
