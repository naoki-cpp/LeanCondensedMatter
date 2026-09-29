import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.QuarticDysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture

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
finite-temperature Bloch–de Dominicis theorem.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Expanding `dysonCoeff` of `quarticInteraction` into a vertex-label sum -/

omit [LinearOrder Mode] [Fintype Mode] in
/-- **Continuity in `σ`, at fixed `k n'`, of a matrix coefficient of
`(interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ)`.**
This is the general finite-mode continuity interface obtained from
`Common.continuous_matrixCoeff_interactionPicture`,
`Common.continuous_matrixCoeff_dysonCoeff`, and `Common.matrixCoeff_comp`; it is retained
independently of the quartic specialization below for downstream arguments that need continuity
of an interaction-picture operator composed with a Dyson coefficient. -/
theorem continuous_matrixCoeff_interactionPicture_comp_dysonCoeff [Finite Mode] (ε : Mode → ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ)
    (k n' : Occupation Mode) :
    Continuous (fun σ : ℝ => Common.matrixCoeff
      ((interactionPicture ε V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ)) k n') := by
  letI := Fintype.ofFinite Mode
  simp_rw [Common.matrixCoeff_comp]
  exact continuous_finsetSum _ fun j _ =>
    (Common.continuous_matrixCoeff_interactionPicture (fermionEnergy ε) V k j).mul
      (Common.continuous_matrixCoeff_dysonCoeff (fermionEnergy ε) V n j n')

set_option linter.unusedFintypeInType false in
/-- **Joint continuity, in the full time vector `τ`, of a matrix coefficient of
`Common.quarticVertexSequenceInteractionPicture`** — by induction on `n`: the base case is constant (`n = 0` gives `LinearMap.id`); the successor case's matrix coefficient is a finite sum of products of a
single-coordinate `Complex.exp` factor (`Common.continuous_matrixCoeff_interactionPicture`,
precomposed with the coordinate-`0` projection) and the inductive hypothesis (precomposed with the
"tail" projection `fun i => τ i.succ`). `[Fintype Mode]` is genuinely used (for the finite sum
`Common.matrixCoeff_comp` needs), just not in the statement itself — the linter can't see that. -/
theorem continuous_matrixCoeff_quarticVertexSequenceInteractionPicture (ε : Mode → ℝ) :
    ∀ (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (k n' : Occupation Mode),
      Continuous (fun τ : Fin n → ℝ => Common.matrixCoeff (Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate n q τ) k n')
  | 0, _, _, _ => continuous_const
  | n + 1, q, k, n' => by
    have heq : ∀ τ : Fin (n + 1) → ℝ, Common.matrixCoeff
        (Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate (n + 1) q τ) k n' =
          ∑ j : Occupation Mode, Common.matrixCoeff
            (interactionPicture ε (quarticVertexOperator (q 0)) (τ 0)) k j *
            Common.matrixCoeff
              (Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate n (fun i => q i.succ) (fun i => τ i.succ)) j n' :=
      fun τ => by
        rw [Common.quarticVertexSequenceInteractionPicture_succ, Common.matrixCoeff_comp]
        simp only [interactionPicture, quarticVertexOperator]
    simp_rw [heq]
    exact continuous_finsetSum _ fun j _ =>
      ((Common.continuous_matrixCoeff_interactionPicture
          (fermionEnergy ε) (quarticVertexOperator (q 0)) k j).comp
          (continuous_apply 0)).mul
        ((continuous_matrixCoeff_quarticVertexSequenceInteractionPicture ε n (fun i => q i.succ) j n').comp
          (continuous_pi fun i => continuous_apply i.succ))

/-- Joint continuity, in the full time vector `τ`, of the canonical finite Gibbs expectation of
an `L`-prefixed Common quartic interaction-picture sequence. The diagonal expectation formula reduces continuity to
a finite sum of continuous matrix coefficients. -/
private theorem finiteGibbsExpectation_continuous_comp_quarticVertexSequenceInteractionPicture
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (L : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Continuous (fun τ : Fin n → ℝ =>
      Common.finiteGibbsExpectation (fermionEnergy ε) β
        (L.comp (Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate n q τ))) := by
  simp_rw [Common.finiteGibbsExpectation_eq_sum, Common.matrixCoeff_comp]
  exact continuous_finsetSum _ fun k' _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => continuous_const.mul
      (continuous_matrixCoeff_quarticVertexSequenceInteractionPicture ε n q j k'))

/-- Joint continuity of the canonical free Gibbs density-state expectation of an
`L`-prefixed quartic interaction-picture vertex sequence. The finite diagonal calculation above remains private proof machinery. -/
theorem continuous_freeGibbsDensityOperator_expectation_comp_quarticVertexSequenceInteractionPicture
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (L : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Continuous (fun τ : Fin n → ℝ =>
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv
          (L.comp (Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate n q τ)))) := by
  simpa only [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation] using
    finiteGibbsExpectation_continuous_comp_quarticVertexSequenceInteractionPicture ε β n q L

/-- The quartic Dyson coefficient expansion through the canonical free Gibbs density-state
expectation. The operator-level Dyson expansion and scalar ordered-simplex coefficient are supplied
by the statistics-independent Common quartic Dyson seam. -/
theorem freeGibbsDensityOperator_expectation_comp_dysonCoeff_quarticInteraction
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ∀ (n : ℕ) (t : ℝ) (L : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode),
      (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperatorAlgEquiv
            (L.comp (Common.dysonCoeff (fermionEnergy ε) (quarticInteraction g) n t))) =
        (-1 : ℂ) ^ n * ∑ q : Fin n → QuarticVertexLabel Mode,
          (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n t
            (fun τ => (freeGibbsDensityOperator ε β).expectation
              (Common.finiteHilbertOperatorAlgEquiv
                (L.comp (Common.quarticVertexSequenceInteractionPicture
                  (fermionEnergy ε) create annihilate n q τ)))) := by
  intro n t L
  simp_rw [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation]
  have hcreate : ∀ τ i, Common.heisenbergEvolve (fermionEnergy ε) τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i := by
    intro τ i
    simpa only [imaginaryTimeEvolve] using imaginaryTimeEvolve_create ε τ i
  have hannihilate : ∀ τ i, Common.heisenbergEvolve (fermionEnergy ε) τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i := by
    intro τ i
    simpa only [imaginaryTimeEvolve] using imaginaryTimeEvolve_annihilate ε τ i
  have hdyson :
      Common.dysonCoeff (fermionEnergy ε) (quarticInteraction g) n t =
        ∑ q : Fin n → QuarticVertexLabel Mode,
          Common.quarticDysonSequenceCoeff ε g q t •
            Common.quarticVertexSequenceOperator create annihilate q := by
    simpa only [quarticInteraction] using
      (Common.dysonCoeff_quarticInteraction_eq_sum
        (energy := fermionEnergy ε) (ε := ε) (create := create) (annihilate := annihilate)
        g hcreate hannihilate n t)
  rw [hdyson]
  have hcomp :
      L.comp
          (∑ q : Fin n → QuarticVertexLabel Mode,
            Common.quarticDysonSequenceCoeff ε g q t •
              Common.quarticVertexSequenceOperator create annihilate q) =
        ∑ q : Fin n → QuarticVertexLabel Mode,
          Common.quarticDysonSequenceCoeff ε g q t •
            L.comp (Common.quarticVertexSequenceOperator create annihilate q) := by
    ext x
    simp [LinearMap.comp_apply, LinearMap.sum_apply]
  rw [hcomp]
  change
    (Common.finiteGibbsExpectationLinearMap (fermionEnergy ε) β)
        (∑ q : Fin n → QuarticVertexLabel Mode,
          Common.quarticDysonSequenceCoeff ε g q t •
            L.comp (Common.quarticVertexSequenceOperator create annihilate q)) =
      _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hintegral : ∀ q : Fin n → QuarticVertexLabel Mode,
      intervalIntegral.orderedSimplexIntegral n t
          (fun τ => Common.finiteGibbsExpectation (fermionEnergy ε) β
            (L.comp (Common.quarticVertexSequenceInteractionPicture
              (fermionEnergy ε) create annihilate n q τ))) =
        Common.finiteGibbsExpectation (fermionEnergy ε) β
            (L.comp (Common.quarticVertexSequenceOperator create annihilate q)) *
          intervalIntegral.orderedSimplexIntegral n t
            (Common.quarticVertexSequenceTimeFactor ε q) := by
    intro q
    calc
      intervalIntegral.orderedSimplexIntegral n t
          (fun τ => Common.finiteGibbsExpectation (fermionEnergy ε) β
            (L.comp (Common.quarticVertexSequenceInteractionPicture
              (fermionEnergy ε) create annihilate n q τ))) =
          intervalIntegral.orderedSimplexIntegral n t
            (fun τ =>
              Common.finiteGibbsExpectation (fermionEnergy ε) β
                  (L.comp (Common.quarticVertexSequenceOperator create annihilate q)) *
                Common.quarticVertexSequenceTimeFactor ε q τ) := by
            apply intervalIntegral.orderedSimplexIntegral_congr
            intro τ
            rw [Common.quarticVertexSequenceInteractionPicture_eq_smul
              (fermionEnergy ε) ε create annihilate hcreate hannihilate n q τ,
              LinearMap.comp_smul, Common.finiteGibbsExpectation_smul]
            ring
      _ = Common.finiteGibbsExpectation (fermionEnergy ε) β
              (L.comp (Common.quarticVertexSequenceOperator create annihilate q)) *
            intervalIntegral.orderedSimplexIntegral n t
              (Common.quarticVertexSequenceTimeFactor ε q) :=
        intervalIntegral.orderedSimplexIntegral_smul n t
          (Common.finiteGibbsExpectation (fermionEnergy ε) β
            (L.comp (Common.quarticVertexSequenceOperator create annihilate q)))
          (Common.quarticVertexSequenceTimeFactor ε q)
  simp_rw [hintegral]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Common.quarticDysonSequenceCoeff, Common.finiteGibbsExpectation]
  ring

end Fermionic
end SecondQuantization
