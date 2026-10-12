import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.QuarticDysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.InteractionPicture

set_option linter.style.header false

/-!
# Quartic Dyson coefficient expansion and continuity

This module specializes the Common quartic Dyson coefficient expansion to finite fermionic
free-Gibbs expectations, and establishes continuity of the quartic interaction-picture vertex
sequence via its scalar imaginary-time factor.

The Bloch–de Dominicis pairing expansion is proved in `DysonDiagramExpansion/Pairing.lean`;
the final Dyson-to-Wick-diagram reindexing is proved in `DysonDiagramExpansion/Reindexing.lean`.
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

omit [Fintype Mode] in
/-- Joint continuity of the matrix coefficients of the quartic interaction-picture vertex
sequence. The Common scalar-time-factor decomposition reduces this to continuity of a finite
product of exponentials, without a finite-mode assumption. -/
theorem continuous_matrixCoeff_quarticVertexSequenceInteractionPicture (ε : Mode → ℝ) :
    ∀ (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (k n' : Occupation Mode),
      Continuous (fun τ : Fin n → ℝ => Common.matrixCoeff
        (Common.quarticVertexSequenceInteractionPicture
          (fermionEnergy ε) create annihilate n q τ) k n') := by
  intro n q k n'
  have hcreate : ∀ τ i, Common.heisenbergEvolve (fermionEnergy ε) τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i := by
    intro τ i
    simpa only [imaginaryTimeEvolve] using imaginaryTimeEvolve_create ε τ i
  have hannihilate : ∀ τ i, Common.heisenbergEvolve (fermionEnergy ε) τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i := by
    intro τ i
    simpa only [imaginaryTimeEvolve] using imaginaryTimeEvolve_annihilate ε τ i
  simp_rw [Common.quarticVertexSequenceInteractionPicture_eq_smul
    (fermionEnergy ε) ε create annihilate hcreate hannihilate n q]
  change Continuous (fun τ : Fin n → ℝ =>
    (Common.matrixCoeffLinear k n')
      (Common.quarticVertexSequenceTimeFactor ε q τ •
        Common.quarticVertexSequenceOperator create annihilate q))
  simp only [map_smul, smul_eq_mul]
  exact (Common.continuous_quarticVertexSequenceTimeFactor ε q).mul continuous_const

/-- Joint continuity of the free Gibbs density-state expectation of an `L`-prefixed quartic
interaction-picture sequence, directly from the Common scalar-time-factor decomposition. -/
theorem continuous_freeGibbsDensityOperator_expectation_comp_quarticVertexSequenceInteractionPicture
    (ε : Mode → ℝ) (β : ℝ) (n : ℕ) (q : Fin n → QuarticVertexLabel Mode)
    (L : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    Continuous (fun τ : Fin n → ℝ =>
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperatorAlgEquiv
          (L.comp (Common.quarticVertexSequenceInteractionPicture
            (fermionEnergy ε) create annihilate n q τ)))) := by
  have hcreate : ∀ τ i, Common.heisenbergEvolve (fermionEnergy ε) τ (create i) =
      Complex.exp ((τ : ℂ) * (ε i : ℂ)) • create i := by
    intro τ i
    simpa only [imaginaryTimeEvolve] using imaginaryTimeEvolve_create ε τ i
  have hannihilate : ∀ τ i, Common.heisenbergEvolve (fermionEnergy ε) τ (annihilate i) =
      Complex.exp (-(τ : ℂ) * (ε i : ℂ)) • annihilate i := by
    intro τ i
    simpa only [imaginaryTimeEvolve] using imaginaryTimeEvolve_annihilate ε τ i
  simp_rw [Common.quarticVertexSequenceInteractionPicture_eq_smul
    (fermionEnergy ε) ε create annihilate hcreate hannihilate n q]
  simp only [LinearMap.comp_smul,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    Common.finiteGibbsExpectation_smul]
  exact (Common.continuous_quarticVertexSequenceTimeFactor ε q).mul continuous_const

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
    rw [← intervalIntegral.orderedSimplexIntegral_smul]
    apply intervalIntegral.orderedSimplexIntegral_congr
    intro τ
    rw [Common.quarticVertexSequenceInteractionPicture_eq_smul
      (fermionEnergy ε) ε create annihilate hcreate hannihilate n q τ,
      LinearMap.comp_smul, Common.finiteGibbsExpectation_smul]
    ring
  simp_rw [hintegral]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Common.quarticDysonSequenceCoeff, Common.finiteGibbsExpectation]
  ring

end Fermionic
end SecondQuantization
