import LeanCondensedMatter.SecondQuantization.Common.Perturbation.DysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.QuarticDysonExpansion
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.QuarticInteraction
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.InteractionPicture
import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# Quartic Dyson coefficient expansion and continuity

This module evaluates the Common quartic Dyson coefficient expansion against an arbitrary
finite occupation-basis Gibbs energy. The physical interaction-picture evolution retains
`fermionEnergy ε`, independently of the energy defining the expectation.

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
`(Common.interactionPicture (fermionEnergy ε) V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ)`.**
This is the general finite-mode continuity interface obtained from
`Common.continuous_matrixCoeff_interactionPicture`,
`Common.continuous_matrixCoeff_dysonCoeff`, and `Common.matrixCoeff_comp`; it is retained
independently of the quartic specialization below for downstream arguments that need continuity
of an interaction-picture operator composed with a Dyson coefficient. -/
theorem continuous_matrixCoeff_interactionPicture_comp_dysonCoeff [Finite Mode] (ε : Mode → ℝ)
    (V : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) (n : ℕ)
    (k n' : Occupation Mode) :
    Continuous (fun σ : ℝ => Common.matrixCoeff
      ((Common.interactionPicture (fermionEnergy ε) V σ).comp (Common.dysonCoeff (fermionEnergy ε) V n σ)) k n') := by
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

/-- The quartic Dyson coefficient expansion against a finite Gibbs expectation with arbitrary
configuration energy. Dyson evolution continues to use the physical `fermionEnergy ε`;
the Gibbs energy is an independent input, permitting explicit-μ specializations. -/
theorem finiteGibbsExpectation_comp_dysonCoeff_quarticInteraction
    (ε : Mode → ℝ) (energy : Occupation Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) :
    ∀ (n : ℕ) (t : ℝ) (L : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode),
      Common.finiteGibbsExpectation energy β
          (L.comp (Common.dysonCoeff (fermionEnergy ε) (quarticInteraction g) n t)) =
        (-1 : ℂ) ^ n * ∑ q : Fin n → QuarticVertexLabel Mode,
          (∏ i, g (q i)) * intervalIntegral.orderedSimplexIntegral n t
            (fun τ => Common.finiteGibbsExpectation energy β
              (L.comp (Common.quarticVertexSequenceInteractionPicture
                (fermionEnergy ε) create annihilate n q τ))) := by
  intro n t L
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
    (Common.finiteGibbsExpectationLinearMap energy β)
        (∑ q : Fin n → QuarticVertexLabel Mode,
          Common.quarticDysonSequenceCoeff ε g q t •
            L.comp (Common.quarticVertexSequenceOperator create annihilate q)) =
      _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  have hintegral : ∀ q : Fin n → QuarticVertexLabel Mode,
      intervalIntegral.orderedSimplexIntegral n t
          (fun τ => Common.finiteGibbsExpectation energy β
            (L.comp (Common.quarticVertexSequenceInteractionPicture
              (fermionEnergy ε) create annihilate n q τ))) =
        Common.finiteGibbsExpectation energy β
            (L.comp (Common.quarticVertexSequenceOperator create annihilate q)) *
          intervalIntegral.orderedSimplexIntegral n t
            (Common.quarticVertexSequenceTimeFactor ε q) := by
    intro q
    rw [← intervalIntegral.orderedSimplexIntegral_smul]
    apply intervalIntegral.orderedSimplexIntegral_congr
    intro τ
    rw [Common.quarticVertexSequenceInteractionPicture_eq_smul
      (fermionEnergy ε) ε create annihilate hcreate hannihilate n q τ,
      LinearMap.comp_smul, Common.finiteGibbsExpectation, map_smul, smul_eq_mul]
    exact mul_comm _ _
  simp_rw [hintegral]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  simp only [Common.quarticDysonSequenceCoeff, Common.finiteGibbsExpectation]
  ring

end Fermionic
end SecondQuantization
