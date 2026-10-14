import Mathlib.RingTheory.Idempotents
import LeanCondensedMatter.Models.RashbaExchange.Operator
import LeanCondensedMatter.Models.RashbaExchange.Model.Spectral
import LeanCondensedMatter.Transport.Resolvent.Uniqueness
import LeanCondensedMatter.Transport.Resolvent.Spectral
import LeanCondensedMatter.Analysis.Operator.FiniteTrace

set_option linter.style.header false

/-!
# Bounded-operator spectral resolvent of the Rashba-exchange model

Gauge-free band projectors are transported to the bounded-operator realization and used to build the
finite two-band projector resolvent.  Away from the band degeneracy, this candidate equals the
canonical resolvent at every nonzero signed imaginary regulator.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

open ContinuousLinearMap
open QuantumTheory.Transport

/-- Band projector transported to the bounded-operator representation. -/
noncomputable def bandProjectorOperator
    (params : Parameters) (band : Band) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  matrixOperator (bandProjector params band px py)

/-- Ordered current band block `Tr(P_target j_μ P_source j_ν)`. -/
noncomputable def currentBandBlockTrace
    (params : Parameters) (μ ν : Fin 2) (source target : Band) (px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator params target px py *
      currentBoundedOperator params μ px py *
      bandProjectorOperator params source px py *
      currentBoundedOperator params ν px py)

/-- The operator band projectors resolve the identity. -/
theorem sum_bandProjectorOperator_eq_one
    (params : Parameters) (px py : ℝ) :
    ∑ band : Band, bandProjectorOperator params band px py = 1 := by
  unfold bandProjectorOperator matrixOperator
  rw [← map_sum, sum_bandProjector_eq_one params px py, map_one]

/-- Operator projectors remain idempotent. -/
theorem bandProjectorOperator_mul_self
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    bandProjectorOperator params band px py *
        bandProjectorOperator params band px py =
      bandProjectorOperator params band px py := by
  simpa [bandProjectorOperator, matrixOperator] using
    congrArg matrixOperator (bandProjector_mul_self params band px py hE)

/-- Opposite-band operator projectors are orthogonal. -/
theorem bandProjectorOperator_mul_oppositeBand
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    bandProjectorOperator params band px py *
        bandProjectorOperator params (oppositeBand band) px py = 0 := by
  simpa [bandProjectorOperator, matrixOperator] using
    congrArg matrixOperator
      (bandProjector_mul_oppositeBand params band px py hE)

/-- The Hamiltonian acts on each projector with its shifted band energy. -/
theorem hamiltonianOperator_mul_bandProjectorOperator
    (params : Parameters) (band : Band) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    hamiltonianOperator params px py * bandProjectorOperator params band px py =
      (((bandEnergy params band px py : ℝ) : ℂ)) •
        bandProjectorOperator params band px py := by
  unfold hamiltonianOperator bandProjectorOperator matrixOperator
  rw [← map_mul, hamiltonian_mul_bandProjector params band px py hE, map_smul]

/-- Scalar coefficient of one band in the projector resolvent. -/
noncomputable def projectorResolventCoefficient
    (z : ℂ) (params : Parameters) (band : Band) (px py : ℝ) : ℂ :=
  (z - ((bandEnergy params band px py : ℝ) : ℂ))⁻¹

/-- The model-local projector coefficient is the generic scalar spectral resolvent coefficient. -/
theorem projectorResolventCoefficient_eq_scalarResolventCoefficient
    (z : ℂ) (params : Parameters) (band : Band) (px py : ℝ) :
    projectorResolventCoefficient z params band px py =
      scalarResolventCoefficient z (bandEnergy params band px py) := by
  rfl

/-- The scalar projector-resolvent coefficient is continuous away from its pole. -/
theorem continuousAt_projectorResolventCoefficient
    (z : ℂ) (params : Parameters) (band : Band) (px py : ℝ)
    (hden : z - ((bandEnergy params band px py : ℝ) : ℂ) ≠ 0) :
    ContinuousAt
      (fun w : ℂ => projectorResolventCoefficient w params band px py)
      z := by
  simpa only [projectorResolventCoefficient_eq_scalarResolventCoefficient] using
    continuousAt_scalarResolventCoefficient
      z (bandEnergy params band px py) hden

/-- Gauge-free finite-band spectral candidate for the resolvent. -/
noncomputable def projectorResolvent
    (z : ℂ) (params : Parameters) (px py : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  ∑ band : Band,
    projectorResolventCoefficient z params band px py •
      bandProjectorOperator params band px py

/-- Squaring the projector resolvent squares only the scalar coefficients. -/
theorem projectorResolvent_sq
    (z : ℂ) (params : Parameters) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) :
    projectorResolvent z params px py ^ 2 =
      ∑ band : Band,
        projectorResolventCoefficient z params band px py ^ 2 •
          bandProjectorOperator params band px py := by
  have hproj : OrthogonalIdempotents
      (fun band : Band => bandProjectorOperator params band px py) := by
    refine ⟨?_, ?_⟩
    · intro band
      exact bandProjectorOperator_mul_self params band px py hE
    · intro i j hij
      cases i <;> cases j <;> try exact (hij rfl).elim
      · exact bandProjectorOperator_mul_oppositeBand params .lower px py hE
      · exact bandProjectorOperator_mul_oppositeBand params .upper px py hE
  classical
  simp [projectorResolvent, pow_two, Finset.sum_mul, Finset.mul_sum,
    smul_smul, hproj.mul_eq]

private theorem shiftedHamiltonian_mul_projectorResolvent
    (z : ℂ) (params : Parameters) (px py : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0)
    (hlower : z - ((bandEnergy params .lower px py : ℝ) : ℂ) ≠ 0)
    (hupper : z - ((bandEnergy params .upper px py : ℝ) : ℂ) ≠ 0) :
    (algebraMap ℂ (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) z -
        hamiltonianOperator params px py) *
        projectorResolvent z params px py = 1 := by
  simpa only [projectorResolvent, projectorResolventCoefficient] using
    QuantumTheory.mul_sum_inv_smul_eq_one_of_diagonal_action
      (algebraMap ℂ (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) z -
        hamiltonianOperator params px py)
      (fun band : Band => bandProjectorOperator params band px py)
      (fun band : Band => z - ((bandEnergy params band px py : ℝ) : ℂ))
      (sum_bandProjectorOperator_eq_one params px py)
      (by
        intro band
        rw [sub_mul, hamiltonianOperator_mul_bandProjectorOperator params band px py hE]
        simp [Algebra.algebraMap_eq_smul_one, sub_smul])
      (by intro band; cases band <;> assumption)

/-- At nonzero signed regulator, the canonical resolvent equals the gauge-free projector expansion. -/
theorem resolvent_spectralParameterOfRegulator_eq_projectorResolvent
    (params : Parameters) (px py probeEnergy regulator : ℝ)
    (hE : spinOrbitEnergy params px py ≠ 0) (hregulator : regulator ≠ 0) :
    resolvent (hamiltonianOperator params px py)
        (spectralParameterOfRegulator probeEnergy regulator) =
      projectorResolvent
        (spectralParameterOfRegulator probeEnergy regulator) params px py := by
  apply resolvent_eq_of_spectralShift_mul_eq_one
    (hamiltonianOperator params px py)
    (projectorResolvent
      (spectralParameterOfRegulator probeEnergy regulator) params px py)
    (hamiltonianOperator_isSelfAdjoint params px py)
    probeEnergy regulator hregulator
  exact shiftedHamiltonian_mul_projectorResolvent
    (spectralParameterOfRegulator probeEnergy regulator) params px py hE
    (spectralParameterOfRegulator_sub_real_ne_zero
      probeEnergy regulator (bandEnergy params .lower px py) hregulator)
    (spectralParameterOfRegulator_sub_real_ne_zero
      probeEnergy regulator (bandEnergy params .upper px py) hregulator)

end

end QuantumTheory.Models.RashbaExchange
