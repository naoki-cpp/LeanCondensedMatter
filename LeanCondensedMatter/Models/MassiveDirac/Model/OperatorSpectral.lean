import Mathlib.RingTheory.Idempotents
import LeanCondensedMatter.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Models.MassiveDirac.Model.Spectral
import LeanCondensedMatter.Transport.Resolvent.Uniqueness
import LeanCondensedMatter.Transport.Resolvent.Spectral

set_option linter.style.header false

/-!
# Bounded-operator spectral resolvent of the massive-Dirac model

The massive-Dirac model has explicit gauge-independent rank-one band projectors `P₋` and `P₊`.
This module transports those projectors to the bounded-operator realization and connects them to the
generic transport resolvent, without choosing eigenvectors or introducing a response formalism.

Away from the band degeneracy,

```text
G(z) = ∑ₙ (z - Eₙ)⁻¹ Pₙ
```

is a left inverse of `z I - H₀`. The operator-projector algebra, direction-indexed current band
blocks, and finite-band scalar coefficient form of that spectral expansion, including its square and
arbitrary nonzero signed-regulator realization, are therefore model-level spectral infrastructure.
Kubo–Bastin, Středa, propagator, and disorder consumers remain downstream.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

open ContinuousLinearMap

/-- A massive-Dirac band projector transported to the bounded-operator representation used by the
transport stack. -/
noncomputable def bandProjectorOperator (band : Band) (v m px py : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (bandProjector band v m px py)

/-- Every band projector is a nonzero bounded operator. -/
theorem bandProjectorOperator_ne_zero (band : Band) (v m px py : ℝ) :
    bandProjectorOperator band v m px py ≠ 0 := by
  intro hzero
  have hmatrix : bandProjector band v m px py = 0 := by
    apply (Matrix.toEuclideanCLM :
      Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert)).injective
    simpa [bandProjectorOperator, matrixOperator] using hzero
  have htrace := congrArg Matrix.trace hmatrix
  simpa using htrace

/-- Ordered current band block `Tr(P_target j_μ P_source j_ν)` in the bounded-operator model. -/
noncomputable def currentBandBlockTrace
    (μ ν : Fin 2) (source target : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator target v m px py * currentOperator μ e v *
      bandProjectorOperator source v m px py * currentOperator ν e v)

/-- The bounded-operator projectors inherit the complete orthogonal family
from the matrix realization under the algebra equivalence. -/
theorem bandProjectorOperator_completeOrthogonalIdempotents
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    CompleteOrthogonalIdempotents
      (fun band : Band => bandProjectorOperator band v m px py) := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) :=
    Matrix.toEuclideanCLM
  change CompleteOrthogonalIdempotents
    ((φ.toRingEquiv.toRingHom) ∘
      (fun band : Band => bandProjector band v m px py))
  exact (bandProjector_completeOrthogonalIdempotents v m px py hE).map
    φ.toRingEquiv.toRingHom

/-- The Hamiltonian acts on each operator projector with its band energy. -/
theorem hamiltonianOperator_mul_bandProjectorOperator
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    hamiltonianOperator v m px py * bandProjectorOperator band v m px py =
      (((bandEnergy band v m px py : ℝ) : ℂ)) •
        bandProjectorOperator band v m px py := by
  unfold hamiltonianOperator bandProjectorOperator matrixOperator
  rw [← map_mul, hamiltonian_mul_bandProjector band v m px py hE, map_smul]

/-- Scalar coefficient of band `band` in the gauge-free projector resolvent at spectral parameter
`z`. -/
noncomputable def projectorResolventCoefficient
    (z : ℂ) (band : Band) (v m px py : ℝ) : ℂ :=
  (z - ((bandEnergy band v m px py : ℝ) : ℂ))⁻¹

/-- The model-local projector coefficient is the generic scalar spectral resolvent coefficient. -/
theorem projectorResolventCoefficient_eq_scalarResolventCoefficient
    (z : ℂ) (band : Band) (v m px py : ℝ) :
    projectorResolventCoefficient z band v m px py =
      scalarResolventCoefficient z (bandEnergy band v m px py) := by
  rfl

/-- The scalar projector-resolvent coefficient is continuous wherever its spectral denominator is
nonzero. -/
theorem continuousAt_projectorResolventCoefficient
    (z : ℂ) (band : Band) (v m px py : ℝ)
    (hden : z - ((bandEnergy band v m px py : ℝ) : ℂ) ≠ 0) :
    ContinuousAt
      (fun w : ℂ => projectorResolventCoefficient w band v m px py)
      z := by
  simpa only [projectorResolventCoefficient_eq_scalarResolventCoefficient] using
    continuousAt_scalarResolventCoefficient
      z (bandEnergy band v m px py) hden

/-- Gauge-free finite-band spectral candidate for the resolvent of the massive-Dirac Hamiltonian. -/
noncomputable def projectorResolvent
    (z : ℂ) (v m px py : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  ∑ band : Band,
    projectorResolventCoefficient z band v m px py •
      bandProjectorOperator band v m px py

/-- Squaring the finite-band projector resolvent squares only its scalar spectral coefficients. -/
theorem projectorResolvent_sq
    (z : ℂ) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    projectorResolvent z v m px py ^ 2 =
      ∑ band : Band,
        projectorResolventCoefficient z band v m px py ^ 2 •
          bandProjectorOperator band v m px py := by
  have hproj := bandProjectorOperator_completeOrthogonalIdempotents v m px py hE
  classical
  simp [projectorResolvent, pow_two, Finset.sum_mul, Finset.mul_sum,
    smul_smul, hproj.toOrthogonalIdempotents.mul_eq]

private theorem shiftedHamiltonian_mul_projectorResolvent
    (z : ℂ) (v m px py : ℝ) (hE : energy v m px py ≠ 0)
    (hlower : z - ((bandEnergy .lower v m px py : ℝ) : ℂ) ≠ 0)
    (hupper : z - ((bandEnergy .upper v m px py : ℝ) : ℂ) ≠ 0) :
    (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert) z - hamiltonianOperator v m px py) *
        projectorResolvent z v m px py = 1 := by
  simpa only [projectorResolvent, projectorResolventCoefficient] using
    QuantumTheory.mul_sum_inv_smul_eq_one_of_diagonal_action
      (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert) z -
        hamiltonianOperator v m px py)
      (fun band : Band => bandProjectorOperator band v m px py)
      (fun band : Band => z - ((bandEnergy band v m px py : ℝ) : ℂ))
      (bandProjectorOperator_completeOrthogonalIdempotents v m px py hE).complete
      (by
        intro band
        rw [sub_mul, hamiltonianOperator_mul_bandProjectorOperator band v m px py hE]
        simp [Algebra.algebraMap_eq_smul_one, sub_smul])
      (by intro band; cases band <;> assumption)

/-- The regulated massive-Dirac resolvent equals the gauge-free finite-projector expansion for any
nonzero signed imaginary regulator. -/
theorem resolvent_spectralParameterOfRegulator_eq_projectorResolvent
    (v m px py probeEnergy regulator : ℝ)
    (hE : energy v m px py ≠ 0) (hregulator : regulator ≠ 0) :
    resolvent (hamiltonianOperator v m px py)
        (spectralParameterOfRegulator probeEnergy regulator) =
      projectorResolvent (spectralParameterOfRegulator probeEnergy regulator) v m px py := by
  apply resolvent_eq_of_spectralShift_mul_eq_one
    (hamiltonianOperator v m px py)
    (projectorResolvent (spectralParameterOfRegulator probeEnergy regulator) v m px py)
    (hamiltonianOperator_isSelfAdjoint v m px py)
    probeEnergy regulator hregulator
  exact shiftedHamiltonian_mul_projectorResolvent
    (spectralParameterOfRegulator probeEnergy regulator) v m px py hE
    (spectralParameterOfRegulator_sub_real_ne_zero
      probeEnergy regulator (bandEnergy .lower v m px py) hregulator)
    (spectralParameterOfRegulator_sub_real_ne_zero
      probeEnergy regulator (bandEnergy .upper v m px py) hregulator)

end

end QuantumTheory.Models.MassiveDirac
