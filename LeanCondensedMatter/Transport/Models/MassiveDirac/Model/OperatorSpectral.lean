import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Operator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Model.Spectral
import LeanCondensedMatter.Transport.Resolvent.Uniqueness

set_option linter.style.header false

/-!
# Bounded-operator spectral resolvent of the massive-Dirac model

The massive-Dirac model has explicit gauge-independent rank-one band projectors `P₋` and `P₊`.
This module transports those projectors to the bounded-operator realization and connects them to the
generic transport resolvent, without choosing eigenvectors or introducing a response formalism.

Away from the band degeneracy,

```text
G(z) = (z - E₋)⁻¹ P₋ + (z - E₊)⁻¹ P₊
```

is a left inverse of `z I - H₀`. The operator-projector algebra and scalar coefficient form of that
spectral expansion, including its square and arbitrary nonzero signed-regulator realization, are
therefore model-level spectral infrastructure. Kubo–Bastin, Středa, propagator, and disorder
consumers remain downstream.
-/

namespace AnomalousHall.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- A massive-Dirac band projector transported to the bounded-operator representation used by the
transport stack. -/
noncomputable def bandProjectorOperator (band : Band) (v m px py : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (bandProjector band v m px py)

/-- The two operator projectors resolve the identity. -/
theorem bandProjectorOperator_lower_add_upper (v m px py : ℝ) :
    bandProjectorOperator .lower v m px py +
        bandProjectorOperator .upper v m px py = 1 := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (bandProjector .lower v m px py) +
      φ (bandProjector .upper v m px py) = 1
  simpa using congrArg φ (bandProjector_lower_add_upper v m px py)

/-- Operator projectors remain idempotent after transport from `2 × 2` matrices. -/
theorem bandProjectorOperator_mul_self
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator band v m px py * bandProjectorOperator band v m px py =
      bandProjectorOperator band v m px py := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (bandProjector band v m px py) * φ (bandProjector band v m px py) =
    φ (bandProjector band v m px py)
  simpa using congrArg φ (bandProjector_mul_self band v m px py hE)

/-- Lower then upper operator projectors are orthogonal away from the Dirac degeneracy. -/
theorem bandProjectorOperator_lower_mul_upper
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator .lower v m px py * bandProjectorOperator .upper v m px py = 0 := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (bandProjector .lower v m px py) * φ (bandProjector .upper v m px py) = 0
  simpa using congrArg φ (bandProjector_lower_mul_upper v m px py hE)

/-- Upper then lower operator projectors are orthogonal away from the Dirac degeneracy. -/
theorem bandProjectorOperator_upper_mul_lower
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator .upper v m px py * bandProjectorOperator .lower v m px py = 0 := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (bandProjector .upper v m px py) * φ (bandProjector .lower v m px py) = 0
  simpa using congrArg φ (bandProjector_upper_mul_lower v m px py hE)

/-- The Hamiltonian acts on each operator projector with its band energy. -/
theorem hamiltonianOperator_mul_bandProjectorOperator
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    hamiltonianOperator v m px py * bandProjectorOperator band v m px py =
      (((bandEnergy band v m px py : ℝ) : ℂ)) •
        bandProjectorOperator band v m px py := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (hamiltonian v m px py) * φ (bandProjector band v m px py) =
      (((bandEnergy band v m px py : ℝ) : ℂ)) • φ (bandProjector band v m px py)
  simpa only [map_mul, map_smul] using
    congrArg φ (hamiltonian_mul_bandProjector band v m px py hE)

private theorem shiftedHamiltonian_mul_bandProjectorOperator
    (z : ℂ) (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert) z - hamiltonianOperator v m px py) *
        bandProjectorOperator band v m px py =
      (z - ((bandEnergy band v m px py : ℝ) : ℂ)) •
        bandProjectorOperator band v m px py := by
  rw [sub_mul]
  rw [hamiltonianOperator_mul_bandProjectorOperator band v m px py hE]
  simp [Algebra.algebraMap_eq_smul_one, sub_smul]

/-- Scalar coefficient of band `band` in the gauge-free projector resolvent at spectral parameter
`z`. -/
noncomputable def projectorResolventCoefficient
    (z : ℂ) (band : Band) (v m px py : ℝ) : ℂ :=
  (z - ((bandEnergy band v m px py : ℝ) : ℂ))⁻¹

/-- The scalar projector-resolvent coefficient is continuous wherever its spectral denominator is
nonzero. -/
theorem continuousAt_projectorResolventCoefficient
    (z : ℂ) (band : Band) (v m px py : ℝ)
    (hden : z - ((bandEnergy band v m px py : ℝ) : ℂ) ≠ 0) :
    ContinuousAt
      (fun w : ℂ => projectorResolventCoefficient w band v m px py)
      z := by
  unfold projectorResolventCoefficient
  exact (continuousAt_id.sub continuousAt_const).inv₀ hden

/-- Gauge-free two-band spectral candidate for the resolvent of the massive-Dirac Hamiltonian. -/
noncomputable def projectorResolvent
    (z : ℂ) (v m px py : ℝ) : DiracHilbert →L[ℂ] DiracHilbert :=
  (z - ((bandEnergy .lower v m px py : ℝ) : ℂ))⁻¹ •
      bandProjectorOperator .lower v m px py +
    (z - ((bandEnergy .upper v m px py : ℝ) : ℂ))⁻¹ •
      bandProjectorOperator .upper v m px py

/-- The projector resolvent written using the named scalar band coefficients. -/
theorem projectorResolvent_eq_coefficients
    (z : ℂ) (v m px py : ℝ) :
    projectorResolvent z v m px py =
      projectorResolventCoefficient z .lower v m px py •
          bandProjectorOperator .lower v m px py +
        projectorResolventCoefficient z .upper v m px py •
          bandProjectorOperator .upper v m px py := by
  rfl

/-- Squaring the two-band projector resolvent squares only its scalar spectral coefficients. -/
theorem projectorResolvent_sq
    (z : ℂ) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    projectorResolvent z v m px py ^ 2 =
      projectorResolventCoefficient z .lower v m px py ^ 2 •
          bandProjectorOperator .lower v m px py +
        projectorResolventCoefficient z .upper v m px py ^ 2 •
          bandProjectorOperator .upper v m px py := by
  rw [projectorResolvent_eq_coefficients, pow_two]
  rw [add_mul, mul_add, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [bandProjectorOperator_mul_self .lower v m px py hE]
  rw [bandProjectorOperator_mul_self .upper v m px py hE]
  rw [bandProjectorOperator_lower_mul_upper v m px py hE]
  rw [bandProjectorOperator_upper_mul_lower v m px py hE]
  simp [pow_two]

private theorem shiftedHamiltonian_mul_projectorResolvent
    (z : ℂ) (v m px py : ℝ) (hE : energy v m px py ≠ 0)
    (hlower : z - ((bandEnergy .lower v m px py : ℝ) : ℂ) ≠ 0)
    (hupper : z - ((bandEnergy .upper v m px py : ℝ) : ℂ) ≠ 0) :
    (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert) z - hamiltonianOperator v m px py) *
        projectorResolvent z v m px py = 1 := by
  rw [projectorResolvent, mul_add]
  rw [mul_smul_comm, mul_smul_comm]
  rw [shiftedHamiltonian_mul_bandProjectorOperator z .lower v m px py hE]
  rw [shiftedHamiltonian_mul_bandProjectorOperator z .upper v m px py hE]
  rw [smul_smul, smul_smul]
  simp only [inv_mul_cancel₀ hlower, inv_mul_cancel₀ hupper, one_smul]
  exact bandProjectorOperator_lower_add_upper v m px py

/-- The regulated massive-Dirac resolvent equals the gauge-free two-projector expansion for any
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

end AnomalousHall.MassiveDirac
