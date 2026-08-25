import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Response
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model.Spectral
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Gauge-free spectral resolvent for the massive Dirac model

The generic transport layer defines retarded and advanced Green operators as algebraic resolvents
of bounded self-adjoint operators.  The massive-Dirac model already has explicit gauge-independent
rank-one band projectors `P₋` and `P₊`.  This file connects those two descriptions directly, without
choosing eigenvectors or constructing `PurePointLehmannData`.

Away from the band degeneracy,

```text
G(z) = (z - E₋)⁻¹ P₋ + (z - E₊)⁻¹ P₊
```

is a left inverse of `z I - H₀`.  This module also owns the operator-projector algebra and scalar
coefficient form of that spectral expansion, including its square. At positive retarded/advanced
broadening the generic resolvent is the corresponding two-projector expansion. This is the spectral
bridge needed before expanding the Bastin/Středa trace into interband projector traces and comparing
it with Berry curvature.
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
  calc
    φ (bandProjector band v m px py) * φ (bandProjector band v m px py) =
        φ (bandProjector band v m px py * bandProjector band v m px py) := by
      symm
      exact map_mul φ _ _
    _ = φ (bandProjector band v m px py) := by
      rw [bandProjector_mul_self band v m px py hE]

/-- Lower then upper operator projectors are orthogonal away from the Dirac degeneracy. -/
theorem bandProjectorOperator_lower_mul_upper
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator .lower v m px py * bandProjectorOperator .upper v m px py = 0 := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (bandProjector .lower v m px py) * φ (bandProjector .upper v m px py) = 0
  calc
    φ (bandProjector .lower v m px py) * φ (bandProjector .upper v m px py) =
        φ (bandProjector .lower v m px py * bandProjector .upper v m px py) := by
      symm
      exact map_mul φ _ _
    _ = 0 := by rw [bandProjector_lower_mul_upper v m px py hE, map_zero]

/-- Upper then lower operator projectors are orthogonal away from the Dirac degeneracy. -/
theorem bandProjectorOperator_upper_mul_lower
    (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator .upper v m px py * bandProjectorOperator .lower v m px py = 0 := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (bandProjector .upper v m px py) * φ (bandProjector .lower v m px py) = 0
  calc
    φ (bandProjector .upper v m px py) * φ (bandProjector .lower v m px py) =
        φ (bandProjector .upper v m px py * bandProjector .lower v m px py) := by
      symm
      exact map_mul φ _ _
    _ = 0 := by rw [bandProjector_upper_mul_lower v m px py hE, map_zero]

/-- The Hamiltonian acts on each operator projector with its band energy. -/
theorem hamiltonianOperator_mul_bandProjectorOperator
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    hamiltonianOperator v m px py * bandProjectorOperator band v m px py =
      (((bandEnergy band v m px py : ℝ) : ℂ)) •
        bandProjectorOperator band v m px py := by
  let φ : Matrix2 ≃⋆ₐ[ℂ] (DiracHilbert →L[ℂ] DiracHilbert) := Matrix.toEuclideanCLM
  change φ (hamiltonian v m px py) * φ (bandProjector band v m px py) =
      (((bandEnergy band v m px py : ℝ) : ℂ)) • φ (bandProjector band v m px py)
  calc
    φ (hamiltonian v m px py) * φ (bandProjector band v m px py) =
        φ (hamiltonian v m px py * bandProjector band v m px py) := by
      symm
      exact map_mul φ _ _
    _ = φ ((((bandEnergy band v m px py : ℝ) : ℂ)) •
        bandProjector band v m px py) := by
      rw [hamiltonian_mul_bandProjector band v m px py hE]
    _ = (((bandEnergy band v m px py : ℝ) : ℂ)) •
        φ (bandProjector band v m px py) := by
      exact map_smul φ _ _

/-- Multiplying one spectral projector by the shifted Hamiltonian gives its scalar spectral
factor. -/
theorem shiftedHamiltonian_mul_bandProjectorOperator
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

/-- If the spectral parameter misses both bands, the projector expansion is a left inverse of
`z I - H₀`. -/
theorem shiftedHamiltonian_mul_projectorResolvent
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

/-- Positive retarded broadening keeps the spectral parameter away from either real band energy. -/
theorem retardedSpectralParameter_sub_bandEnergy_ne_zero
    (band : Band) (v m px py probeEnergy broadening : ℝ) (hbroadening : 0 < broadening) :
    retardedSpectralParameter probeEnergy broadening -
        ((bandEnergy band v m px py : ℝ) : ℂ) ≠ 0 := by
  intro hzero
  have him : broadening = 0 := by
    simpa [retardedSpectralParameter] using congrArg Complex.im hzero
  exact (ne_of_gt hbroadening) him

/-- Positive advanced broadening keeps the spectral parameter away from either real band energy. -/
theorem advancedSpectralParameter_sub_bandEnergy_ne_zero
    (band : Band) (v m px py probeEnergy broadening : ℝ) (hbroadening : 0 < broadening) :
    advancedSpectralParameter probeEnergy broadening -
        ((bandEnergy band v m px py : ℝ) : ℂ) ≠ 0 := by
  intro hzero
  have him : broadening = 0 := by
    simpa [advancedSpectralParameter] using congrArg Complex.im hzero
  exact (ne_of_gt hbroadening) him

/-- The generic retarded resolvent equals the gauge-free two-projector spectral expansion. -/
theorem retardedResolvent_eq_projectorResolvent
    (v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
      projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py := by
  let shift : DiracHilbert →L[ℂ] DiracHilbert :=
    algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
        (retardedSpectralParameter probeEnergy broadening) - hamiltonianOperator v m px py
  let candidate := projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py
  have hleft : shift * candidate = 1 := by
    exact shiftedHamiltonian_mul_projectorResolvent
      (retardedSpectralParameter probeEnergy broadening) v m px py hE
      (retardedSpectralParameter_sub_bandEnergy_ne_zero
        .lower v m px py probeEnergy broadening hbroadening)
      (retardedSpectralParameter_sub_bandEnergy_ne_zero
        .upper v m px py probeEnergy broadening hbroadening)
  have hright :
      retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening * shift = 1 := by
    exact resolvent_mul_retardedShift
      (hamiltonianOperator v m px py)
      (hamiltonianOperator_isSelfAdjoint v m px py)
      probeEnergy broadening hbroadening
  calc
    retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
        retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening * 1 := by simp
    _ = retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening *
        (shift * candidate) := by rw [hleft]
    _ = (retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening * shift) *
        candidate := by rw [mul_assoc]
    _ = candidate := by rw [hright, one_mul]
    _ = projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py := rfl

/-- The generic advanced resolvent equals the same projector expansion at the advanced spectral
parameter. -/
theorem advancedResolvent_eq_projectorResolvent
    (v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
      projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py := by
  let shift : DiracHilbert →L[ℂ] DiracHilbert :=
    algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
        (advancedSpectralParameter probeEnergy broadening) - hamiltonianOperator v m px py
  let candidate := projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py
  have hleft : shift * candidate = 1 := by
    exact shiftedHamiltonian_mul_projectorResolvent
      (advancedSpectralParameter probeEnergy broadening) v m px py hE
      (advancedSpectralParameter_sub_bandEnergy_ne_zero
        .lower v m px py probeEnergy broadening hbroadening)
      (advancedSpectralParameter_sub_bandEnergy_ne_zero
        .upper v m px py probeEnergy broadening hbroadening)
  have hright :
      advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening * shift = 1 := by
    exact resolvent_mul_advancedShift
      (hamiltonianOperator v m px py)
      (hamiltonianOperator_isSelfAdjoint v m px py)
      probeEnergy broadening hbroadening
  calc
    advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
        advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening * 1 := by simp
    _ = advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening *
        (shift * candidate) := by rw [hleft]
    _ = (advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening * shift) *
        candidate := by rw [mul_assoc]
    _ = candidate := by rw [hright, one_mul]
    _ = projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py := rfl

end

end AnomalousHall.MassiveDirac
