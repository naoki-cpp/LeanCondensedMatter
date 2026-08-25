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

/-- Nonzero broadening keeps either side-indexed spectral parameter away from every real band
energy. -/
theorem spectralParameter_sub_bandEnergy_ne_zero
    (side : SpectralSide) (band : Band) (v m px py probeEnergy broadening : ℝ)
    (hbroadening : broadening ≠ 0) :
    spectralParameter side probeEnergy broadening -
        ((bandEnergy band v m px py : ℝ) : ℂ) ≠ 0 := by
  intro hzero
  have him : side.sign * broadening = 0 := by
    simpa using congrArg Complex.im hzero
  exact (mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening) him

/-- The generic resolvent on either spectral side equals the gauge-free two-projector expansion. -/
theorem resolvent_spectralParameter_eq_projectorResolvent
    (side : SpectralSide) (v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : broadening ≠ 0) :
    resolvent (hamiltonianOperator v m px py) (spectralParameter side probeEnergy broadening) =
      projectorResolvent (spectralParameter side probeEnergy broadening) v m px py := by
  let shift : DiracHilbert →L[ℂ] DiracHilbert :=
    algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert)
        (spectralParameter side probeEnergy broadening) - hamiltonianOperator v m px py
  let candidate := projectorResolvent (spectralParameter side probeEnergy broadening) v m px py
  have hleft : shift * candidate = 1 := by
    exact shiftedHamiltonian_mul_projectorResolvent
      (spectralParameter side probeEnergy broadening) v m px py hE
      (spectralParameter_sub_bandEnergy_ne_zero
        side .lower v m px py probeEnergy broadening hbroadening)
      (spectralParameter_sub_bandEnergy_ne_zero
        side .upper v m px py probeEnergy broadening hbroadening)
  have hright :
      resolvent (hamiltonianOperator v m px py) (spectralParameter side probeEnergy broadening) *
          shift = 1 := by
    exact resolvent_mul_spectralShift
      side (hamiltonianOperator v m px py)
      (hamiltonianOperator_isSelfAdjoint v m px py)
      probeEnergy broadening hbroadening
  calc
    resolvent (hamiltonianOperator v m px py) (spectralParameter side probeEnergy broadening) =
        resolvent (hamiltonianOperator v m px py) (spectralParameter side probeEnergy broadening) *
          1 := by simp
    _ = resolvent (hamiltonianOperator v m px py) (spectralParameter side probeEnergy broadening) *
        (shift * candidate) := by rw [hleft]
    _ = (resolvent (hamiltonianOperator v m px py) (spectralParameter side probeEnergy broadening) *
        shift) * candidate := by rw [mul_assoc]
    _ = candidate := by rw [hright, one_mul]
    _ = projectorResolvent (spectralParameter side probeEnergy broadening) v m px py := rfl

/-- The generic retarded resolvent equals the gauge-free two-projector spectral expansion. -/
theorem retardedResolvent_eq_projectorResolvent
    (v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    retardedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
      projectorResolvent (retardedSpectralParameter probeEnergy broadening) v m px py := by
  simpa only [retardedResolvent, spectralParameter_retarded] using
    resolvent_spectralParameter_eq_projectorResolvent .retarded
      v m px py probeEnergy broadening hE (ne_of_gt hbroadening)

/-- The generic advanced resolvent equals the same projector expansion at the advanced spectral
parameter. -/
theorem advancedResolvent_eq_projectorResolvent
    (v m px py probeEnergy broadening : ℝ)
    (hE : energy v m px py ≠ 0) (hbroadening : 0 < broadening) :
    advancedResolvent (hamiltonianOperator v m px py) probeEnergy broadening =
      projectorResolvent (advancedSpectralParameter probeEnergy broadening) v m px py := by
  simpa only [advancedResolvent, spectralParameter_advanced] using
    resolvent_spectralParameter_eq_projectorResolvent .advanced
      v m px py probeEnergy broadening hE (ne_of_gt hbroadening)

end

end AnomalousHall.MassiveDirac
