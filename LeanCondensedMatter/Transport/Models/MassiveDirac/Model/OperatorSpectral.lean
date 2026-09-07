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
G(z) = ∑ₙ (z - Eₙ)⁻¹ Pₙ
```

is a left inverse of `z I - H₀`. The operator-projector algebra, direction-indexed current band
blocks, and finite-band scalar coefficient form of that spectral expansion, including its square and
arbitrary nonzero signed-regulator realization, are therefore model-level spectral infrastructure.
Kubo–Bastin, Středa, propagator, and disorder consumers remain downstream.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- A massive-Dirac band projector transported to the bounded-operator representation used by the
transport stack. -/
noncomputable def bandProjectorOperator (band : Band) (v m px py : ℝ) :
    DiracHilbert →L[ℂ] DiracHilbert :=
  matrixOperator (bandProjector band v m px py)

/-- Ordered current band block `Tr(P_target j_μ P_source j_ν)` in the bounded-operator model. -/
noncomputable def currentBandBlockTrace
    (μ ν : Direction2) (source target : Band) (e v m px py : ℝ) : ℂ :=
  finiteDimensionalOperatorTrace
    (bandProjectorOperator target v m px py * currentOperator μ e v *
      bandProjectorOperator source v m px py * currentOperator ν e v)

/-- The finite sum of operator band projectors resolves the identity. -/
theorem sum_bandProjectorOperator_eq_one (v m px py : ℝ) :
    ∑ band : Band, bandProjectorOperator band v m px py = 1 := by
  simp only [sum_band]
  unfold bandProjectorOperator matrixOperator
  rw [← map_add]
  rw [show
    bandProjector .lower v m px py + bandProjector .upper v m px py = 1 by
      simpa only [sum_band] using sum_bandProjector_eq_one v m px py]
  rw [map_one]

/-- Operator projectors remain idempotent after transport from `2 × 2` matrices. -/
theorem bandProjectorOperator_mul_self
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator band v m px py * bandProjectorOperator band v m px py =
      bandProjectorOperator band v m px py := by
  simpa [bandProjectorOperator, matrixOperator] using
    congrArg matrixOperator (bandProjector_mul_self band v m px py hE)

/-- Opposite-band operator projectors are orthogonal away from the Dirac degeneracy. -/
theorem bandProjectorOperator_mul_oppositeBand
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    bandProjectorOperator band v m px py *
        bandProjectorOperator (oppositeBand band) v m px py = 0 := by
  simpa [bandProjectorOperator, matrixOperator] using
    congrArg matrixOperator (bandProjector_mul_oppositeBand band v m px py hE)

/-- The Hamiltonian acts on each operator projector with its band energy. -/
theorem hamiltonianOperator_mul_bandProjectorOperator
    (band : Band) (v m px py : ℝ) (hE : energy v m px py ≠ 0) :
    hamiltonianOperator v m px py * bandProjectorOperator band v m px py =
      (((bandEnergy band v m px py : ℝ) : ℂ)) •
        bandProjectorOperator band v m px py := by
  unfold hamiltonianOperator bandProjectorOperator matrixOperator
  rw [← map_mul, hamiltonian_mul_bandProjector band v m px py hE, map_smul]

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
  have hlu :
      bandProjectorOperator .lower v m px py * bandProjectorOperator .upper v m px py = 0 := by
    simpa using bandProjectorOperator_mul_oppositeBand .lower v m px py hE
  have hul :
      bandProjectorOperator .upper v m px py * bandProjectorOperator .lower v m px py = 0 := by
    simpa using bandProjectorOperator_mul_oppositeBand .upper v m px py hE
  simp only [projectorResolvent, sum_band]
  rw [pow_two, add_mul, mul_add, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [bandProjectorOperator_mul_self .lower v m px py hE]
  rw [bandProjectorOperator_mul_self .upper v m px py hE]
  rw [hlu, hul]
  simp [pow_two]

private theorem shiftedHamiltonian_mul_projectorResolvent
    (z : ℂ) (v m px py : ℝ) (hE : energy v m px py ≠ 0)
    (hlower : z - ((bandEnergy .lower v m px py : ℝ) : ℂ) ≠ 0)
    (hupper : z - ((bandEnergy .upper v m px py : ℝ) : ℂ) ≠ 0) :
    (algebraMap ℂ (DiracHilbert →L[ℂ] DiracHilbert) z - hamiltonianOperator v m px py) *
        projectorResolvent z v m px py = 1 := by
  simp only [projectorResolvent, sum_band]
  rw [mul_add, mul_smul_comm, mul_smul_comm]
  rw [shiftedHamiltonian_mul_bandProjectorOperator z .lower v m px py hE]
  rw [shiftedHamiltonian_mul_bandProjectorOperator z .upper v m px py hE]
  rw [smul_smul, smul_smul]
  simp only [projectorResolventCoefficient, inv_mul_cancel₀ hlower, inv_mul_cancel₀ hupper, one_smul]
  simpa only [sum_band] using sum_bandProjectorOperator_eq_one v m px py

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

end QuantumTheory.Transport.Models.MassiveDirac
