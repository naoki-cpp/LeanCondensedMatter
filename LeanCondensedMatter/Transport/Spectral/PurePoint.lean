import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann
import LeanCondensedMatter.Transport.Resolvent.Spectral

set_option linter.style.header false

/-!
# Pure-point spectral adapter for regulated resolvents

This module is the neutral seam between generic signed-regulator resolvent algebra and supplied
pure-point Lehmann response data. It is shared by Kubo–Bastin and Středa consumers so neither
response representation owns or duplicates the basis-action proof.

The arbitrary-regulator eigenvector action remains in `Transport.Resolvent.Spectral`; only results
whose statements require `PurePointLehmannData` live here.
-/

namespace QuantumTheory
namespace Transport

open QuantumTheory.LinearResponse

noncomputable section

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable
  (system : BoundedFreeSystem H)
  (data : PurePointLehmannData system ι)

/-- A resolvent with arbitrary nonzero signed regulator acts diagonally on the supplied pure-point
energy basis. -/
theorem resolvent_spectralParameterOfRegulator_apply_purePointBasis_at_energy
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (n : ι) :
    resolvent system.hamiltonian.1 (spectralParameterOfRegulator energy regulator)
        (data.basis n) =
      (spectralParameterOfRegulator energy regulator - (data.energy n : ℂ))⁻¹ • data.basis n := by
  exact resolvent_spectralParameterOfRegulator_apply_eigenvector
    system.hamiltonian.1 system.hamiltonian.2
    (data.hamiltonian_apply_basis n) energy regulator hregulator

/-- The canonical side-indexed spectral resolvent acts diagonally on the supplied pure-point energy
basis at nonzero physical broadening. -/
theorem spectralResolvent_apply_purePointBasis_at_energy
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) (n : ι) :
    spectralResolvent side system.hamiltonian.1 energy broadening (data.basis n) =
      (spectralParameter side energy broadening - (data.energy n : ℂ))⁻¹ • data.basis n := by
  simpa only [spectralResolvent, spectralParameter] using
    resolvent_spectralParameterOfRegulator_apply_purePointBasis_at_energy
      system data energy (side.regulator broadening)
      (side.regulator_ne_zero hbroadening) n

/-- On a pure-point energy basis, the square of a resolvent with arbitrary nonzero signed regulator
has the squared scalar denominator. -/
theorem resolvent_spectralParameterOfRegulator_sq_apply_purePointBasis_at_energy
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) (n : ι) :
    ((resolvent system.hamiltonian.1 (spectralParameterOfRegulator energy regulator)) ^ 2)
        (data.basis n) =
      ((spectralParameterOfRegulator energy regulator - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  rw [pow_two]
  change resolvent system.hamiltonian.1 (spectralParameterOfRegulator energy regulator)
      (resolvent system.hamiltonian.1 (spectralParameterOfRegulator energy regulator)
        (data.basis n)) = _
  rw [resolvent_spectralParameterOfRegulator_apply_purePointBasis_at_energy
    system data energy regulator hregulator n]
  rw [map_smul]
  rw [resolvent_spectralParameterOfRegulator_apply_purePointBasis_at_energy
    system data energy regulator hregulator n]
  rw [smul_smul, pow_two]

/-- The square of the canonical side-indexed spectral resolvent acts diagonally with the squared
side-indexed scalar denominator at nonzero physical broadening. -/
theorem spectralResolvent_sq_apply_purePointBasis_at_energy
    (side : SpectralSide) (energy broadening : ℝ) (hbroadening : broadening ≠ 0) (n : ι) :
    ((spectralResolvent side system.hamiltonian.1 energy broadening) ^ 2) (data.basis n) =
      ((spectralParameter side energy broadening - (data.energy n : ℂ))⁻¹) ^ 2 •
        data.basis n := by
  simpa only [spectralResolvent, spectralParameter] using
    resolvent_spectralParameterOfRegulator_sq_apply_purePointBasis_at_energy
      system data energy (side.regulator broadening)
      (side.regulator_ne_zero hbroadening) n

end
end Transport
end QuantumTheory
