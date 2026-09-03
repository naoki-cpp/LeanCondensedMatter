import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.FiniteToys

set_option linter.style.header false

/-!
# Explicit nonzero evaluation of the two-level transport toy

The foundation toy model supplies a degenerate two-level Hamiltonian and an independently chosen
identity current. This module evaluates its canonical finite pure-point Bastin trace at the concrete
regularized point `E = 1`, `γ = 1`.

The result is the nonzero value `-2`. It therefore checks the overall retarded/advanced sign and the
multiplicity of the two-level trace independently of the abstract Bastin/Středa decomposition. The
same value is then transferred to the Středa surface-plus-sea side by the proved pointwise identity.
No numerical approximation, disorder average, or limiting procedure is used.
-/

namespace SecondQuantization
namespace Fermionic
namespace Validation

open scoped BigOperators
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

/-- Inner products of the supplied two-level pure-point basis are Kronecker deltas. -/
@[simp]
theorem twoLevelData_inner_basis (m n : Fin 2) :
    inner ℂ (twoLevelData.basis m) (twoLevelData.basis n) =
      if m = n then 1 else 0 :=
  orthonormal_iff_ite.mp twoLevelData.basis.orthonormal m n

/-- Closed scalar form of the canonical Bastin spectral trace for the identity-current two-level
toy. Both levels have the same zero energy, so the outer trace contributes the explicit factor two. -/
theorem twoLevel_scalarCurrent_spectralTraceSum
    (energy broadening : ℝ) :
    regularizedBastinSpectralTraceSum
        twoLevelSystem twoLevelData
        twoLevelScalarCurrent twoLevelScalarCurrent energy broadening =
      2 *
        ((retardedSpectralParameter energy broadening)⁻¹ -
          (advancedSpectralParameter energy broadening)⁻¹) *
        (((retardedSpectralParameter energy broadening)⁻¹) ^ 2 -
          ((advancedSpectralParameter energy broadening)⁻¹) ^ 2) := by
  classical
  simp [regularizedBastinSpectralTraceSum, stredaSpectralFactor,
    retardedSpectralParameter, advancedSpectralParameter, twoLevelScalarCurrent]
  ring

/-- At `E = 1` and `γ = 1`, the two-level scalar-current spectral trace is exactly `-2`. -/
theorem twoLevel_scalarCurrent_spectralTraceSum_one_one :
    regularizedBastinSpectralTraceSum
        twoLevelSystem twoLevelData
        twoLevelScalarCurrent twoLevelScalarCurrent 1 1 = -2 := by
  rw [twoLevel_scalarCurrent_spectralTraceSum]
  apply Complex.ext
  · norm_num [retardedSpectralParameter, advancedSpectralParameter,
      Complex.normSq, pow_two]
  · norm_num [retardedSpectralParameter, advancedSpectralParameter,
      Complex.normSq, pow_two]

/-- The canonical ordinary-trace Bastin integrand has the same explicit nonzero value. -/
theorem twoLevel_scalarCurrent_bastinTrace_one_one :
    regularizedBastinTraceIntegrand
        twoLevelSystem.hamiltonian.1
        twoLevelScalarCurrent twoLevelScalarCurrent 1 1 = -2 := by
  rw [regularizedBastinTraceIntegrand_eq_spectral_sum
    twoLevelSystem twoLevelData twoLevelScalarCurrent twoLevelScalarCurrent 1 1 (by norm_num)]
  exact twoLevel_scalarCurrent_spectralTraceSum_one_one

/-- The corresponding Středa surface-derivative plus residual-sea trace evaluates to the same
nonzero value, giving a concrete sign check of the pointwise decomposition. -/
theorem twoLevel_scalarCurrent_streda_sum_one_one :
    regularizedStredaSurfacePrimitiveTraceDerivative
        twoLevelSystem.hamiltonian.1
        twoLevelScalarCurrent twoLevelScalarCurrent 1 1 +
      regularizedStredaResidualSeaTraceKernel
        twoLevelSystem.hamiltonian.1
        twoLevelScalarCurrent twoLevelScalarCurrent 1 1 = -2 := by
  rw [← twoLevel_scalarCurrent_bastin_eq_streda]
  exact twoLevel_scalarCurrent_bastinTrace_one_one

end
end Validation
end Fermionic
end SecondQuantization
