import LeanCondensedMatter.Transport.Resolvent.Basic
import Mathlib.Analysis.Complex.RealDeriv

set_option linter.style.header false

/-!
# Real-energy derivatives of signed-regulator resolvents

The representation-independent holomorphic identity

```text
dG(z) / dz = -G(z)^2
```

is owned by `Analysis.Operator.Spectral.Resolvent`. The Středa energy integral instead
differentiates real-energy paths at fixed imaginary regulator. This module records that the
signed-regulator spectral parameter `E ↦ E + iγ` has derivative one and proves the corresponding
resolvent derivative and continuity directly for arbitrary nonzero `γ`. Physical retarded and
advanced consumers specialize `γ` at their use sites.

The result remains dimension-independent and contains no trace, conductivity, zero-broadening,
or thermodynamic-limit statement.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Along the real-energy axis, a spectral parameter with fixed signed regulator has derivative one. -/
theorem hasDerivAt_spectralParameterOfRegulator_energy
    (energy regulator : ℝ) :
    HasDerivAt (fun x : ℝ => spectralParameterOfRegulator x regulator)
      (1 : ℂ) energy := by
  simpa [spectralParameterOfRegulator] using
    (Complex.ofRealCLM.hasDerivAt.add_const ((regulator : ℂ) * Complex.I))

/-- A resolvent at fixed nonzero signed regulator differentiates to minus its square along the real
energy axis. -/
theorem hasDerivAt_resolvent_spectralParameterOfRegulator_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    HasDerivAt
      (fun x : ℝ => resolvent hamiltonian (spectralParameterOfRegulator x regulator))
      (-(resolvent hamiltonian (spectralParameterOfRegulator energy regulator)) ^ 2)
      energy := by
  have hresolvent :
      HasDerivAt (resolvent hamiltonian)
        (-(resolvent hamiltonian (spectralParameterOfRegulator energy regulator)) ^ 2)
        (spectralParameterOfRegulator energy regulator) := by
    exact spectrum.hasDerivAt_resolvent_const_left
      (spectrum.notMem_iff.mp
        (QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
          hamiltonian hself (spectralParameterOfRegulator energy regulator)
          (by
            rw [spectralParameterOfRegulator_im]
            exact hregulator)))
  have hcomp := hresolvent.scomp energy
    (hasDerivAt_spectralParameterOfRegulator_energy energy regulator)
  change HasDerivAt
    (resolvent hamiltonian ∘ fun x : ℝ => spectralParameterOfRegulator x regulator)
    (-(resolvent hamiltonian (spectralParameterOfRegulator energy regulator)) ^ 2)
    energy
  simpa only [one_smul] using hcomp

/-- At fixed nonzero signed regulator, the resolvent is continuous along the real-energy axis. -/
theorem continuous_resolvent_spectralParameterOfRegulator_energy
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (regulator : ℝ) (hregulator : regulator ≠ 0) :
    Continuous (fun energy : ℝ =>
      resolvent hamiltonian (spectralParameterOfRegulator energy regulator)) := by
  rw [continuous_iff_continuousAt]
  intro energy
  exact
    (hasDerivAt_resolvent_spectralParameterOfRegulator_energy
      hamiltonian hself energy regulator hregulator).continuousAt

end

end QuantumTheory.Transport
