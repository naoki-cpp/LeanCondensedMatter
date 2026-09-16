import LeanCondensedMatter.Transport.Core.ContinuumMeasure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Two-dimensional polar Fourier transform

This module owns the representation-independent scalar Fourier transform used when a two-dimensional
physical-momentum integral is written in polar coordinates with a finite radial cutoff. The transform
includes the physical continuum normalization `d²p / (2πℏ)²` and the polar Jacobian `p`, while the
consumer supplies the momentum-space scalar field.

No model Hamiltonian, matrix representation, disorder approximation, real-space cutoff, Bessel
reduction, or conductivity normalization is introduced here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

open MeasureTheory
open scoped Interval

/-- Fourier phase `exp(i p·r / ℏ)` for polar momentum `(p cos θ, p sin θ)` in two dimensions. -/
def physicalMomentumPolarFourierPhase
    (hbar p θ : ℝ) (r : Fin 2 → ℝ) : ℂ :=
  Complex.exp
    (Complex.I *
      (((p * (r 0 * Real.cos θ + r 1 * Real.sin θ) / hbar : ℝ) : ℂ)))

/-- Finite-cutoff polar Fourier transform of a complex scalar momentum field with the physical
momentum measure `d²p / (2πℏ)²` included exactly once. -/
noncomputable def finiteCutoffPhysicalMomentumPolarFourier
    (hbar pMax : ℝ) (field : ℝ → ℝ → ℂ) (r : Fin 2 → ℝ) : ℂ :=
  (((momentumMeasurePrefactor hbar : ℝ) : ℂ)) *
    ∫ p in (0 : ℝ)..pMax,
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        ((p : ℂ) * physicalMomentumPolarFourierPhase hbar p θ r) * field p θ

end

end Transport
end QuantumTheory
