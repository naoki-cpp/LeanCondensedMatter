import LeanCondensedMatter.Transport.Analysis.PolarFourier
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder.FiniteBroadeningBornPropagator

set_option linter.style.header false

/-!
# Finite-cutoff real-space Born-Dyson propagator

This module owns the real-space representation of the finite-cutoff finite-broadening Born-Dyson
Green matrix. The matrix Fourier transform is performed entrywise through the generic two-dimensional
physical-momentum polar Fourier transform, so the factor `d²p / (2πℏ)²` is already included in every
real-space Green block.

No crossed-diagram topology, current vertex, real-space integration, cutoff removal, Bessel reduction,
or conductivity normalization is introduced here.
-/

namespace QuantumTheory.Transport.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Finite-cutoff finite-`η` real-space Born-Dyson Green matrix. -/
noncomputable def finiteCutoffContinuumBornDysonRealSpaceGreenMatrix
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax : ℝ)
    (r : Fin 2 → ℝ) : Matrix2 :=
  fun i j =>
    finiteCutoffPhysicalMomentumPolarFourier hbar pMax
      (fun p θ =>
        finiteCutoffContinuumBornDysonGreenMatrix
          side v m (p * Real.cos θ) (p * Real.sin θ)
          probeEnergy broadening disorderStrength hbar pMax i j)
      r

end

end QuantumTheory.Transport.Models.MassiveDirac
