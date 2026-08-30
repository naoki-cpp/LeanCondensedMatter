import LeanCondensedMatter.Transport.Resolvent.EnergyDerivative
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Real-energy derivative of a dressed Green operator

For an energy-dependent self-energy `Σ(E)`, define the dressed spectral shift

```text
Sˢ(E) = zˢ(E, η) I - H - Σ(E).
```

If a differentiable Green family is the inverse of this shift, differentiating
`Sˢ(E) Gˢ(E) = I` and using the opposite inverse identity gives

```text
∂E Gˢ = -Gˢ (I - ∂E Σ) Gˢ.
```

This module keeps that family-level calculus separate from the pointwise algebraic
`IsSelfEnergy` relation and from the clean identity `∂E G₀ˢ = -(G₀ˢ)^2`. It does not identify any
Born or SCBA approximation with an exact disorder average and does not assert differentiability for
a supplied approximation family; differentiability is an explicit hypothesis.
-/

namespace QuantumTheory.Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Side-indexed dressed spectral shift
`Sˢ(E) = zˢ(E,η) I - H - Σ(E)` for an energy-dependent self-energy family. -/
noncomputable def dressedSpectralShift
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H)
    (selfEnergy : ℝ → H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
    hamiltonian - selfEnergy energy

/-- Along the real-energy axis, the dressed spectral shift has derivative `I - ∂E Σ`. -/
theorem hasDerivAt_dressedSpectralShift_energy
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H)
    (selfEnergy : ℝ → H →L[ℂ] H)
    (energy broadening : ℝ) (selfEnergyDerivative : H →L[ℂ] H)
    (hselfEnergy : HasDerivAt selfEnergy selfEnergyDerivative energy) :
    HasDerivAt
      (fun x : ℝ => dressedSpectralShift side hamiltonian selfEnergy x broadening)
      (1 - selfEnergyDerivative) energy := by
  have hspectral := hasDerivAt_spectralParameter_energy side energy broadening
  have halgebraMap :
      HasDerivAt
        (fun x : ℝ =>
          algebraMap ℂ (H →L[ℂ] H) (spectralParameter side x broadening))
        (1 : H →L[ℂ] H) energy := by
    simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
      hspectral.smul_const (1 : H →L[ℂ] H)
  change HasDerivAt
    (((fun x : ℝ =>
        algebraMap ℂ (H →L[ℂ] H) (spectralParameter side x broadening)) -
      fun _ : ℝ => hamiltonian) - selfEnergy)
    (1 - selfEnergyDerivative) energy
  simpa only [sub_zero] using
    (halgebraMap.sub (hasDerivAt_const energy hamiltonian)).sub hselfEnergy

/-- The derivative of a differentiable inverse Green family is
`-Gˢ (I - ∂E Σ) Gˢ`.

The left inverse identity is required for the whole supplied energy family so that it can be
differentiated. The opposite inverse identity is needed only at the target energy to isolate the
Green derivative. No self-adjointness or nonzero-broadening assumption is required beyond these
explicit inverse hypotheses. -/
theorem hasDerivAt_dressedGreen_energy
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H)
    (selfEnergy dressedGreen : ℝ → H →L[ℂ] H)
    (energy broadening : ℝ) (selfEnergyDerivative : H →L[ℂ] H)
    (hselfEnergy : HasDerivAt selfEnergy selfEnergyDerivative energy)
    (hgreen : DifferentiableAt ℝ dressedGreen energy)
    (hleft : ∀ x : ℝ,
      dressedSpectralShift side hamiltonian selfEnergy x broadening * dressedGreen x = 1)
    (hright :
      dressedGreen energy *
        dressedSpectralShift side hamiltonian selfEnergy energy broadening = 1) :
    HasDerivAt dressedGreen
      (-dressedGreen energy * (1 - selfEnergyDerivative) * dressedGreen energy) energy := by
  have hshift := hasDerivAt_dressedSpectralShift_energy
    side hamiltonian selfEnergy energy broadening selfEnergyDerivative hselfEnergy
  have hgreenDerivative := hgreen.hasDerivAt
  have hproduct := hshift.mul hgreenDerivative
  have hproductZero :
      HasDerivAt
        (fun x : ℝ =>
          dressedSpectralShift side hamiltonian selfEnergy x broadening * dressedGreen x)
        0 energy := by
    simpa only [hleft] using
      (hasDerivAt_const energy (1 : H →L[ℂ] H))
  have hderivativeSum :
      (1 - selfEnergyDerivative) * dressedGreen energy +
          dressedSpectralShift side hamiltonian selfEnergy energy broadening *
            deriv dressedGreen energy = 0 :=
    hproduct.unique hproductZero
  have hshift_mul_deriv :
      dressedSpectralShift side hamiltonian selfEnergy energy broadening *
          deriv dressedGreen energy =
        -((1 - selfEnergyDerivative) * dressedGreen energy) := by
    calc
      dressedSpectralShift side hamiltonian selfEnergy energy broadening *
          deriv dressedGreen energy =
          ((1 - selfEnergyDerivative) * dressedGreen energy +
              dressedSpectralShift side hamiltonian selfEnergy energy broadening *
                deriv dressedGreen energy) -
            (1 - selfEnergyDerivative) * dressedGreen energy := by
        noncomm_ring
      _ = 0 - (1 - selfEnergyDerivative) * dressedGreen energy := by
        rw [hderivativeSum]
      _ = -((1 - selfEnergyDerivative) * dressedGreen energy) := by
        noncomm_ring
  have hgreenDerivativeFormula :
      deriv dressedGreen energy =
        -dressedGreen energy * (1 - selfEnergyDerivative) * dressedGreen energy := by
    calc
      deriv dressedGreen energy = 1 * deriv dressedGreen energy := by simp
      _ = (dressedGreen energy *
            dressedSpectralShift side hamiltonian selfEnergy energy broadening) *
          deriv dressedGreen energy := by
        rw [hright]
      _ = dressedGreen energy *
          (dressedSpectralShift side hamiltonian selfEnergy energy broadening *
            deriv dressedGreen energy) := by
        rw [mul_assoc]
      _ = dressedGreen energy *
          (-((1 - selfEnergyDerivative) * dressedGreen energy)) := by
        rw [hshift_mul_deriv]
      _ = -dressedGreen energy * (1 - selfEnergyDerivative) * dressedGreen energy := by
        noncomm_ring
  rw [hgreenDerivativeFormula] at hgreenDerivative
  exact hgreenDerivative

end

end QuantumTheory.Transport
