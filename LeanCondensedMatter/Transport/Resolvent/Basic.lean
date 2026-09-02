import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent

set_option linter.style.header false

/-!
# Dimension-independent retarded and advanced resolvents

For a bounded self-adjoint Hamiltonian `H`, the common spectral parameter is first written with a
signed imaginary regulator

```text
z(E, γ) = E + iγ,
```

where `γ > 0` is retarded and `γ < 0` is advanced. The physical `SpectralSide` API specializes this
core through `γ = side.sign * η`, with `η` the nonzero broadening magnitude. Resolvent identities at
arbitrary signed regulator are stated directly for the representation-independent `resolvent`, so no
second Green-operator routing wrapper is introduced. The canonical physical Green operator remains
`spectralResolvent side H E η`; conventional retarded/advanced names remain public specializations.

The spectrum of a self-adjoint element of the endomorphism C⋆-algebra is real. Therefore a spectral
parameter lies in the resolvent set whenever its imaginary regulator is nonzero, without a
finite-dimensional assumption. Representation-independent spectrum exclusion and shifted-resolvent
inverse algebra are owned by `Analysis.Operator.Spectral.Resolvent`; this module keeps the spectral
parameter conventions and their transport specializations.

No transport-system wrapper, trace, trace-class, finite-volume, thermodynamic-limit, or conductivity
statement occurs in this module.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Retarded/advanced choice for a complex spectral parameter. -/
inductive SpectralSide
  | retarded
  | advanced
  deriving DecidableEq

namespace SpectralSide

/-- Sign multiplying the imaginary broadening: `+1` for retarded and `-1` for advanced. -/
def sign : SpectralSide → ℝ
  | .retarded => 1
  | .advanced => -1

@[simp] theorem sign_retarded : sign .retarded = 1 := rfl
@[simp] theorem sign_advanced : sign .advanced = -1 := rfl

theorem sign_ne_zero (side : SpectralSide) : side.sign ≠ 0 := by
  cases side <;> simp [sign]

/-- The opposite physical boundary-value side. -/
def opposite : SpectralSide → SpectralSide
  | .retarded => .advanced
  | .advanced => .retarded

@[simp]
theorem opposite_opposite (side : SpectralSide) : side.opposite.opposite = side := by
  cases side <;> rfl

@[simp]
theorem sign_opposite (side : SpectralSide) : side.opposite.sign = -side.sign := by
  cases side <;> simp [opposite, sign]

end SpectralSide

/-- Spectral parameter `E + iγ` with an arbitrary signed imaginary regulator `γ`. -/
def spectralParameterOfRegulator (energy regulator : ℝ) : ℂ :=
  (energy : ℂ) + (regulator : ℂ) * Complex.I

@[simp]
theorem spectralParameterOfRegulator_re (energy regulator : ℝ) :
    (spectralParameterOfRegulator energy regulator).re = energy := by
  simp [spectralParameterOfRegulator]

@[simp]
theorem spectralParameterOfRegulator_im (energy regulator : ℝ) :
    (spectralParameterOfRegulator energy regulator).im = regulator := by
  simp [spectralParameterOfRegulator]

/-- Complex conjugation reverses the signed imaginary regulator. -/
@[simp]
theorem star_spectralParameterOfRegulator (energy regulator : ℝ) :
    star (spectralParameterOfRegulator energy regulator) =
      spectralParameterOfRegulator energy (-regulator) := by
  apply Complex.ext <;>
    simp [spectralParameterOfRegulator]

/-- A nonzero signed regulator keeps the spectral parameter away from every real energy. -/
theorem spectralParameterOfRegulator_sub_real_ne_zero
    (energy regulator eigenvalue : ℝ) (hregulator : regulator ≠ 0) :
    spectralParameterOfRegulator energy regulator - (eigenvalue : ℂ) ≠ 0 := by
  intro hzero
  have him : regulator = 0 := by
    simpa [spectralParameterOfRegulator] using congrArg Complex.im hzero
  exact hregulator him

/-- Side-indexed spectral parameter `E + s iη`, with `s = ±1`. -/
def spectralParameter (side : SpectralSide) (energy broadening : ℝ) : ℂ :=
  spectralParameterOfRegulator energy (side.sign * broadening)

/-- The retarded spectral parameter `E + iη`. -/
def retardedSpectralParameter (energy broadening : ℝ) : ℂ :=
  spectralParameterOfRegulator energy broadening

/-- The advanced spectral parameter `E - iη`. -/
def advancedSpectralParameter (energy broadening : ℝ) : ℂ :=
  spectralParameterOfRegulator energy (-broadening)

/-- The retarded parameter is the `+1` specialization of `spectralParameter`. -/
theorem spectralParameter_retarded (energy broadening : ℝ) :
    spectralParameter .retarded energy broadening =
      retardedSpectralParameter energy broadening := by
  simp [spectralParameter, retardedSpectralParameter]

/-- The advanced parameter is the `-1` specialization of `spectralParameter`. -/
theorem spectralParameter_advanced (energy broadening : ℝ) :
    spectralParameter .advanced energy broadening =
      advancedSpectralParameter energy broadening := by
  simp [spectralParameter, advancedSpectralParameter]

@[simp]
theorem spectralParameter_im (side : SpectralSide) (energy broadening : ℝ) :
    (spectralParameter side energy broadening).im = side.sign * broadening := by
  simp [spectralParameter]

/-- A nonzero broadening keeps either spectral-side parameter away from every real energy. -/
theorem spectralParameter_sub_real_ne_zero
    (side : SpectralSide) (energy broadening eigenvalue : ℝ)
    (hbroadening : broadening ≠ 0) :
    spectralParameter side energy broadening - (eigenvalue : ℂ) ≠ 0 := by
  exact spectralParameterOfRegulator_sub_real_ne_zero
    energy (side.sign * broadening) eigenvalue
      (mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening)

@[simp]
theorem retardedSpectralParameter_re (energy broadening : ℝ) :
    (retardedSpectralParameter energy broadening).re = energy := by
  simp [retardedSpectralParameter]

@[simp]
theorem retardedSpectralParameter_im (energy broadening : ℝ) :
    (retardedSpectralParameter energy broadening).im = broadening := by
  simp [retardedSpectralParameter]

@[simp]
theorem advancedSpectralParameter_re (energy broadening : ℝ) :
    (advancedSpectralParameter energy broadening).re = energy := by
  simp [advancedSpectralParameter]

@[simp]
theorem advancedSpectralParameter_im (energy broadening : ℝ) :
    (advancedSpectralParameter energy broadening).im = -broadening := by
  simp [advancedSpectralParameter]

@[simp] private theorem star_retardedSpectralParameter
    (energy broadening : ℝ) :
    star (retardedSpectralParameter energy broadening) =
      advancedSpectralParameter energy broadening := by
  simpa [retardedSpectralParameter, advancedSpectralParameter] using
    star_spectralParameterOfRegulator energy broadening

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- For an arbitrary nonzero signed regulator, the spectral shift multiplied by its resolvent is
the identity. -/
theorem spectralShift_mul_resolvent_spectralParameterOfRegulator
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) - hamiltonian) *
        resolvent hamiltonian (spectralParameterOfRegulator energy regulator) = 1 := by
  exact QuantumTheory.spectralShift_mul_resolvent_of_not_mem
    hamiltonian (spectralParameterOfRegulator energy regulator)
    (QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
      hamiltonian hself (spectralParameterOfRegulator energy regulator)
      (by
        rw [spectralParameterOfRegulator_im]
        exact hregulator))

/-- For an arbitrary nonzero signed regulator, its resolvent multiplied by the spectral shift is
the identity. -/
theorem resolvent_spectralParameterOfRegulator_mul_spectralShift
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy regulator : ℝ) (hregulator : regulator ≠ 0) :
    resolvent hamiltonian (spectralParameterOfRegulator energy regulator) *
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameterOfRegulator energy regulator) - hamiltonian) =
      1 := by
  exact QuantumTheory.resolvent_mul_spectralShift_of_not_mem
    hamiltonian (spectralParameterOfRegulator energy regulator)
    (QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
      hamiltonian hself (spectralParameterOfRegulator energy regulator)
      (by
        rw [spectralParameterOfRegulator_im]
        exact hregulator))

/-- For a self-adjoint Hamiltonian, taking the adjoint of a resolvent reverses the arbitrary signed
imaginary regulator. -/
theorem star_resolvent_spectralParameterOfRegulator
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy regulator : ℝ) :
    star (resolvent hamiltonian (spectralParameterOfRegulator energy regulator)) =
      resolvent hamiltonian (spectralParameterOfRegulator energy (-regulator)) := by
  unfold resolvent
  rw [← Ring.inverse_star]
  congr 1
  rw [star_sub, hself]
  simp [Algebra.algebraMap_eq_smul_one]

/-- Green operator on either spectral side, `((E + s iη) I - H)⁻¹`. -/
noncomputable def spectralResolvent
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  resolvent hamiltonian (spectralParameter side energy broadening)

/-- Retarded Green operator `((E + iη) I - H)⁻¹`. -/
noncomputable def retardedResolvent
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  resolvent hamiltonian (retardedSpectralParameter energy broadening)

/-- Advanced Green operator `((E - iη) I - H)⁻¹`. -/
noncomputable def advancedResolvent
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  resolvent hamiltonian (advancedSpectralParameter energy broadening)

omit [CompleteSpace H] in
@[simp]
theorem spectralResolvent_retarded
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) :
    spectralResolvent .retarded hamiltonian energy broadening =
      retardedResolvent hamiltonian energy broadening := by
  unfold spectralResolvent retardedResolvent
  rw [spectralParameter_retarded]

omit [CompleteSpace H] in
@[simp]
theorem spectralResolvent_advanced
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) :
    spectralResolvent .advanced hamiltonian energy broadening =
      advancedResolvent hamiltonian energy broadening := by
  unfold spectralResolvent advancedResolvent
  rw [spectralParameter_advanced]

/-- The side-indexed shifted operator multiplied by the canonical spectral resolvent is the
identity. -/
theorem spectralShift_mul_spectralResolvent
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) *
        spectralResolvent side hamiltonian energy broadening = 1 := by
  simpa only [spectralResolvent, spectralParameter] using
    spectralShift_mul_resolvent_spectralParameterOfRegulator
      hamiltonian hself energy (side.sign * broadening)
      (mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening)

/-- The canonical spectral resolvent multiplied by its side-indexed shift is the identity. -/
theorem spectralResolvent_mul_spectralShift
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    spectralResolvent side hamiltonian energy broadening *
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) =
      1 := by
  simpa only [spectralResolvent, spectralParameter] using
    resolvent_spectralParameterOfRegulator_mul_spectralShift
      hamiltonian hself energy (side.sign * broadening)
      (mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening)

/-- Adjointing a physical spectral resolvent exchanges it with the opposite spectral side. -/
theorem star_spectralResolvent
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) :
    star (spectralResolvent side hamiltonian energy broadening) =
      spectralResolvent side.opposite hamiltonian energy broadening := by
  simpa [spectralResolvent, spectralParameter] using
    star_resolvent_spectralParameterOfRegulator
      hamiltonian hself energy (side.sign * broadening)

/-- The advanced resolvent is the adjoint of the retarded resolvent. -/
theorem star_retardedResolvent
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) :
    star (retardedResolvent hamiltonian energy broadening) =
      advancedResolvent hamiltonian energy broadening := by
  unfold retardedResolvent advancedResolvent
  simpa [retardedSpectralParameter, advancedSpectralParameter] using
    star_resolvent_spectralParameterOfRegulator hamiltonian hself energy broadening

end
end Transport
end QuantumTheory
