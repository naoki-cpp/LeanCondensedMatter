import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent

set_option linter.style.header false

/-!
# Dimension-independent retarded and advanced resolvents

For a bounded self-adjoint Hamiltonian `H`, the common spectral parameter is first written with a
signed imaginary regulator

```text
z(E, γ) = E + iγ,
```

where `γ > 0` is retarded and `γ < 0` is advanced. The physical `SpectralSide` API owns the
specialization through `γ = side.regulator η`; conventional branches take `η > 0`. Algebraic
resolvent-set results below only require the regulator to be nonzero. Resolvent identities at an
arbitrary signed regulator are stated directly for the representation-independent `resolvent`, so no
second Green-operator routing wrapper is introduced. The canonical physical Green operator is
`spectralResolvent side H E η`; conventional retarded/advanced names are public specializations.

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

/-- Sign distinguishing the retarded (`+1`) and advanced (`-1`) spectral sides. -/
def sign : SpectralSide → ℝ
  | .retarded => 1
  | .advanced => -1

@[simp] theorem sign_retarded : sign .retarded = 1 := rfl
@[simp] theorem sign_advanced : sign .advanced = -1 := rfl

theorem sign_ne_zero (side : SpectralSide) : side.sign ≠ 0 := by
  cases side <;> simp [sign]

/-- Signed analytic regulator selected by a physical spectral side and nonnegative broadening
parameter. This is the canonical physical-to-analytic boundary for retarded/advanced APIs. -/
def regulator (side : SpectralSide) (broadening : ℝ) : ℝ :=
  side.sign * broadening

@[simp] theorem regulator_retarded (broadening : ℝ) :
    SpectralSide.retarded.regulator broadening = broadening := by
  simp [regulator]

@[simp] theorem regulator_advanced (broadening : ℝ) :
    SpectralSide.advanced.regulator broadening = -broadening := by
  simp [regulator]

theorem regulator_ne_zero (side : SpectralSide) {broadening : ℝ}
    (hbroadening : broadening ≠ 0) : side.regulator broadening ≠ 0 := by
  exact mul_ne_zero (sign_ne_zero side) hbroadening

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

@[simp]
theorem regulator_opposite (side : SpectralSide) (broadening : ℝ) :
    side.opposite.regulator broadening = -side.regulator broadening := by
  simp [regulator]

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

/-- Side-indexed spectral parameter `E + iγˢ`, where `γˢ = side.regulator η`. -/
def spectralParameter (side : SpectralSide) (energy broadening : ℝ) : ℂ :=
  spectralParameterOfRegulator energy (side.regulator broadening)

/-- The retarded spectral parameter `E + iη`. -/
def retardedSpectralParameter (energy broadening : ℝ) : ℂ :=
  spectralParameter .retarded energy broadening

/-- The advanced spectral parameter `E - iη`. -/
def advancedSpectralParameter (energy broadening : ℝ) : ℂ :=
  spectralParameter .advanced energy broadening

/-- The retarded parameter is the retarded specialization of the canonical side-indexed parameter. -/
theorem spectralParameter_retarded (energy broadening : ℝ) :
    spectralParameter .retarded energy broadening =
      retardedSpectralParameter energy broadening :=
  rfl

/-- The advanced parameter is the advanced specialization of the canonical side-indexed parameter. -/
theorem spectralParameter_advanced (energy broadening : ℝ) :
    spectralParameter .advanced energy broadening =
      advancedSpectralParameter energy broadening :=
  rfl

@[simp]
theorem spectralParameter_im (side : SpectralSide) (energy broadening : ℝ) :
    (spectralParameter side energy broadening).im = side.regulator broadening := by
  simp [spectralParameter]

@[simp]
theorem retardedSpectralParameter_re (energy broadening : ℝ) :
    (retardedSpectralParameter energy broadening).re = energy := by
  simp [retardedSpectralParameter, spectralParameter]

@[simp]
theorem retardedSpectralParameter_im (energy broadening : ℝ) :
    (retardedSpectralParameter energy broadening).im = broadening := by
  simp [retardedSpectralParameter, spectralParameter]

@[simp]
theorem advancedSpectralParameter_re (energy broadening : ℝ) :
    (advancedSpectralParameter energy broadening).re = energy := by
  simp [advancedSpectralParameter, spectralParameter]

@[simp]
theorem advancedSpectralParameter_im (energy broadening : ℝ) :
    (advancedSpectralParameter energy broadening).im = -broadening := by
  simp [advancedSpectralParameter, spectralParameter]

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

/-- Green operator on either spectral side, `((E + iγˢ) I - H)⁻¹`. -/
noncomputable def spectralResolvent
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H)
    (energy broadening : ℝ) : H →L[ℂ] H :=
  resolvent hamiltonian (spectralParameter side energy broadening)

/-- Retarded Green operator `((E + iη) I - H)⁻¹`. -/
noncomputable def retardedResolvent
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  spectralResolvent .retarded hamiltonian energy broadening

/-- Advanced Green operator `((E - iη) I - H)⁻¹`. -/
noncomputable def advancedResolvent
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  spectralResolvent .advanced hamiltonian energy broadening

/-- The side-indexed shifted operator multiplied by the canonical spectral resolvent is the
identity. -/
theorem spectralShift_mul_spectralResolvent
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) *
        spectralResolvent side hamiltonian energy broadening = 1 := by
  simpa only [spectralResolvent, spectralParameter] using
    spectralShift_mul_resolvent_spectralParameterOfRegulator
      hamiltonian hself energy (side.regulator broadening)
      (side.regulator_ne_zero hbroadening)

/-- The canonical spectral resolvent multiplied by its side-indexed shift is the identity. -/
theorem spectralResolvent_mul_spectralShift
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    spectralResolvent side hamiltonian energy broadening *
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) =
      1 := by
  simpa only [spectralResolvent, spectralParameter] using
    resolvent_spectralParameterOfRegulator_mul_spectralShift
      hamiltonian hself energy (side.regulator broadening)
      (side.regulator_ne_zero hbroadening)

end
end Transport
end QuantumTheory
