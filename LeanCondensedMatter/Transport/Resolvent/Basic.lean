import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

set_option linter.style.header false

/-!
# Dimension-independent retarded and advanced resolvents

For a bounded self-adjoint Hamiltonian `H`, define the two spectral sides

```text
zˢ(E, η) = E + s iη,  s = ±1,
```

with `s = +1` for the retarded side and `s = -1` for the advanced side. The conventional
retarded/advanced names remain as public specializations of the small common core used by proofs
that genuinely do not depend on the side.

The spectrum of a self-adjoint element of the endomorphism C⋆-algebra is real. Therefore both
spectral parameters lie in the resolvent set whenever `η ≠ 0`, without a finite-dimensional
assumption. The algebraic inverse and spectral-parameter derivative identities below are
consequently available on every complete complex Hilbert space.

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

end SpectralSide

/-- Side-indexed spectral parameter `E + s iη`, with `s = ±1`. -/
def spectralParameter (side : SpectralSide) (energy broadening : ℝ) : ℂ :=
  (energy : ℂ) + ((side.sign * broadening : ℝ) : ℂ) * Complex.I

/-- The retarded spectral parameter `E + iη`. -/
def retardedSpectralParameter (energy broadening : ℝ) : ℂ :=
  (energy : ℂ) + (broadening : ℂ) * Complex.I

/-- The advanced spectral parameter `E - iη`. -/
def advancedSpectralParameter (energy broadening : ℝ) : ℂ :=
  (energy : ℂ) - (broadening : ℂ) * Complex.I

/-- The retarded parameter is the `+1` specialization of `spectralParameter`. -/
theorem spectralParameter_retarded (energy broadening : ℝ) :
    spectralParameter .retarded energy broadening =
      retardedSpectralParameter energy broadening := by
  simp [spectralParameter, retardedSpectralParameter]

/-- The advanced parameter is the `-1` specialization of `spectralParameter`. -/
theorem spectralParameter_advanced (energy broadening : ℝ) :
    spectralParameter .advanced energy broadening =
      advancedSpectralParameter energy broadening := by
  simp [spectralParameter, advancedSpectralParameter, sub_eq_add_neg]

@[simp]
theorem spectralParameter_im (side : SpectralSide) (energy broadening : ℝ) :
    (spectralParameter side energy broadening).im = side.sign * broadening := by
  simp [spectralParameter]

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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Retarded Green operator `((E + iη) I - H)⁻¹`. -/
noncomputable def retardedResolvent
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  resolvent hamiltonian (retardedSpectralParameter energy broadening)

/-- Advanced Green operator `((E - iη) I - H)⁻¹`. -/
noncomputable def advancedResolvent
    (hamiltonian : H →L[ℂ] H) (energy broadening : ℝ) : H →L[ℂ] H :=
  resolvent hamiltonian (advancedSpectralParameter energy broadening)

/-- A nonreal scalar cannot belong to the spectrum of a self-adjoint bounded operator. -/
theorem spectralParameter_not_mem_spectrum_of_im_ne_zero
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (z : ℂ) (hz : z.im ≠ 0) :
    z ∉ spectrum ℂ hamiltonian := by
  intro hmem
  exact hz (IsSelfAdjoint.im_eq_zero_of_mem_spectrum
    (A := H →L[ℂ] H) hself hmem)

/-- A positive imaginary part excludes the retarded parameter from the real spectrum. -/
theorem retardedSpectralParameter_not_mem_spectrum
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    retardedSpectralParameter energy broadening ∉ spectrum ℂ hamiltonian := by
  apply spectralParameter_not_mem_spectrum_of_im_ne_zero hamiltonian hself
  simp [ne_of_gt hbroadening]

/-- A negative imaginary part excludes the advanced parameter from the real spectrum. -/
theorem advancedSpectralParameter_not_mem_spectrum
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    advancedSpectralParameter energy broadening ∉ spectrum ℂ hamiltonian := by
  apply spectralParameter_not_mem_spectrum_of_im_ne_zero hamiltonian hself
  simp [ne_of_gt hbroadening]

/-- The side-indexed spectral parameter lies in the resolvent set for nonzero broadening. -/
theorem spectralParameter_mem_resolventSet
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    spectralParameter side energy broadening ∈ resolventSet ℂ hamiltonian := by
  apply spectrum.notMem_iff.mp
  apply spectralParameter_not_mem_spectrum_of_im_ne_zero hamiltonian hself
  rw [spectralParameter_im]
  exact mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening

/-- The retarded spectral parameter lies in the resolvent set for `η > 0`. -/
theorem retardedSpectralParameter_mem_resolventSet
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    retardedSpectralParameter energy broadening ∈ resolventSet ℂ hamiltonian :=
  spectrum.notMem_iff.mp
    (retardedSpectralParameter_not_mem_spectrum
      hamiltonian hself energy broadening hbroadening)

/-- The advanced spectral parameter lies in the resolvent set for `η > 0`. -/
theorem advancedSpectralParameter_mem_resolventSet
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    advancedSpectralParameter energy broadening ∈ resolventSet ℂ hamiltonian :=
  spectrum.notMem_iff.mp
    (advancedSpectralParameter_not_mem_spectrum
      hamiltonian hself energy broadening hbroadening)

/-- The side-indexed shifted operator multiplied by its resolvent is the identity. -/
theorem spectralShift_mul_resolvent
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) *
        resolvent hamiltonian (spectralParameter side energy broadening) = 1 := by
  have hres := spectralParameter_mem_resolventSet
    side hamiltonian hself energy broadening hbroadening
  rw [spectrum.resolvent_eq hres]
  exact hres.mul_val_inv

/-- The side-indexed resolvent multiplied by its shifted operator is the identity. -/
theorem resolvent_mul_spectralShift
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    resolvent hamiltonian (spectralParameter side energy broadening) *
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) =
      1 := by
  have hres := spectralParameter_mem_resolventSet
    side hamiltonian hself energy broadening hbroadening
  rw [spectrum.resolvent_eq hres]
  exact hres.val_inv_mul

/-- The shifted retarded operator multiplied by its resolvent is the identity. -/
theorem retardedShift_mul_resolvent
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    (algebraMap ℂ (H →L[ℂ] H) (retardedSpectralParameter energy broadening) - hamiltonian) *
        retardedResolvent hamiltonian energy broadening = 1 := by
  simpa only [retardedResolvent, spectralParameter_retarded] using
    spectralShift_mul_resolvent .retarded hamiltonian hself energy broadening
      (ne_of_gt hbroadening)

/-- The retarded resolvent multiplied by its shifted operator is the identity. -/
theorem resolvent_mul_retardedShift
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    retardedResolvent hamiltonian energy broadening *
        (algebraMap ℂ (H →L[ℂ] H) (retardedSpectralParameter energy broadening) - hamiltonian) =
      1 := by
  simpa only [retardedResolvent, spectralParameter_retarded] using
    resolvent_mul_spectralShift .retarded hamiltonian hself energy broadening
      (ne_of_gt hbroadening)

/-- The shifted advanced operator multiplied by its resolvent is the identity. -/
theorem advancedShift_mul_resolvent
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    (algebraMap ℂ (H →L[ℂ] H) (advancedSpectralParameter energy broadening) - hamiltonian) *
        advancedResolvent hamiltonian energy broadening = 1 := by
  simpa only [advancedResolvent, spectralParameter_advanced] using
    spectralShift_mul_resolvent .advanced hamiltonian hself energy broadening
      (ne_of_gt hbroadening)

/-- The advanced resolvent multiplied by its shifted operator is the identity. -/
theorem resolvent_mul_advancedShift
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    advancedResolvent hamiltonian energy broadening *
        (algebraMap ℂ (H →L[ℂ] H) (advancedSpectralParameter energy broadening) - hamiltonian) =
      1 := by
  simpa only [advancedResolvent, spectralParameter_advanced] using
    resolvent_mul_spectralShift .advanced hamiltonian hself energy broadening
      (ne_of_gt hbroadening)

/-- Complex conjugation exchanges the retarded and advanced spectral parameters. -/
@[simp]
theorem star_retardedSpectralParameter (energy broadening : ℝ) :
    star (retardedSpectralParameter energy broadening) =
      advancedSpectralParameter energy broadening := by
  apply Complex.ext <;>
    simp [retardedSpectralParameter, advancedSpectralParameter]

/-- Complex conjugation exchanges the advanced and retarded spectral parameters. -/
@[simp]
theorem star_advancedSpectralParameter (energy broadening : ℝ) :
    star (advancedSpectralParameter energy broadening) =
      retardedSpectralParameter energy broadening := by
  apply Complex.ext <;>
    simp [retardedSpectralParameter, advancedSpectralParameter]

/-- The advanced resolvent is the adjoint of the retarded resolvent. -/
theorem star_retardedResolvent
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) :
    star (retardedResolvent hamiltonian energy broadening) =
      advancedResolvent hamiltonian energy broadening := by
  unfold retardedResolvent advancedResolvent resolvent
  rw [← Ring.inverse_star]
  congr 1
  rw [star_sub, hself]
  simp [Algebra.algebraMap_eq_smul_one]

/-- The advanced resolvent adjoints back to the retarded resolvent. -/
theorem star_advancedResolvent
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) :
    star (advancedResolvent hamiltonian energy broadening) =
      retardedResolvent hamiltonian energy broadening := by
  rw [← star_retardedResolvent hamiltonian hself energy broadening]
  simp

/-- Raw resolvent identity at two retarded spectral parameters. -/
theorem retardedResolvent_sub_retardedResolvent
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy₁ energy₂ broadening : ℝ) (hbroadening : 0 < broadening) :
    retardedResolvent hamiltonian energy₁ broadening -
        retardedResolvent hamiltonian energy₂ broadening =
      retardedResolvent hamiltonian energy₁ broadening *
        ((algebraMap ℂ (H →L[ℂ] H) (retardedSpectralParameter energy₂ broadening) - hamiltonian) -
          (algebraMap ℂ (H →L[ℂ] H) (retardedSpectralParameter energy₁ broadening) - hamiltonian)) *
        retardedResolvent hamiltonian energy₂ broadening := by
  have h₁ := retardedSpectralParameter_mem_resolventSet
    hamiltonian hself energy₁ broadening hbroadening
  have h₂ := retardedSpectralParameter_mem_resolventSet
    hamiltonian hself energy₂ broadening hbroadening
  unfold retardedResolvent resolvent
  exact Ring.inverse_sub_inverse (iff_of_true h₁ h₂)

/-- Raw resolvent identity at two advanced spectral parameters. -/
theorem advancedResolvent_sub_advancedResolvent
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy₁ energy₂ broadening : ℝ) (hbroadening : 0 < broadening) :
    advancedResolvent hamiltonian energy₁ broadening -
        advancedResolvent hamiltonian energy₂ broadening =
      advancedResolvent hamiltonian energy₁ broadening *
        ((algebraMap ℂ (H →L[ℂ] H) (advancedSpectralParameter energy₂ broadening) - hamiltonian) -
          (algebraMap ℂ (H →L[ℂ] H) (advancedSpectralParameter energy₁ broadening) - hamiltonian)) *
        advancedResolvent hamiltonian energy₂ broadening := by
  have h₁ := advancedSpectralParameter_mem_resolventSet
    hamiltonian hself energy₁ broadening hbroadening
  have h₂ := advancedSpectralParameter_mem_resolventSet
    hamiltonian hself energy₂ broadening hbroadening
  unfold advancedResolvent resolvent
  exact Ring.inverse_sub_inverse (iff_of_true h₁ h₂)

/-- Complex spectral-parameter derivative of the resolvent at either side-indexed point. -/
theorem hasDerivAt_resolvent_spectralParameter
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    HasDerivAt (resolvent hamiltonian)
      (-(resolvent hamiltonian (spectralParameter side energy broadening)) ^ 2)
      (spectralParameter side energy broadening) := by
  exact spectrum.hasDerivAt_resolvent_const_left
    (spectralParameter_mem_resolventSet
      side hamiltonian hself energy broadening hbroadening)

/-- Complex spectral-parameter derivative of the resolvent at the retarded point. -/
theorem hasDerivAt_resolvent_retarded
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (resolvent hamiltonian)
      (-(retardedResolvent hamiltonian energy broadening) ^ 2)
      (retardedSpectralParameter energy broadening) := by
  simpa only [retardedResolvent, spectralParameter_retarded] using
    hasDerivAt_resolvent_spectralParameter .retarded hamiltonian hself
      energy broadening (ne_of_gt hbroadening)

/-- Complex spectral-parameter derivative of the resolvent at the advanced point. -/
theorem hasDerivAt_resolvent_advanced
    (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : 0 < broadening) :
    HasDerivAt (resolvent hamiltonian)
      (-(advancedResolvent hamiltonian energy broadening) ^ 2)
      (advancedSpectralParameter energy broadening) := by
  simpa only [advancedResolvent, spectralParameter_advanced] using
    hasDerivAt_resolvent_spectralParameter .advanced hamiltonian hself
      energy broadening (ne_of_gt hbroadening)

end
end Transport
end QuantumTheory
