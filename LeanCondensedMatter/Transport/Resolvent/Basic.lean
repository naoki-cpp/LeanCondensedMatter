import LeanCondensedMatter.Analysis.Operator.Spectral.Resolvent

set_option linter.style.header false

/-!
# Dimension-independent retarded and advanced resolvents

For a bounded self-adjoint Hamiltonian `H`, define the two spectral sides

```text
zˢ(E, η) = E + s iη,  s = ±1,
```

with `s = +1` for the retarded side and `s = -1` for the advanced side. The canonical Green
operator is `spectralResolvent side H E η`; conventional retarded/advanced names remain public
specializations of that common core.

The spectrum of a self-adjoint element of the endomorphism C⋆-algebra is real. Therefore both
spectral parameters lie in the resolvent set whenever `η ≠ 0`, without a finite-dimensional
assumption. Representation-independent spectrum exclusion and shifted-resolvent inverse algebra are
owned by `Analysis.Operator.Spectral.Resolvent`; this module keeps the retarded/advanced spectral
parameter conventions and their physical specializations.

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

/-- A nonzero broadening keeps either spectral-side parameter away from every real energy. -/
theorem spectralParameter_sub_real_ne_zero
    (side : SpectralSide) (energy broadening eigenvalue : ℝ)
    (hbroadening : broadening ≠ 0) :
    spectralParameter side energy broadening - (eigenvalue : ℂ) ≠ 0 := by
  intro hzero
  have him : side.sign * broadening = 0 := by
    simpa [spectralParameter] using congrArg Complex.im hzero
  exact (mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening) him

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

private @[simp] theorem star_retardedSpectralParameter
    (energy broadening : ℝ) :
    star (retardedSpectralParameter energy broadening) =
      advancedSpectralParameter energy broadening := by
  apply Complex.ext <;>
    simp [retardedSpectralParameter, advancedSpectralParameter]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

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
  simpa only [spectralResolvent] using
    QuantumTheory.spectralShift_mul_resolvent_of_not_mem
      hamiltonian (spectralParameter side energy broadening)
      (QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
        hamiltonian hself (spectralParameter side energy broadening)
        (by
          rw [spectralParameter_im]
          exact mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening))

/-- The canonical spectral resolvent multiplied by its side-indexed shift is the identity. -/
theorem spectralResolvent_mul_spectralShift
    (side : SpectralSide) (hamiltonian : H →L[ℂ] H) (hself : IsSelfAdjoint hamiltonian)
    (energy broadening : ℝ) (hbroadening : broadening ≠ 0) :
    spectralResolvent side hamiltonian energy broadening *
        (algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) - hamiltonian) =
      1 := by
  simpa only [spectralResolvent] using
    QuantumTheory.resolvent_mul_spectralShift_of_not_mem
      hamiltonian (spectralParameter side energy broadening)
      (QuantumTheory.not_mem_spectrum_of_isSelfAdjoint_of_im_ne_zero
        hamiltonian hself (spectralParameter side energy broadening)
        (by
          rw [spectralParameter_im]
          exact mul_ne_zero (SpectralSide.sign_ne_zero side) hbroadening))

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

end
end Transport
end QuantumTheory
