import LeanCondensedMatter.Transport.System
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

set_option linter.style.header false

/-!
# Dimension-independent retarded and advanced resolvents

For a bounded self-adjoint Hamiltonian `H`, define

```text
Gᴿ(E, η) = ((E + iη) I - H)⁻¹,
Gᴬ(E, η) = ((E - iη) I - H)⁻¹.
```

The spectrum of a self-adjoint element of the endomorphism C⋆-algebra is real. Therefore both
spectral parameters lie in the resolvent set whenever `η > 0`, without a finite-dimensional
assumption. The algebraic inverse, adjoint, resolvent-difference, and spectral-parameter derivative
identities below are consequently available on every complete complex Hilbert space.

No trace, trace-class, finite-volume, thermodynamic-limit, or conductivity statement occurs in
this module.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Retarded Green operator `((E + iη) I - H)⁻¹`. -/
noncomputable def retardedResolvent
    (hamiltonian : Observable H) (energy broadening : ℝ) : H →L[ℂ] H :=
  resolvent hamiltonian.1
    (retardedSpectralParameter energy broadening)

/-- Advanced Green operator `((E - iη) I - H)⁻¹`. -/
noncomputable def advancedResolvent
    (hamiltonian : Observable H) (energy broadening : ℝ) : H →L[ℂ] H :=
  resolvent hamiltonian.1
    (advancedSpectralParameter energy broadening)

/-- A positive imaginary part excludes the retarded parameter from the real spectrum. -/
theorem retardedSpectralParameter_not_mem_spectrum
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    retardedSpectralParameter energy broadening ∉ spectrum ℂ hamiltonian.1 := by
  intro hmem
  have him := hamiltonian.2.im_eq_zero_of_mem_spectrum hmem
  have hzero : broadening = 0 := by
    simpa using him
  exact (ne_of_gt hbroadening) hzero

/-- A negative imaginary part excludes the advanced parameter from the real spectrum. -/
theorem advancedSpectralParameter_not_mem_spectrum
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    advancedSpectralParameter energy broadening ∉ spectrum ℂ hamiltonian.1 := by
  intro hmem
  have him := hamiltonian.2.im_eq_zero_of_mem_spectrum hmem
  have hzero : -broadening = 0 := by
    simpa using him
  exact (ne_of_gt hbroadening) (neg_eq_zero.mp hzero)

/-- The retarded spectral parameter lies in the resolvent set for `η > 0`. -/
theorem retardedSpectralParameter_mem_resolventSet
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    retardedSpectralParameter energy broadening ∈
      resolventSet ℂ hamiltonian.1 :=
  spectrum.notMem_iff.mp
    (retardedSpectralParameter_not_mem_spectrum
      hamiltonian energy broadening hbroadening)

/-- The advanced spectral parameter lies in the resolvent set for `η > 0`. -/
theorem advancedSpectralParameter_mem_resolventSet
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    advancedSpectralParameter energy broadening ∈
      resolventSet ℂ hamiltonian.1 :=
  spectrum.notMem_iff.mp
    (advancedSpectralParameter_not_mem_spectrum
      hamiltonian energy broadening hbroadening)

/-- The shifted retarded operator multiplied by its resolvent is the identity. -/
theorem retardedShift_mul_resolvent
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    (algebraMap ℂ (H →L[ℂ] H)
          (retardedSpectralParameter energy broadening) - hamiltonian.1) *
        retardedResolvent hamiltonian energy broadening = 1 := by
  have hres := retardedSpectralParameter_mem_resolventSet
    hamiltonian energy broadening hbroadening
  rw [retardedResolvent, spectrum.resolvent_eq hres]
  exact hres.mul_val_inv

/-- The retarded resolvent multiplied by its shifted operator is the identity. -/
theorem resolvent_mul_retardedShift
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    retardedResolvent hamiltonian energy broadening *
        (algebraMap ℂ (H →L[ℂ] H)
          (retardedSpectralParameter energy broadening) - hamiltonian.1) = 1 := by
  have hres := retardedSpectralParameter_mem_resolventSet
    hamiltonian energy broadening hbroadening
  rw [retardedResolvent, spectrum.resolvent_eq hres]
  exact hres.val_inv_mul

/-- The shifted advanced operator multiplied by its resolvent is the identity. -/
theorem advancedShift_mul_resolvent
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    (algebraMap ℂ (H →L[ℂ] H)
          (advancedSpectralParameter energy broadening) - hamiltonian.1) *
        advancedResolvent hamiltonian energy broadening = 1 := by
  have hres := advancedSpectralParameter_mem_resolventSet
    hamiltonian energy broadening hbroadening
  rw [advancedResolvent, spectrum.resolvent_eq hres]
  exact hres.mul_val_inv

/-- The advanced resolvent multiplied by its shifted operator is the identity. -/
theorem resolvent_mul_advancedShift
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    advancedResolvent hamiltonian energy broadening *
        (algebraMap ℂ (H →L[ℂ] H)
          (advancedSpectralParameter energy broadening) - hamiltonian.1) = 1 := by
  have hres := advancedSpectralParameter_mem_resolventSet
    hamiltonian energy broadening hbroadening
  rw [advancedResolvent, spectrum.resolvent_eq hres]
  exact hres.val_inv_mul

/-- The advanced resolvent is the adjoint of the retarded resolvent. -/
theorem star_retardedResolvent
    (hamiltonian : Observable H) (energy broadening : ℝ) :
    star (retardedResolvent hamiltonian energy broadening) =
      advancedResolvent hamiltonian energy broadening := by
  unfold retardedResolvent advancedResolvent resolvent
  rw [← Ring.inverse_star]
  congr 1
  simp [retardedSpectralParameter, advancedSpectralParameter, hamiltonian.2]

/-- The advanced resolvent adjoints back to the retarded resolvent. -/
theorem star_advancedResolvent
    (hamiltonian : Observable H) (energy broadening : ℝ) :
    star (advancedResolvent hamiltonian energy broadening) =
      retardedResolvent hamiltonian energy broadening := by
  rw [← star_retardedResolvent hamiltonian energy broadening]
  simp

/-- Raw resolvent identity at two retarded spectral parameters. -/
theorem retardedResolvent_sub_retardedResolvent
    (hamiltonian : Observable H) (energy₁ energy₂ broadening : ℝ)
    (hbroadening : 0 < broadening) :
    retardedResolvent hamiltonian energy₁ broadening -
        retardedResolvent hamiltonian energy₂ broadening =
      retardedResolvent hamiltonian energy₁ broadening *
        ((algebraMap ℂ (H →L[ℂ] H)
              (retardedSpectralParameter energy₂ broadening) - hamiltonian.1) -
          (algebraMap ℂ (H →L[ℂ] H)
              (retardedSpectralParameter energy₁ broadening) - hamiltonian.1)) *
        retardedResolvent hamiltonian energy₂ broadening := by
  have h₁ := retardedSpectralParameter_mem_resolventSet
    hamiltonian energy₁ broadening hbroadening
  have h₂ := retardedSpectralParameter_mem_resolventSet
    hamiltonian energy₂ broadening hbroadening
  unfold retardedResolvent resolvent
  exact Ring.inverse_sub_inverse (iff_of_true h₁ h₂)

/-- Raw resolvent identity at two advanced spectral parameters. -/
theorem advancedResolvent_sub_advancedResolvent
    (hamiltonian : Observable H) (energy₁ energy₂ broadening : ℝ)
    (hbroadening : 0 < broadening) :
    advancedResolvent hamiltonian energy₁ broadening -
        advancedResolvent hamiltonian energy₂ broadening =
      advancedResolvent hamiltonian energy₁ broadening *
        ((algebraMap ℂ (H →L[ℂ] H)
              (advancedSpectralParameter energy₂ broadening) - hamiltonian.1) -
          (algebraMap ℂ (H →L[ℂ] H)
              (advancedSpectralParameter energy₁ broadening) - hamiltonian.1)) *
        advancedResolvent hamiltonian energy₂ broadening := by
  have h₁ := advancedSpectralParameter_mem_resolventSet
    hamiltonian energy₁ broadening hbroadening
  have h₂ := advancedSpectralParameter_mem_resolventSet
    hamiltonian energy₂ broadening hbroadening
  unfold advancedResolvent resolvent
  exact Ring.inverse_sub_inverse (iff_of_true h₁ h₂)

/-- Complex spectral-parameter derivative of the resolvent at the retarded point. -/
theorem hasDerivAt_resolvent_retarded
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    HasDerivAt (resolvent hamiltonian.1)
      (-(retardedResolvent hamiltonian energy broadening) ^ 2)
      (retardedSpectralParameter energy broadening) := by
  exact spectrum.hasDerivAt_resolvent_const_left
    (retardedSpectralParameter_mem_resolventSet
      hamiltonian energy broadening hbroadening)

/-- Complex spectral-parameter derivative of the resolvent at the advanced point. -/
theorem hasDerivAt_resolvent_advanced
    (hamiltonian : Observable H) (energy broadening : ℝ)
    (hbroadening : 0 < broadening) :
    HasDerivAt (resolvent hamiltonian.1)
      (-(advancedResolvent hamiltonian energy broadening) ^ 2)
      (advancedSpectralParameter energy broadening) := by
  exact spectrum.hasDerivAt_resolvent_const_left
    (advancedSpectralParameter_mem_resolventSet
      hamiltonian energy broadening hbroadening)

namespace BoundedSystem

/-- Retarded resolvent using the broadening stored in a transport system. -/
noncomputable def retardedGreen
    (system : BoundedSystem H) (energy : ℝ) : H →L[ℂ] H :=
  retardedResolvent system.hamiltonian energy system.broadening

/-- Advanced resolvent using the broadening stored in a transport system. -/
noncomputable def advancedGreen
    (system : BoundedSystem H) (energy : ℝ) : H →L[ℂ] H :=
  advancedResolvent system.hamiltonian energy system.broadening

/-- System-level retarded/advanced adjoint relation. -/
theorem star_retardedGreen (system : BoundedSystem H) (energy : ℝ) :
    star (system.retardedGreen energy) = system.advancedGreen energy :=
  star_retardedResolvent system.hamiltonian energy system.broadening

/-- System-level retarded resolvent identity. -/
theorem retardedGreen_sub_retardedGreen
    (system : BoundedSystem H) (energy₁ energy₂ : ℝ) :
    system.retardedGreen energy₁ - system.retardedGreen energy₂ =
      system.retardedGreen energy₁ *
        ((algebraMap ℂ (H →L[ℂ] H)
              (retardedSpectralParameter energy₂ system.broadening) -
            system.hamiltonian.1) -
          (algebraMap ℂ (H →L[ℂ] H)
              (retardedSpectralParameter energy₁ system.broadening) -
            system.hamiltonian.1)) *
        system.retardedGreen energy₂ :=
  retardedResolvent_sub_retardedResolvent system.hamiltonian
    energy₁ energy₂ system.broadening system.broadening_pos

/-- System-level complex spectral-parameter derivative at the retarded point. -/
theorem hasDerivAt_resolvent_retardedGreen
    (system : BoundedSystem H) (energy : ℝ) :
    HasDerivAt (resolvent system.hamiltonian.1)
      (-(system.retardedGreen energy) ^ 2)
      (retardedSpectralParameter energy system.broadening) :=
  hasDerivAt_resolvent_retarded system.hamiltonian
    energy system.broadening system.broadening_pos

end BoundedSystem

end
end Transport
end QuantumTheory
