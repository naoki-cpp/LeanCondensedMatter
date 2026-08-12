import LeanCondensedMatter.SecondQuantization.Fermionic.Field.KuboBastinTrace

set_option linter.style.header false

/-!
# Static target of the finite-dimensional Kubo–Bastin response

The response derived before the Středa layer retains finite frequency, positive switching rate, an
explicit Peierls contact term, and the finite-volume electric-field normalization. A static
Smrčka–Středa bridge must therefore begin by fixing the exact `ω = 0` specialization rather than
silently replacing the response by an unnormalized energy integral.

This module names that target and separates its vector-potential coefficient from the final
current-density/electric-field normalization. It proves the exact zero-frequency specialization of
the causal Kubo response and exposes the finite spectral formula with the contact term unchanged.

No contact cancellation, traced energy-integral representation, zero-switching limit, disorder,
trace per unit volume, or thermodynamic-limit statement is made here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open Lattice

open QuantumTheory.LinearResponse

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype ι]

/-- Zero-frequency vector-potential response coefficient, retaining the finite current-current
ordinary trace and the explicit Peierls contact expectation. -/
noncomputable def finiteDimensionalStaticKuboBastinVectorPotentialResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
      (finiteKuboBastinDirectionalTraceCarrier
        system data geometry direction K q 0 eta) +
    purePointNormalizedExpectation system data
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K)

/-- Named finite-dimensional static Kubo–Bastin conductivity target. The switching rate remains
positive and finite; only the driving frequency is specialized to zero. -/
noncomputable def finiteDimensionalStaticKuboBastinDirectionalConductivity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteDimensionalKuboBastinDirectionalConductivity
    convention system data geometry direction K q 0 eta

/-- The static conductivity is the retained vector-potential coefficient multiplied by the exact
zero-frequency finite-volume electric-field normalization. -/
theorem finiteDimensionalStaticKuboBastinDirectionalConductivity_eq_vectorPotential
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteDimensionalStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta =
      finiteDimensionalStaticKuboBastinVectorPotentialResponse
          system data geometry direction K q eta *
        finiteVolumeConductivityNormalization convention 0 eta := by
  rfl

/-- Expanding the static ordinary trace gives the finite zero-frequency spectral sum plus the
unchanged contact expectation. -/
theorem finiteDimensionalStaticKuboBastinVectorPotentialResponse_eq_finite_sum
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteDimensionalStaticKuboBastinVectorPotentialResponse
        system data geometry direction K q eta =
      (∑ mn : ι × ι,
        finiteKuboBastinSpectralDirectionalCurrentTerm
          system data geometry direction K q 0 eta mn) +
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K) := by
  unfold finiteDimensionalStaticKuboBastinVectorPotentialResponse
  rw [linearMap_trace_finiteKuboBastinDirectionalTraceCarrier]

/-- Exact finite spectral form of the named static conductivity target. -/
theorem finiteDimensionalStaticKuboBastinDirectionalConductivity_eq_finite_sum
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteDimensionalStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta =
      ((∑ mn : ι × ι,
        finiteKuboBastinSpectralDirectionalCurrentTerm
          system data geometry direction K q 0 eta mn) +
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K)) *
        finiteVolumeConductivityNormalization convention 0 eta := by
  rw [finiteDimensionalStaticKuboBastinDirectionalConductivity_eq_vectorPotential]
  rw [finiteDimensionalStaticKuboBastinVectorPotentialResponse_eq_finite_sum]

/-- The static named target remains connected to the causal Kubo response at every positive
switching rate. -/
theorem infiniteTimeAdiabaticDirectionalConductivity_zero_frequency_eq_staticKuboBastin
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) (heta : 0 < eta) :
    infiniteTimeAdiabaticDirectionalConductivity convention
        system (purePointNormalizedExpectation system data)
          geometry direction K q 0 eta =
      finiteDimensionalStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta := by
  exact infiniteTimeAdiabaticDirectionalConductivity_eq_finiteDimensionalKuboBastin
    convention system data geometry direction K q 0 eta heta

/-- At zero frequency, the electric-field normalization keeps the finite switching rate and volume
explicit. -/
theorem finiteVolumeConductivityNormalization_zero_frequency
    (convention : QuantumTheory.Transport.PositiveVolume) (eta : ℝ) :
    finiteVolumeConductivityNormalization convention 0 eta =
      (((convention.volume : ℂ) * (-(eta : ℂ))))⁻¹ := by
  simp [finiteVolumeConductivityNormalization]

end
end Field
end Fermionic
end SecondQuantization
