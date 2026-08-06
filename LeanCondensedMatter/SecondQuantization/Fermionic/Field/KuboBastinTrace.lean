import LeanCondensedMatter.SecondQuantization.Fermionic.Field.KuboBastinSpectral
import Mathlib.Analysis.InnerProductSpace.Trace

set_option linter.style.header false

/-!
# Ordinary finite-dimensional trace form of the Kubo–Bastin response

This module packages the finite resolvent spectral expression proved in
`KuboBastinSpectral` as an ordinary complex linear trace. The trace carrier is constructed on the
same finite energy basis: each retarded-resolvent transition coefficient multiplies the rank-one
projector onto its first energy state. The ordinary trace of that projector is one, so expanding
the carrier trace recovers exactly the finite spectral double sum.

This is the finite equivalent permitted at the B2 boundary of issue #367. It is intentionally
basis-resolved because the resolvent energy `Eₘ + ℏω` depends on the outer spectral index. The
main theorem does not introduce a disconnected Bastin law: it proves that the named trace response
is equal to the conductivity already obtained through time-dependent perturbation theory, the
causal Kubo theorem, the finite observation-time limit, and the Kubo–Greenwood expansion.

The Peierls contact expectation, positive finite volume, electric-field conversion factor,
frequency, and positive switching rate remain explicit. No cyclic energy-integral formula,
zero-broadening limit, DC limit, disorder average, trace per unit volume, or thermodynamic limit is
claimed.

A future infinite-dimensional finite-volume extension would require an actual complex trace ideal
for the generally non-self-adjoint current–resolvent products, closure of that ideal under bounded
left and right multiplication, cyclicity for bounded/trace-class products, and integrability of the
energy-dependent trace. Those ingredients are not presently available in the repository and are
not replaced here by compactness or by a self-adjoint spectral trace. Trace per unit volume and the
thermodynamic limit remain separate constructions.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open QuantumTheory.LinearResponse

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype ι]

/-- Rank-one orthogonal projector onto one vector of the supplied pure-point energy basis. -/
noncomputable def purePointBasisProjector
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι) (m : ι) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  ContinuousLinearMap.toSpanSingleton ℂ (data.basis m) ∘L
    ContinuousLinearMap.innerSL ℂ (data.basis m)

/-- The energy-basis projector acts by the corresponding Kronecker coefficient. -/
@[simp]
theorem purePointBasisProjector_apply
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι) (m n : ι) :
    purePointBasisProjector system data m (data.basis n) =
      (if m = n then (1 : ℂ) else 0) • data.basis m := by
  classical
  simp [purePointBasisProjector,
    orthonormal_iff_ite.mp data.basis.orthonormal]

/-- The ordinary finite-dimensional trace of one normalized energy-basis projector is one. -/
theorem linearMap_trace_purePointBasisProjector
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι) (m : ι) :
    LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
        (purePointBasisProjector system data m :
          FiniteLatticeHilbertFock Site →ₗ[ℂ] FiniteLatticeHilbertFock Site) = 1 := by
  classical
  rw [LinearMap.trace_eq_sum_inner
    (purePointBasisProjector system data m :
      FiniteLatticeHilbertFock Site →ₗ[ℂ] FiniteLatticeHilbertFock Site) data.basis]
  simp [purePointBasisProjector,
    orthonormal_iff_ite.mp data.basis.orthonormal, eq_comm]

/-- Finite-dimensional trace carrier for the regularized Kubo–Bastin current-current response.

All current, Hamiltonian, Fermi-probability, frequency, and resolvent dependence is contained in
the transition coefficients inherited from `finiteKuboBastinSpectralDirectionalCurrentTerm`. -/
noncomputable def finiteKuboBastinDirectionalTraceCarrier
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    FiniteLatticeHilbertFock Site →ₗ[ℂ] FiniteLatticeHilbertFock Site :=
  ∑ mn : ι × ι,
    finiteKuboBastinSpectralDirectionalCurrentTerm
        system data geometry direction K q omega eta mn •
      (purePointBasisProjector system data mn.1 :
        FiniteLatticeHilbertFock Site →ₗ[ℂ] FiniteLatticeHilbertFock Site)

/-- Expanding the ordinary trace carrier gives the finite retarded-resolvent spectral sum. -/
theorem linearMap_trace_finiteKuboBastinDirectionalTraceCarrier
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
        (finiteKuboBastinDirectionalTraceCarrier
          system data geometry direction K q omega eta) =
      ∑ mn : ι × ι,
        finiteKuboBastinSpectralDirectionalCurrentTerm
          system data geometry direction K q omega eta mn := by
  classical
  unfold finiteKuboBastinDirectionalTraceCarrier
  simp [linearMap_trace_purePointBasisProjector]

/-- Named ordinary finite-dimensional Kubo–Bastin conductivity.

The current-current term is an ordinary finite-dimensional trace; the Peierls contact expectation
and the finite-volume electric-field normalization remain separate and explicit. -/
noncomputable def finiteDimensionalKuboBastinDirectionalConductivity
    (convention : FiniteVolumeConductivityConvention)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) : ℂ :=
  (LinearMap.trace ℂ (FiniteLatticeHilbertFock Site)
      (finiteKuboBastinDirectionalTraceCarrier
        system data geometry direction K q omega eta) +
    purePointNormalizedExpectation system data
      (boundedDirectionalContact geometry direction
        (system.hbar : ℂ) (q : ℂ) K)) *
    finiteVolumeConductivityNormalization convention omega eta

/-- The ordinary trace definition has exactly the finite spectral/Lehmann representation proved in
`KuboBastinSpectral`. -/
theorem finiteDimensionalKuboBastinDirectionalConductivity_eq_spectral
    (convention : FiniteVolumeConductivityConvention)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) :
    finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta =
      finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention := by
  unfold finiteDimensionalKuboBastinDirectionalConductivity
    finiteKuboBastinSpectralDirectionalConductivity
  rw [linearMap_trace_finiteKuboBastinDirectionalTraceCarrier]

/-- Main B2 identification: the ordinary finite-dimensional Kubo–Bastin trace response is exactly
the conductivity derived from the causal Kubo response chain, at fixed positive switching rate. -/
theorem infiniteTimeAdiabaticDirectionalConductivity_eq_finiteDimensionalKuboBastin
    (convention : FiniteVolumeConductivityConvention)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q omega eta : ℝ) (heta : 0 < eta) :
    infiniteTimeAdiabaticDirectionalConductivity convention
        system (purePointNormalizedExpectation system data)
          geometry direction K q omega eta =
      finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta := by
  calc
    infiniteTimeAdiabaticDirectionalConductivity convention
        system (purePointNormalizedExpectation system data)
          geometry direction K q omega eta =
      finiteKuboGreenwoodDirectionalConductivity
        convention system data geometry direction K q omega eta :=
      infiniteTimeAdiabaticDirectionalConductivity_eq_finiteKuboGreenwood
        convention system data geometry direction K q omega eta heta
    _ = finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q omega eta convention :=
      finiteKuboGreenwoodDirectionalConductivity_eq_bastinSpectral
        system data geometry direction K q omega eta convention heta
    _ = finiteDimensionalKuboBastinDirectionalConductivity
        convention system data geometry direction K q omega eta :=
      (finiteDimensionalKuboBastinDirectionalConductivity_eq_spectral
        convention system data geometry direction K q omega eta).symm

end
end Field
end Fermionic
end SecondQuantization
