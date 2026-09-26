import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinSpectral
import LeanCondensedMatter.Transport.Streda.GeneralizedStatic

set_option linter.style.header false

/-!
# Static target of the finite spectral Kubo–Bastin response

The finite spectral response depends on frequency and positive switching rate and includes both the
explicit Peierls contact term and finite-volume electric-field normalization. The static target used
for comparison with Smrčka–Středa representations is obtained by fixing `ω = 0`.

This module separates that static vector-potential response coefficient from the final
current-density/electric-field normalization. It does not convert the scalar response into an
operator trace by multiplying by a trace-one density operator; operator traces enter through the
static Bastin layer in `Transport.Streda.TraceKernel`.

The Smrčka–Středa terminology follows L. Smrčka and P. Středa, *J. Phys. C* **10**, 2153 (1977),
[doi:10.1088/0022-3719/10/12/021](https://doi.org/10.1088/0022-3719/10/12/021).
These declarations remain finite-volume and finite-broadening and do not assert a DC or
thermodynamic-limit theorem.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype ι]

/-- Neutral response-channel packaging used by the static directional charge-current target. -/
private noncomputable def staticDirectionalChargeResponseChannel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) :
    ResponseChannel (FiniteLatticeHilbertFock Site) where
  measured := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  source := boundedDirectionalCurrent geometry direction
    (system.hbar : ℂ) (q : ℂ) K
  observableVariation := boundedDirectionalContact geometry direction
    (system.hbar : ℂ) (q : ℂ) K

/-- Zero-frequency vector-potential response coefficient, retaining the finite spectral
current-current response and explicit Peierls contact expectation. -/
noncomputable def finiteStaticKuboBastinVectorPotentialResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteStaticKuboBastinChannelResponse system data
    (staticDirectionalChargeResponseChannel system geometry direction K q) eta

/-- Named finite static Kubo–Bastin conductivity target. The switching rate remains positive and
finite; only the driving frequency is specialized to zero. The Smrcka--Streda terminology follows
L. Smrcka and P. Streda, *J. Phys. C* **10**, 2153 (1977),
[doi:10.1088/0022-3719/10/12/021](https://doi.org/10.1088/0022-3719/10/12/021); no DC or
thermodynamic-limit claim is made here. -/
noncomputable def finiteStaticKuboBastinDirectionalConductivity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralDirectionalConductivity
    system data geometry direction K q 0 eta convention

/-- The static conductivity is the retained vector-potential coefficient multiplied by the exact
zero-frequency finite-volume electric-field normalization. -/
theorem finiteStaticKuboBastinDirectionalConductivity_eq_vectorPotentialResponse_mul_normalization
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta =
      finiteStaticKuboBastinVectorPotentialResponse
          system data geometry direction K q eta *
        finiteVolumeConductivityNormalization convention 0 eta := by
  rfl

/-- Expanding the static spectral response gives the finite zero-frequency transition sum plus the
unchanged contact expectation. -/
theorem finiteStaticKuboBastinVectorPotentialResponse_eq_finite_sum
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteStaticKuboBastinVectorPotentialResponse
        system data geometry direction K q eta =
      (∑ mn : ι × ι,
        finiteKuboBastinSpectralDirectionalCurrentTerm
          system data geometry direction K q 0 eta mn) +
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K) := by
  rfl

/-- Exact finite spectral form of the named static conductivity target. -/
theorem finiteStaticKuboBastinDirectionalConductivity_eq_finite_sum
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta =
      ((∑ mn : ι × ι,
        finiteKuboBastinSpectralDirectionalCurrentTerm
          system data geometry direction K q 0 eta mn) +
        purePointNormalizedExpectation system data
          (boundedDirectionalContact geometry direction
            (system.hbar : ℂ) (q : ℂ) K)) *
        finiteVolumeConductivityNormalization convention 0 eta := by
  rfl

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
      finiteStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta := by
  calc
    _ = finiteKuboGreenwoodDirectionalConductivity
        convention system data geometry direction K q 0 eta :=
      infiniteTimeAdiabaticDirectionalConductivity_eq_finiteKuboGreenwood
        convention system data geometry direction K q 0 eta heta
    _ = finiteKuboBastinSpectralDirectionalConductivity
        system data geometry direction K q 0 eta convention :=
      finiteKuboGreenwoodDirectionalConductivity_eq_bastinSpectral
        system data geometry direction K q 0 eta convention heta
    _ = _ := rfl

/-- At zero frequency, the electric-field normalization keeps the finite switching rate and volume
explicit. -/
theorem finiteVolumeConductivityNormalization_zero_frequency
    (convention : QuantumTheory.Transport.PositiveVolume) (eta : ℝ) :
    finiteVolumeConductivityNormalization convention 0 eta =
      (((convention.volume : ℂ) * (-(eta : ℂ))))⁻¹ := by
  simp [finiteVolumeConductivityNormalization, adiabaticElectricFieldFactor]

end
end Transport
end Fermionic
end SecondQuantization
