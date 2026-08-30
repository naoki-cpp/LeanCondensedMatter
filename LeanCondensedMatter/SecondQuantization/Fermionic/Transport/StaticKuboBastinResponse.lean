import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinSpectral
import LeanCondensedMatter.Transport.Streda.ConductivityMatrix
import LeanCondensedMatter.Transport.Streda.GeneralizedStatic

set_option linter.style.header false

/-!
# Static conductivity matrix from finite Kubo–Bastin response

The existing one-direction static response remains the canonical diagonal path. This module adds the
minimal two-direction static response needed to form conductivity components `σ_ij`, without
rewriting the historical diagonal API.

The component response keeps measured-current and source-field directions independent. Peierls
contact terms remain explicit before the finite-volume electric-field normalization. A later Ward/
f-sum bridge identifies each normalized component with a Středa representation.
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

/-- Zero-frequency two-vertex response coefficient for conductivity component `ij`, before the
explicit Peierls contact and electric-field normalization are added. -/
noncomputable def finiteStaticKuboBastinVectorPotentialVertexComponentResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteStaticKuboBastinChannelVertexResponse system data
    (peierlsCurrentComponentResponseChannel geometry measuredDirection sourceDirection
      (system.hbar : ℂ) (q : ℂ) K) eta

/-- Explicit zero-frequency Peierls contact response for conductivity component `ij`, before the
electric-field normalization. -/
noncomputable def finiteStaticPeierlsContactComponentResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) : ℂ :=
  purePointNormalizedExpectation system data
    (boundedMixedDirectionalContact geometry measuredDirection sourceDirection
      (system.hbar : ℂ) (q : ℂ) K)

/-- Complete zero-frequency vector-potential response coefficient for conductivity component `ij`. -/
noncomputable def finiteStaticKuboBastinVectorPotentialComponentResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteStaticKuboBastinChannelResponse system data
    (peierlsCurrentComponentResponseChannel geometry measuredDirection sourceDirection
      (system.hbar : ℂ) (q : ℂ) K) eta

/-- The complete component response is the two-vertex contribution plus the mixed contact. -/
theorem finiteStaticKuboBastinVectorPotentialComponentResponse_eq_vertex_add_contact
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteStaticKuboBastinVectorPotentialComponentResponse
        system data geometry measuredDirection sourceDirection K q eta =
      finiteStaticKuboBastinVectorPotentialVertexComponentResponse
          system data geometry measuredDirection sourceDirection K q eta +
        finiteStaticPeierlsContactComponentResponse
          system data geometry measuredDirection sourceDirection K q := by
  rfl

/-- Finite-rate static conductivity component `σ_ij`. Only the external driving frequency is set to
zero; positive switching/broadening remains explicit. -/
noncomputable def finiteStaticKuboBastinConductivityComponent
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteStaticKuboBastinVectorPotentialComponentResponse
      system data geometry measuredDirection sourceDirection K q eta *
    finiteVolumeConductivityNormalization convention 0 eta

/-- Coordinate-indexed finite static conductivity matrix before any longitudinal/Hall projection. -/
noncomputable def finiteStaticKuboBastinConductivityMatrix
    {κ : Type*}
    (axes : κ → E →ₗ[ℝ] ℝ)
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : κ → κ → ℂ :=
  fun i j =>
    finiteStaticKuboBastinConductivityComponent
      convention system data geometry (axes i) (axes j) K q eta

/-- Středa-decomposed static conductivity matrix assembled from proved component representations. -/
noncomputable def finiteStaticStredaConductivityMatrix
    {κ : Type*}
    (axes : κ → E →ₗ[ℝ] ℝ)
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (K : LocallyFiniteHopping Site) (q eta : ℝ)
    (representation : ∀ i j : κ,
      RegularizedStredaRepresentation
        (finiteStaticKuboBastinConductivityComponent
          convention system data geometry (axes i) (axes j) K q eta)) :
    StaticStredaConductivityMatrix κ :=
  StaticStredaConductivityMatrix.ofRepresentations
    (fun i j =>
      finiteStaticKuboBastinConductivityComponent
        convention system data geometry (axes i) (axes j) K q eta)
    representation

/-- The assembled Středa matrix reproduces the finite static conductivity componentwise. -/
theorem finiteStaticStredaConductivityMatrix_total_eq_kuboBastin
    {κ : Type*}
    (axes : κ → E →ₗ[ℝ] ℝ)
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (K : LocallyFiniteHopping Site) (q eta : ℝ)
    (representation : ∀ i j : κ,
      RegularizedStredaRepresentation
        (finiteStaticKuboBastinConductivityComponent
          convention system data geometry (axes i) (axes j) K q eta))
    (i j : κ) :
    (finiteStaticStredaConductivityMatrix axes convention system data geometry K q eta
        representation).total i j =
      finiteStaticKuboBastinConductivityMatrix
        axes convention system data geometry K q eta i j := by
  unfold finiteStaticStredaConductivityMatrix finiteStaticKuboBastinConductivityMatrix
  exact StaticStredaConductivityMatrix.ofRepresentations_total
    (fun a b =>
      finiteStaticKuboBastinConductivityComponent
        convention system data geometry (axes a) (axes b) K q eta)
    representation i j

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
finite; only the driving frequency is specialized to zero. -/
noncomputable def finiteStaticKuboBastinDirectionalConductivity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralDirectionalConductivity
    system data geometry direction K q 0 eta convention

/-- The component conductivity reduces to the historical directional conductivity on the diagonal. -/
@[simp]
theorem finiteStaticKuboBastinConductivityComponent_self
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteStaticKuboBastinConductivityComponent
        convention system data geometry direction direction K q eta =
      finiteStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta := by
  unfold finiteStaticKuboBastinConductivityComponent
    finiteStaticKuboBastinVectorPotentialComponentResponse
    finiteStaticKuboBastinChannelResponse
    finiteKuboBastinSpectralChannelResponse
    peierlsCurrentComponentResponseChannel
    finiteStaticKuboBastinDirectionalConductivity
    finiteKuboBastinSpectralDirectionalConductivity
  rw [boundedMixedDirectionalContact_self]

/-- The static conductivity is the retained vector-potential coefficient multiplied by the exact
zero-frequency finite-volume electric-field normalization. -/
theorem finiteStaticKuboBastinDirectionalConductivity_eq_vectorPotential
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
  simp [finiteVolumeConductivityNormalization]

end
end Transport
end Fermionic
end SecondQuantization
