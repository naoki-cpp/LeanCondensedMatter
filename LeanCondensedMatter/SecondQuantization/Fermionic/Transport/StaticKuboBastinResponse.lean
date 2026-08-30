import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinSpectral
import LeanCondensedMatter.Transport.Streda.ConductivityMatrix
import LeanCondensedMatter.Transport.Streda.GeneralizedStatic

set_option linter.style.header false

/-!
# Static conductivity matrix from finite Kubo–Bastin response

The response derived before the Středa layer retains finite frequency, positive switching rate, an
explicit Peierls contact term, and the finite-volume electric-field normalization. A static
Smrčka–Středa bridge therefore begins by fixing `ω = 0` and keeping measured-current and source-field
coordinates independent.

The primary static object in this module is the coordinate-indexed conductivity matrix. A supplied
regularized Středa representation for each current-current vertex component splits that matrix into
Fermi-surface, Fermi-sea, and explicit contact contributions. Longitudinal and Hall responses are
then projections of the same matrix rather than separate foundational formulas.

The Středa surface/sea split is not identified with an intrinsic/extrinsic mechanism split. Genuine
operator traces remain owned by `Transport.Streda.TraceKernel` and `TraceRepresentation`.
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

/-- Complete zero-frequency vector-potential response coefficient for conductivity component `ij`.
This is the two-vertex response plus the Peierls contact response. -/
noncomputable def finiteStaticKuboBastinVectorPotentialComponentResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteStaticKuboBastinChannelResponse system data
    (peierlsCurrentComponentResponseChannel geometry measuredDirection sourceDirection
      (system.hbar : ℂ) (q : ℂ) K) eta

/-- The complete static vector-potential response is vertex plus explicit contact. -/
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

/-- Finite-rate static conductivity component `σ_ij`. Only the external driving frequency has been
set to zero; the positive switching/broadening scale remains explicit. -/
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

/-- Coordinate-indexed finite static conductivity matrix before choosing longitudinal or Hall
projections. -/
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

/-- Středa-decomposed static conductivity matrix for a chosen coordinate family. The required
regularized Středa representation is supplied independently for every two-vertex component; the
Peierls contact remains an explicit third contribution. -/
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
        (finiteStaticKuboBastinVectorPotentialVertexComponentResponse
          system data geometry (axes i) (axes j) K q eta)) :
    StaticStredaConductivityMatrix κ :=
  StaticStredaConductivityMatrix.ofRepresentations
    (fun i j =>
      finiteStaticKuboBastinVectorPotentialVertexComponentResponse
        system data geometry (axes i) (axes j) K q eta)
    (fun i j =>
      finiteStaticPeierlsContactComponentResponse
        system data geometry (axes i) (axes j) K q)
    representation
    (finiteVolumeConductivityNormalization convention 0 eta)

/-- The total of the Středa-decomposed matrix is the finite static Kubo–Bastin conductivity matrix
component by component. -/
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
        (finiteStaticKuboBastinVectorPotentialVertexComponentResponse
          system data geometry (axes i) (axes j) K q eta))
    (i j : κ) :
    (finiteStaticStredaConductivityMatrix axes convention system data geometry K q eta
        representation).total i j =
      finiteStaticKuboBastinConductivityMatrix
        axes convention system data geometry K q eta i j := by
  unfold finiteStaticStredaConductivityMatrix finiteStaticKuboBastinConductivityMatrix
    finiteStaticKuboBastinConductivityComponent
  rw [StaticStredaConductivityMatrix.ofRepresentations_total]
  rw [finiteStaticKuboBastinVectorPotentialComponentResponse_eq_vertex_add_contact]

/-- Neutral response-channel packaging used by the historical diagonal static target. -/
private noncomputable def staticDirectionalChargeResponseChannel
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q : ℝ) :
    ResponseChannel (FiniteLatticeHilbertFock Site) :=
  peierlsCurrentComponentResponseChannel geometry direction direction
    (system.hbar : ℂ) (q : ℂ) K

/-- Historical diagonal zero-frequency vector-potential response coefficient. -/
noncomputable def finiteStaticKuboBastinVectorPotentialResponse
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteStaticKuboBastinChannelResponse system data
    (staticDirectionalChargeResponseChannel system geometry direction K q) eta

/-- Named finite static diagonal Kubo–Bastin conductivity target. -/
noncomputable def finiteStaticKuboBastinDirectionalConductivity
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  finiteKuboBastinSpectralDirectionalConductivity
    system data geometry direction K q 0 eta convention

/-- The component API reproduces the historical directional conductivity on the diagonal. -/
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

/-- The static diagonal conductivity is the retained vector-potential coefficient multiplied by the
exact zero-frequency finite-volume electric-field normalization. -/
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

/-- Expanding the static diagonal spectral response gives the finite zero-frequency transition sum
plus the unchanged contact expectation. -/
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

/-- Exact finite spectral form of the named diagonal static conductivity target. -/
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

/-- The static named diagonal target remains connected to the causal Kubo response at every positive
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
