import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StaticStredaWardBridge
import LeanCondensedMatter.Transport.Disorder.Finite

set_option linter.style.header false

/-!
# Exact finite-disorder static conductivity

The finite disorder ensemble is kept outside the exact response of each configuration. For every
configuration `ω`, this module applies the established finite static Kubo–Bastin conductivity to
the exact Hamiltonian `Hω = H₀ + Vω`, using supplied pure-point spectral data for that Hamiltonian.
The disorder-averaged conductivity is then the normalized finite weighted sum.

A visible family of finite-rate Peierls Ward identities transports the configuration-wise static
conductivity to the canonical traced or spectral Bastin energy integral. These equalities are then
lifted through the finite ensemble average without dropping the Peierls contact term or the
finite-volume electric-field normalization inside any configuration.

No Gaussian law, independence assumption, Born approximation, weak-disorder expansion,
trace-per-volume construction, or thermodynamic limit is introduced here.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open SecondQuantization.Fermionic.Lattice

open scoped BigOperators
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E Ω ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype Ω] [Fintype ι]

/-- Exact static Kubo–Bastin conductivity of one disorder configuration. The hopping geometry,
current convention, charge, switching rate, and finite-volume normalization are common ensemble
data; the Hamiltonian and its supplied pure-point data depend on `ω`. -/
noncomputable def finiteDisorderConfigurationStaticConductivity
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) → PurePointLehmannData
      (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : QuantumTheory.Transport.PositiveVolume)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) (ω : Ω) : ℂ :=
  finiteStaticKuboBastinDirectionalConductivity
    convention (ensemble.configurationSystem hbar hbar_pos ω)
      (spectralData ω) geometry direction K q eta

/-- Exact finite disorder average of the configuration-wise static conductivity. -/
noncomputable def finiteDisorderAveragedStaticConductivity
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) → PurePointLehmannData
      (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : QuantumTheory.Transport.PositiveVolume)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) : ℂ :=
  ensemble.average (fun ω =>
    finiteDisorderConfigurationStaticConductivity
      ensemble hbar hbar_pos spectralData convention
        geometry direction K q eta ω)

/-- The averaged conductivity is the explicit normalized finite configuration sum. -/
theorem finiteDisorderAveragedStaticConductivity_eq_sum
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) → PurePointLehmannData
      (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : QuantumTheory.Transport.PositiveVolume)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta : ℝ) :
    finiteDisorderAveragedStaticConductivity
        ensemble hbar hbar_pos spectralData convention
          geometry direction K q eta =
      ∑ ω, (ensemble.probability ω : ℂ) *
        finiteDisorderConfigurationStaticConductivity
          ensemble hbar hbar_pos spectralData convention
            geometry direction K q eta ω := by
  rfl

/-- A visible configuration-wise Ward identity identifies the exact static conductivity with the
canonical traced Bastin energy integral for that same disordered Hamiltonian. -/
theorem finiteDisorderConfigurationStaticConductivity_eq_tracedBastin
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) → PurePointLehmannData
      (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : QuantumTheory.Transport.PositiveVolume)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site)
    (q eta lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (ω : Ω)
    (ward : FiniteStaticPeierlsWardIdentity convention
      (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω)
      geometry direction K q eta lowerEnergy upperEnergy occupation)
    (heta : eta ≠ 0) :
    finiteDisorderConfigurationStaticConductivity
        ensemble hbar hbar_pos spectralData convention
          geometry direction K q eta ω =
      regularizedTracedBastinEnergyIntegral
        (ensemble.configurationSystem hbar hbar_pos ω).hamiltonian.1
        (boundedDirectionalCurrent geometry direction
          ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ) (q : ℂ) K)
        (kuboBastinEnergyBroadening
          (ensemble.configurationSystem hbar hbar_pos ω).hbar eta)
        lowerEnergy upperEnergy occupation := by
  unfold finiteDisorderConfigurationStaticConductivity
  exact ward.staticConductivity_eq_tracedBastin
    convention (ensemble.configurationSystem hbar hbar_pos ω)
      (spectralData ω) geometry direction K q eta
        lowerEnergy upperEnergy occupation heta

/-- Applying the configuration-wise Ward identity in every configuration lifts the exact
Kubo–Středa identification through the finite disorder average. -/
theorem finiteDisorderAveragedStaticConductivity_eq_tracedBastinAverage
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) → PurePointLehmannData
      (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : QuantumTheory.Transport.PositiveVolume)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site)
    (q eta lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (ward : ∀ ω, FiniteStaticPeierlsWardIdentity convention
      (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω)
      geometry direction K q eta lowerEnergy upperEnergy occupation)
    (heta : eta ≠ 0) :
    finiteDisorderAveragedStaticConductivity
        ensemble hbar hbar_pos spectralData convention
          geometry direction K q eta =
      ensemble.average (fun ω =>
        regularizedTracedBastinEnergyIntegral
          (ensemble.configurationSystem hbar hbar_pos ω).hamiltonian.1
          (boundedDirectionalCurrent geometry direction
            ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry direction
            ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ) (q : ℂ) K)
          (kuboBastinEnergyBroadening
            (ensemble.configurationSystem hbar hbar_pos ω).hbar eta)
          lowerEnergy upperEnergy occupation) := by
  unfold finiteDisorderAveragedStaticConductivity
  apply ensemble.average_congr
  intro ω
  exact finiteDisorderConfigurationStaticConductivity_eq_tracedBastin
    ensemble hbar hbar_pos spectralData convention geometry direction K
      q eta lowerEnergy upperEnergy occupation ω (ward ω) heta

/-- The same exact finite-disorder bridge in the pure-point spectral energy-integral form. -/
theorem finiteDisorderAveragedStaticConductivity_eq_spectralEnergyIntegralAverage
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : (ω : Ω) → PurePointLehmannData
      (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : QuantumTheory.Transport.PositiveVolume)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site)
    (q eta lowerEnergy upperEnergy : ℝ) (occupation : ℝ → ℂ)
    (ward : ∀ ω, FiniteStaticPeierlsWardIdentity convention
      (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω)
      geometry direction K q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    finiteDisorderAveragedStaticConductivity
        ensemble hbar hbar_pos spectralData convention
          geometry direction K q eta =
      ensemble.average (fun ω =>
        regularizedBastinSpectralEnergyIntegral
          (ensemble.configurationSystem hbar hbar_pos ω) (spectralData ω)
          (boundedDirectionalCurrent geometry direction
            ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry direction
            ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ) (q : ℂ) K)
          (kuboBastinEnergyBroadening
            (ensemble.configurationSystem hbar hbar_pos ω).hbar eta)
          lowerEnergy upperEnergy occupation) := by
  unfold finiteDisorderAveragedStaticConductivity
  apply ensemble.average_congr
  intro ω
  exact (ward ω).staticConductivity_eq_spectralEnergyIntegral
    convention (ensemble.configurationSystem hbar hbar_pos ω)
      (spectralData ω) geometry direction K q eta
        lowerEnergy upperEnergy occupation heta

end
end Transport
end Fermionic
end SecondQuantization
