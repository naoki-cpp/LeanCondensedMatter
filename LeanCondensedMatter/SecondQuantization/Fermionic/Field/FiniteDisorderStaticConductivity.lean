import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StaticStredaWardBridge
import LeanCondensedMatter.Transport.FiniteDisorder

set_option linter.style.header false

/-!
# Exact finite-disorder average of the static Kubo–Středa conductivity

A finite disorder ensemble changes the bounded Hamiltonian configuration by configuration. This
module applies the already derived finite-dimensional static Kubo–Bastin conductivity to every
exact Hamiltonian `Hω = H₀ + Vω` and then averages the resulting complex conductivity with the
normalized finite probability weight.

The Peierls contact term and finite-volume electric-field normalization remain inside each
configuration-wise conductivity. Identifying that conductivity with a traced Bastin energy
integral, and hence with a Středa surface-plus-sea split, requires a visible finite-rate Ward
identity and analytic integration data for every configuration. Under those assumptions, finite
averaging preserves the split exactly.

No Gaussian law, independence assumption, weak-scattering expansion, Born approximation,
self-consistency, vertex approximation, trace per unit volume, or thermodynamic limit is used.
-/

namespace SecondQuantization
namespace Fermionic
namespace Field

open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E Ω ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype Ω] [Fintype ι]

/-- Exact static Kubo–Bastin conductivity of one finite disorder configuration. The spectral data
and Peierls hopping/current model are supplied configuration by configuration. -/
noncomputable def finiteDisorderConfigurationStaticConductivity
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : ∀ ω,
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : FiniteVolumeConductivityConvention)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (hopping : Ω → LocallyFiniteHopping Site)
    (q eta : ℝ) (ω : Ω) : ℂ :=
  finiteDimensionalStaticKuboBastinDirectionalConductivity
    convention
    (ensemble.configurationSystem hbar hbar_pos ω)
    (spectralData ω) geometry direction (hopping ω) q eta

/-- Exact normalized finite-ensemble average of the configuration-wise static conductivity. -/
noncomputable def finiteDisorderAveragedStaticConductivity
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : ∀ ω,
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : FiniteVolumeConductivityConvention)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (hopping : Ω → LocallyFiniteHopping Site)
    (q eta : ℝ) : ℂ :=
  ensemble.average fun ω =>
    finiteDisorderConfigurationStaticConductivity
      ensemble hbar hbar_pos spectralData convention
      geometry direction hopping q eta ω

/-- The exact averaged conductivity is the explicit normalized finite configuration sum. -/
theorem finiteDisorderAveragedStaticConductivity_eq_sum
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : ∀ ω,
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : FiniteVolumeConductivityConvention)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (hopping : Ω → LocallyFiniteHopping Site)
    (q eta : ℝ) :
    finiteDisorderAveragedStaticConductivity
        ensemble hbar hbar_pos spectralData convention
          geometry direction hopping q eta =
      ∑ ω, (ensemble.probability ω : ℂ) *
        finiteDisorderConfigurationStaticConductivity
          ensemble hbar hbar_pos spectralData convention
            geometry direction hopping q eta ω := by
  rfl

/-- Exact finite-ensemble average of the regularized Středa Fermi-surface contribution supplied
by the configuration-wise analytic data. -/
noncomputable def finiteDisorderAveragedStredaFermiSurface
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    {hbar : ℝ} {hbar_pos : 0 < hbar}
    {geometry : LatticeGeometry Site E} {direction : E →ₗ[ℝ] ℝ}
    {hopping : Ω → LocallyFiniteHopping Site}
    {q eta lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (analyticData : ∀ ω, TracedStredaAnalyticData
      (ensemble.configurationSystem hbar hbar_pos ω).hamiltonian.1
      (boundedDirectionalCurrent geometry direction
        ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ)
        (q : ℂ) (hopping ω))
      (boundedDirectionalCurrent geometry direction
        ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ)
        (q : ℂ) (hopping ω))
      (kuboBastinEnergyBroadening
        (ensemble.configurationSystem hbar hbar_pos ω).hbar eta)
      lowerEnergy upperEnergy occupation occupationDerivative) : ℂ :=
  ensemble.average fun ω =>
    regularizedStredaFermiSurface
      (analyticData ω).toRegularizedStredaIntegralData

/-- Exact finite-ensemble average of the regularized Středa Fermi-sea contribution supplied by
the configuration-wise analytic data. -/
noncomputable def finiteDisorderAveragedStredaFermiSea
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    {hbar : ℝ} {hbar_pos : 0 < hbar}
    {geometry : LatticeGeometry Site E} {direction : E →ₗ[ℝ] ℝ}
    {hopping : Ω → LocallyFiniteHopping Site}
    {q eta lowerEnergy upperEnergy : ℝ}
    {occupation occupationDerivative : ℝ → ℂ}
    (analyticData : ∀ ω, TracedStredaAnalyticData
      (ensemble.configurationSystem hbar hbar_pos ω).hamiltonian.1
      (boundedDirectionalCurrent geometry direction
        ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ)
        (q : ℂ) (hopping ω))
      (boundedDirectionalCurrent geometry direction
        ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ)
        (q : ℂ) (hopping ω))
      (kuboBastinEnergyBroadening
        (ensemble.configurationSystem hbar hbar_pos ω).hbar eta)
      lowerEnergy upperEnergy occupation occupationDerivative) : ℂ :=
  ensemble.average fun ω =>
    regularizedStredaFermiSea
      (analyticData ω).toRegularizedStredaIntegralData

/-- Under the visible Ward and analytic assumptions for one configuration, its exact static
conductivity has the regularized Středa surface-plus-sea representation. -/
theorem finiteDisorderConfigurationStaticConductivity_eq_surface_add_sea
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : ∀ ω,
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : FiniteVolumeConductivityConvention)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (hopping : Ω → LocallyFiniteHopping Site)
    (q eta lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ)
    (analyticData : ∀ ω, TracedStredaAnalyticData
      (ensemble.configurationSystem hbar hbar_pos ω).hamiltonian.1
      (boundedDirectionalCurrent geometry direction
        ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ)
        (q : ℂ) (hopping ω))
      (boundedDirectionalCurrent geometry direction
        ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ)
        (q : ℂ) (hopping ω))
      (kuboBastinEnergyBroadening
        (ensemble.configurationSystem hbar hbar_pos ω).hbar eta)
      lowerEnergy upperEnergy occupation occupationDerivative)
    (ward : ∀ ω, FiniteStaticPeierlsWardIdentity
      convention (ensemble.configurationSystem hbar hbar_pos ω)
      (spectralData ω) geometry direction (hopping ω)
      q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) (ω : Ω) :
    finiteDisorderConfigurationStaticConductivity
        ensemble hbar hbar_pos spectralData convention
          geometry direction hopping q eta ω =
      regularizedStredaFermiSurface
          (analyticData ω).toRegularizedStredaIntegralData +
        regularizedStredaFermiSea
          (analyticData ω).toRegularizedStredaIntegralData := by
  exact (analyticData ω).staticKuboBastinConductivity_eq_surface_add_sea
    convention (ensemble.configurationSystem hbar hbar_pos ω)
    (spectralData ω) geometry direction (hopping ω)
    q eta lowerEnergy upperEnergy occupation occupationDerivative
    (ward ω) heta

/-- Exact finite disorder averaging preserves the regularized Středa surface-plus-sea split. All
contact cancellation and electric-field normalization remain configuration-wise consequences of
the explicitly supplied Ward identities. -/
theorem finiteDisorderAveragedStaticConductivity_eq_surface_add_sea
    (ensemble : FiniteDisorderEnsemble
      (H := FiniteLatticeHilbertFock Site) (Ω := Ω))
    (hbar : ℝ) (hbar_pos : 0 < hbar)
    (spectralData : ∀ ω,
      PurePointLehmannData (ensemble.configurationSystem hbar hbar_pos ω) ι)
    (convention : FiniteVolumeConductivityConvention)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (hopping : Ω → LocallyFiniteHopping Site)
    (q eta lowerEnergy upperEnergy : ℝ)
    (occupation occupationDerivative : ℝ → ℂ)
    (analyticData : ∀ ω, TracedStredaAnalyticData
      (ensemble.configurationSystem hbar hbar_pos ω).hamiltonian.1
      (boundedDirectionalCurrent geometry direction
        ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ)
        (q : ℂ) (hopping ω))
      (boundedDirectionalCurrent geometry direction
        ((ensemble.configurationSystem hbar hbar_pos ω).hbar : ℂ)
        (q : ℂ) (hopping ω))
      (kuboBastinEnergyBroadening
        (ensemble.configurationSystem hbar hbar_pos ω).hbar eta)
      lowerEnergy upperEnergy occupation occupationDerivative)
    (ward : ∀ ω, FiniteStaticPeierlsWardIdentity
      convention (ensemble.configurationSystem hbar hbar_pos ω)
      (spectralData ω) geometry direction (hopping ω)
      q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    finiteDisorderAveragedStaticConductivity
        ensemble hbar hbar_pos spectralData convention
          geometry direction hopping q eta =
      finiteDisorderAveragedStredaFermiSurface ensemble analyticData +
        finiteDisorderAveragedStredaFermiSea ensemble analyticData := by
  unfold finiteDisorderAveragedStaticConductivity
    finiteDisorderAveragedStredaFermiSurface
    finiteDisorderAveragedStredaFermiSea
  rw [← ensemble.average_add]
  apply congrArg ensemble.average
  funext ω
  exact finiteDisorderConfigurationStaticConductivity_eq_surface_add_sea
    ensemble hbar hbar_pos spectralData convention geometry direction hopping
    q eta lowerEnergy upperEnergy occupation occupationDerivative
    analyticData ward heta ω

end
end Field
end Fermionic
end SecondQuantization
