import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.StaticKuboBastinResponse
import LeanCondensedMatter.Transport.Streda.SpectralEnergyIntegral

set_option linter.style.header false

/-!
# Static Bastin energy representation

The finite static conductivity is obtained from a zero-frequency vector-potential response by the
explicit factor `1 / (V (-η))`. Identifying that response with the canonical traced Bastin energy
integral is a separate energy-representation statement. It should not, by itself, be called a Ward
identity: a concrete proof may combine resolvent algebra, a Peierls/contact sum rule, and limiting or
regularity input.

This module owns that missing statement independently of any particular Ward or contact-sum-rule
hypothesis. Downstream modules may construct the representation from model-specific input without
making this layer depend on those models.

No equality between the finite-broadening common-energy kernel and the canonical Bastin integrand is
claimed here. In particular, such a pointwise equality is not expected for an arbitrary occupation
interpolation at finite broadening.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse QuantumTheory.Transport

noncomputable section

variable {Site E ι : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]
variable [Fintype ι]

/-- Explicit energy-representation hypothesis for the complete static vector-potential response.

It states that the current-current spectral response together with the Peierls contact term equals
`V (-η)` times the canonical traced Bastin energy integral. The finite-volume/electric-field factor
is intentionally visible. -/
structure FiniteStaticBastinEnergyRepresentation
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ) : Prop where
  vectorPotentialResponse_eq_scaledTracedBastin :
    finiteStaticKuboBastinVectorPotentialResponse
        system data geometry direction K q eta =
      ((convention.volume : ℂ) * (-(eta : ℂ))) *
        regularizedTracedBastinEnergyIntegral
          system.hamiltonian.1
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          (kuboBastinEnergyBroadening system.hbar eta)
          lowerEnergy upperEnergy occupation

/-- A static Bastin energy representation cancels the explicit finite-volume zero-frequency
normalization and identifies the named static conductivity with the canonical traced Bastin energy
integral. -/
theorem FiniteStaticBastinEnergyRepresentation.staticConductivity_eq_tracedBastin
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ)
    (representation : FiniteStaticBastinEnergyRepresentation convention system data
      geometry direction K q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    finiteStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta =
      regularizedTracedBastinEnergyIntegral
        system.hamiltonian.1
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation := by
  rw [finiteStaticKuboBastinDirectionalConductivity_eq_vectorPotential]
  rw [representation.vectorPotentialResponse_eq_scaledTracedBastin]
  rw [finiteVolumeConductivityNormalization_zero_frequency]
  let denominator : ℂ := (convention.volume : ℂ) * (-(eta : ℂ))
  let integral : ℂ := regularizedTracedBastinEnergyIntegral
    system.hamiltonian.1
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (boundedDirectionalCurrent geometry direction
      (system.hbar : ℂ) (q : ℂ) K)
    (kuboBastinEnergyBroadening system.hbar eta)
    lowerEnergy upperEnergy occupation
  have hdenominator : denominator ≠ 0 := by
    dsimp [denominator]
    simpa using finiteVolumeConductivityDenominator_ne_zero convention 0 eta heta
  change (denominator * integral) * denominator⁻¹ = integral
  calc
    (denominator * integral) * denominator⁻¹ =
        integral * (denominator * denominator⁻¹) := by ring
    _ = integral := by simp [hdenominator]

/-- The same explicit energy representation written using the finite pure-point spectral expansion
of the canonical Bastin trace. -/
theorem FiniteStaticBastinEnergyRepresentation.staticConductivity_eq_spectralEnergyIntegral
    (convention : QuantumTheory.Transport.PositiveVolume)
    (system : BoundedFreeSystem (FiniteLatticeHilbertFock Site))
    (data : PurePointLehmannData system ι)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (q eta lowerEnergy upperEnergy : ℝ)
    (occupation : ℝ → ℂ)
    (representation : FiniteStaticBastinEnergyRepresentation convention system data
      geometry direction K q eta lowerEnergy upperEnergy occupation)
    (heta : 0 < eta) :
    finiteStaticKuboBastinDirectionalConductivity
        convention system data geometry direction K q eta =
      regularizedBastinSpectralEnergyIntegral
        system data
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation := by
  calc
    _ = regularizedTracedBastinEnergyIntegral
        system.hamiltonian.1
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (boundedDirectionalCurrent geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
        (kuboBastinEnergyBroadening system.hbar eta)
        lowerEnergy upperEnergy occupation :=
      representation.staticConductivity_eq_tracedBastin
        convention system data geometry direction K q eta
          lowerEnergy upperEnergy occupation heta
    _ = _ := regularizedTracedBastinEnergyIntegral_eq_spectral
      system data
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      (kuboBastinEnergyBroadening system.hbar eta)
      lowerEnergy upperEnergy occupation
      (kuboBastinEnergyBroadening_pos system.hbar eta system.hbar_pos heta)

end
end Transport
end Fermionic
end SecondQuantization
