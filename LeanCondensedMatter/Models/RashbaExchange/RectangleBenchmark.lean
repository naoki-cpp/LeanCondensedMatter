import LeanCondensedMatter.Models.RashbaExchange.SpinDisplacementBridge

set_option linter.style.header false

/-! # Centered open 2 × 3 Rashba benchmark

The same geometry and parameters as the numerical reference, with one electron
in a lowest-energy orbital. The spectral theorem orders the energies in
descending order, so the last index is occupied. The spin observable uses
`spinScale = 1` in the API `S_z = spinScale * σ_z / 2`, i.e. physical
spin `σ_z / 2` as in the reference. No bulk or DC limit is taken.
-/

namespace QuantumTheory.Models.RashbaExchange

open QuantumTheory.SpinfulLattice QuantumTheory.LinearResponse
open SecondQuantization.Fermionic.Lattice SecondQuantization.Fermionic.Transport

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section

namespace RectangleBenchmark

abbrev Site := RectangularSite 2 3

abbrev OneParticleSpace := EuclideanSpace ℂ (SpinfulSite Site)

/-- Center the open rectangle at (1/2, 1). -/
def geometry : LatticeGeometry Site (ℝ × ℝ) where
  position x := (((ofLex x).1.val : ℝ) - 1 / 2, ((ofLex x).2.val : ℝ) - 1)

/-- With unit spacing and hbar these give hopping t = 1 and SOC c = 1/2. -/
def params : HamiltonianParameters := ⟨1 / 2, 1, 1 / 2⟩

/-- Actual one-particle Hamiltonian of the centered rectangle. -/
def system : BoundedFreeSystem OneParticleSpace :=
  realSpaceRashbaOneParticleFreeSystem geometry (rectangularRashbaBonds params 1 1)
    (fun _ => 4) (fun _ => 1 / 2) 1 (by norm_num)

/-- The final index of the descending finite spectral ordering. -/
def occupied : Fin (Module.finrank ℂ OneParticleSpace) :=
  ⟨Module.finrank ℂ OneParticleSpace - 1, by
    have h := Module.finrank_pos (R := ℂ) (M := OneParticleSpace)
    omega⟩

/-- The selected energy really is minimal among the entire one-particle spectrum. -/
theorem occupied_energy_min (i : Fin (Module.finrank ℂ OneParticleSpace)) :
    (EnergyEigenbasisLehmannData.ofSingleOccupied system occupied).energy occupied ≤
      (EnergyEigenbasisLehmannData.ofSingleOccupied system occupied).energy i := by
  have hi : i ≤ occupied := by
    change i.val ≤ Module.finrank ℂ OneParticleSpace - 1
    have h := i.isLt
    omega
  exact system.hamiltonian.2.isSymmetric.eigenvalues_antitone rfl hi

/-- Proper spin conductivity for y flow, z spin and x electric source at
the specified positive switching rate. This is the physical Fock response,
including the Peierls contact term. -/
def conductivityYX : ℂ :=
  let data := EnergyEigenbasisLehmannData.ofSingleOccupied system occupied
  let ψ : StateVector OneParticleSpace :=
    ⟨data.basis occupied, data.basis.orthonormal.1 occupied⟩
  let many := realSpaceRashbaFreeSystem geometry (rectangularRashbaBonds params 1 1)
    (fun _ => 4) (fun _ => 1 / 2) 1 (by norm_num)
  let channel := realSpaceRashbaSpinDisplacementResponseChannel
    geometry (rectangularRashbaBonds params 1 1) (fun _ => 4) (fun _ => 1 / 2)
    (LinearMap.snd ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ) 1 1 1
    (SpinHalf.cartesianBasisVector .z) 1
  QuantumTheory.Transport.finiteVolumeConductivityFromVectorPotential
    ⟨6, by norm_num⟩ (7 / 10) (1 / 5)
    (channel.infiniteTimeAdiabaticResponse (freePropagatorGroup many) 1
      (QuantumTheory.pure (oneParticleFockState ψ)).toNormalizedExpectation (7 / 10) (1 / 5))

/-- The actual benchmark conductivity is the one-particle Lehmann response
of the centered displacement and geometric charge source. -/
theorem conductivityYX_eq_finiteLehmannTable :
    let K := realSpaceRashbaHopping geometry (rectangularRashbaBonds params 1 1)
      (fun _ => 4) (fun _ => 1 / 2)
    let D := SecondQuantization.Common.finiteHilbertOperatorAlgEquiv
      (LinearMap.symmetrizedProduct (K := ℂ)
        ((spinfulGeometry geometry).directionalPosition (LinearMap.snd ℝ ℝ ℝ))
        (spinOneBodyLinear (Site := Site) 1 (SpinHalf.cartesianBasisVector .z)))
    let B := SecondQuantization.Common.finiteHilbertOperatorAlgEquiv
      (QuantumTheory.PeierlsPhase.peierlsCoupling 1 1 •
        ⁅K.operator, (spinfulGeometry geometry).directionalPosition (LinearMap.fst ℝ ℝ ℝ)⁆)
    conductivityYX = -finiteLehmannTableResponse 1 (7 / 10) (1 / 5)
      (finiteLehmannTableOfEigenbasis system
        (EnergyEigenbasisLehmannData.ofSingleOccupied system occupied) D B) / 6 := by
  exact realSpaceRashbaSpinDisplacement_oneElectron_conductivity_eq_finiteLehmannTable
    ⟨6, by norm_num⟩ geometry (rectangularRashbaBonds params 1 1)
    (fun _ => 4) (fun _ => 1 / 2) (LinearMap.snd ℝ ℝ ℝ) (LinearMap.fst ℝ ℝ ℝ)
    1 1 1 (by norm_num) (SpinHalf.cartesianBasisVector .z) occupied
    (7 / 10) (1 / 5) (by norm_num)

end RectangleBenchmark
end
end QuantumTheory.Models.RashbaExchange
