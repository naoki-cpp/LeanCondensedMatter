import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoSiteDimer

set_option linter.style.header false

/-!
# Zero-parameter checks for the two-site dimer

In addition to the orientation/sign symmetries recorded in `TwoSiteDimer`, the physical dimer
operators vanish when the hopping is turned off, and the Peierls current/contact vanish when the
electric charge is set to zero.

These are finite-operator identities. No singular DC, zero-broadening, or thermodynamic limit is
being taken.
-/

namespace SecondQuantization
namespace Fermionic
namespace Validation

open _root_.SecondQuantization.Fermionic.Lattice

noncomputable section

/-- Turning off the hopping removes the bounded dimer Hamiltonian. -/
@[simp]
theorem twoSiteDimerHamiltonian_zero :
    twoSiteDimerHamiltonian 0 = 0 := by
  simp [twoSiteDimerHamiltonian]

/-- Turning off the hopping removes the continuity-derived dimer current. -/
@[simp]
theorem twoSiteDimerCurrent_zero_hopping :
    twoSiteDimerCurrent 0 = 0 := by
  rw [twoSiteDimerCurrent, boundedBondCurrent_eq_peierlsCoupling_smul]
  rw [LocallyFiniteHopping.boundedBondOperator_eq]
  simp [LocallyFiniteHopping.amplitude_eq]

/-- Turning off the hopping also removes the Peierls contact operator. -/
@[simp]
theorem twoSiteDimerContact_zero_hopping :
    twoSiteDimerContact 0 = 0 := by
  unfold twoSiteDimerContact boundedBondContact bondContact
  simp [LocallyFiniteHopping.oneParticleBondContact,
    LocallyFiniteHopping.amplitude_eq, peierlsCoupling]

/-- At zero charge, the dimer bond carries no Peierls current. -/
@[simp]
theorem twoSiteDimerBondCurrent_zero_charge (t : ℂ) :
    boundedBondCurrent (1 : ℂ) 0 (twoSiteDimerHopping t) 0 1 = 0 := by
  rw [boundedBondCurrent_eq_peierlsCoupling_smul]
  simp [peierlsCoupling]

/-- At zero charge, the source derivative of the Peierls current also vanishes. -/
@[simp]
theorem twoSiteDimerBondContact_zero_charge (t : ℂ) :
    boundedBondContact (twoSiteDimerHopping t) (1 : ℂ) 0 0 1 = 0 := by
  unfold boundedBondContact bondContact
  simp [LocallyFiniteHopping.oneParticleBondContact, peierlsCoupling]

end
end Validation
end Fermionic
end SecondQuantization
