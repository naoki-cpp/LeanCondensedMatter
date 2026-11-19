import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoLevelExplicit
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.HermitianBondCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.PeierlsContact

set_option linter.style.header false

/-!
# Two-site dimer transport validation

This module equips the finite two-site hopping toy with explicit bounded Hamiltonian, current, and
contact operators on the full finite-lattice fermionic Fock space. The Hamiltonian is assembled from
the two second-quantized matrix units with conjugate coefficients. The current is the bounded
oriented bond current of the same Hermitian hopping model at `ℏ = q = 1`, while the contact is the
first Peierls-source derivative of that current family.

The resulting operators provide a finite tight-binding model to which the canonical pointwise
Kubo–Bastin/Středa identity applies directly. Current-orientation reversal is recorded here, while
simultaneous current-sign reversal is provided by the general Středa operator-kernel API. No disorder
average, numerical approximation, or limiting procedure is used.

Zero-hopping and zero-charge specializations are also checked here as finite-operator identities.
-/

namespace SecondQuantization
namespace Fermionic
namespace Validation

open _root_.SecondQuantization.Fermionic.Lattice Transport

open QuantumTheory LinearResponse Transport

noncomputable section

/-- Full finite-dimensional fermionic Fock space of the two-site dimer. -/
abbrev TwoSiteHilbertFock := FiniteLatticeHilbertFock TwoSite

/-- The dimer hopping amplitudes form a Hermitian one-particle matrix. -/
theorem twoSiteDimerHopping_hasHermitianAmplitudes (t : ℂ) :
    (twoSiteDimerHopping t).HasHermitianAmplitudes := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    simp [LocallyFiniteHopping.amplitude_eq, twoSiteDimerHopping]

/-- Bounded second-quantized two-site hopping Hamiltonian
` t |1⟩⟨0| + star t |0⟩⟨1| ` on the finite Fock space. -/
noncomputable def twoSiteDimerHamiltonian (t : ℂ) :
    TwoSiteHilbertFock →L[ℂ] TwoSiteHilbertFock :=
  t • boundedDgammaMatrixUnit 1 0 +
    star t • boundedDgammaMatrixUnit 0 1

/-- The bounded dimer Hamiltonian uses exactly the amplitudes stored by the hopping model. -/
theorem twoSiteDimerHamiltonian_eq_hoppingAmplitudes (t : ℂ) :
    twoSiteDimerHamiltonian t =
      (twoSiteDimerHopping t).amplitude 1 0 • boundedDgammaMatrixUnit 1 0 +
        (twoSiteDimerHopping t).amplitude 0 1 • boundedDgammaMatrixUnit 0 1 := by
  simp [twoSiteDimerHamiltonian, LocallyFiniteHopping.amplitude_eq, twoSiteDimerHopping]

/-- Conjugate hopping amplitudes make the bounded dimer Hamiltonian self-adjoint. -/
theorem twoSiteDimerHamiltonian_selfAdjoint (t : ℂ) :
    IsSelfAdjoint (twoSiteDimerHamiltonian t) := by
  rw [isSelfAdjoint_iff]
  simp [twoSiteDimerHamiltonian, add_comm]

/-- Bounded free system defined by the two-site dimer Hamiltonian, with `ℏ = 1`. -/
noncomputable def twoSiteDimerSystem (t : ℂ) :
    BoundedFreeSystem TwoSiteHilbertFock where
  hamiltonian := ⟨twoSiteDimerHamiltonian t, twoSiteDimerHamiltonian_selfAdjoint t⟩
  hbar := 1
  hbar_pos := by norm_num

/-- Explicit bounded current supplied by the oriented dimer bond at `ℏ = q = 1`. -/
noncomputable def twoSiteDimerCurrent (t : ℂ) :
    TwoSiteHilbertFock →L[ℂ] TwoSiteHilbertFock :=
  boundedBondCurrent (1 : ℂ) (1 : ℂ) (twoSiteDimerHopping t) 0 1

/-- Explicit bounded Peierls contact supplied by the same oriented dimer bond at `ℏ = q = 1`. -/
noncomputable def twoSiteDimerContact (t : ℂ) :
    TwoSiteHilbertFock →L[ℂ] TwoSiteHilbertFock :=
  boundedBondContact (twoSiteDimerHopping t) (1 : ℂ) (1 : ℂ) 0 1

/-- Hermiticity of the hopping model makes the supplied dimer current self-adjoint. -/
theorem twoSiteDimerCurrent_selfAdjoint (t : ℂ) :
    IsSelfAdjoint (twoSiteDimerCurrent t) := by
  simpa [twoSiteDimerCurrent] using
    isSelfAdjoint_boundedBondCurrent_ofReal
      (twoSiteDimerHopping t)
      (twoSiteDimerHopping_hasHermitianAmplitudes t)
      (1 : ℝ) (1 : ℝ) 0 1

/-- Reversing the oriented dimer bond negates its bounded current. -/
theorem twoSiteDimerCurrent_reverse (t : ℂ) :
    boundedBondCurrent (1 : ℂ) (1 : ℂ) (twoSiteDimerHopping t) 1 0 =
      -twoSiteDimerCurrent t := by
  simpa [twoSiteDimerCurrent] using
    boundedBondCurrent_swap (1 : ℂ) (1 : ℂ) (twoSiteDimerHopping t) 0 1

/-! ## Zero-hopping and zero-charge checks

All zero-parameter results below are finite-operator identities, not singular frequency,
broadening, or thermodynamic limits.
-/

section ZeroParameterChecks

open QuantumTheory.PeierlsPhase

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
  simp [twoSiteDimerHopping, LocallyFiniteHopping.amplitude_eq]

/-- Turning off the hopping also removes the Peierls contact operator. -/
@[simp]
theorem twoSiteDimerContact_zero_hopping :
    twoSiteDimerContact 0 = 0 := by
  unfold twoSiteDimerContact boundedBondContact
  simp [LocallyFiniteHopping.oneParticleBondContact, twoSiteDimerHopping,
    LocallyFiniteHopping.amplitude_eq, peierlsCoupling, boundedLatticeOperator]

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
  unfold boundedBondContact
  simp [LocallyFiniteHopping.oneParticleBondContact, peierlsCoupling,
    boundedLatticeOperator]

end ZeroParameterChecks

end
end Validation
end Fermionic
end SecondQuantization
