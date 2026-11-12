import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.NumberOperator
import Mathlib.Data.ZMod.Basic

set_option linter.style.header false

/-!
# Quadratic magnons on the ferromagnetic ring

The natural parameter `twiceSpin` is 2s. Each ring bond is counted once, with
exchange convention H = -2J sum S_i dot S_j / hbar^2. The physical ring has N >= 3.
Replacing the transverse HP square-root factors by sqrt(2s), and dropping the
longitudinal number-number term, defines the quadratic approximation here.
Source: Stancil-Prabhakar, Section 2.7.1, equations (2.154)-(2.156), adapted
from its directed-neighbor sum to the bond-once convention of Section 2.5.

The domain is unrestricted algebraic bosonic Fock space, not the capped spin sector.
The quadratic Hamiltonian is not identified with the exact HP Hamiltonian, and no
approximation error bound is asserted. TransverseReplacement owns the polynomial
comparison after replacing the transverse factors.
-/

namespace Models.Heisenberg.QuadraticMagnon

open SecondQuantization SecondQuantization.Bosonic
open scoped BigOperators

noncomputable section
variable {Mode : Type*}

/-- Quadratic excitation on one bond: the two number terms minus the two hoppings.
The coefficient J(2s) follows the bond-once exchange convention. -/
def excitationBond (J : ℝ) (twiceSpin : ℕ) (i j : Mode) : Module.End ℂ (FockSpace Mode) :=
  ((J : ℂ) * twiceSpin) • (numberOperator i + numberOperator j -
    (create i).comp (annihilate j) - (create j).comp (annihilate i))

theorem excitationBond_vacuum (J : ℝ) (twiceSpin : ℕ) (i j : Mode) :
    excitationBond J twiceSpin i j fockVacuum = 0 := by
  simp [excitationBond, numberOperator, fockVacuum, vacuum,
    annihilate_basisState_of_zero]

variable {N : ℕ} [NeZero N]

/-- Polarized energy -2JN s^2 for the zero-field ring, with N bonds. -/
def polarizedEnergy (N : ℕ) (J : ℝ) (twiceSpin : ℕ) : ℝ :=
  -J * N * twiceSpin ^ 2 / 2

/-- The zero-field quadratic excitation Hamiltonian on unrestricted bosonic Fock space.
This is a model definition, not an equality with the exact capped HP Hamiltonian. -/
def excitationHamiltonian (J : ℝ) (twiceSpin : ℕ) :
    Module.End ℂ (FockSpace (ZMod N)) :=
  ∑ i : ZMod N, excitationBond J twiceSpin i (i + 1)

/-- The quadratic Hamiltonian including the polarized reference energy. -/
def hamiltonian (J : ℝ) (twiceSpin : ℕ) : Module.End ℂ (FockSpace (ZMod N)) :=
  (polarizedEnergy N J twiceSpin : ℂ) • LinearMap.id +
    excitationHamiltonian J twiceSpin

theorem excitationHamiltonian_vacuum (J : ℝ) (twiceSpin : ℕ) :
    excitationHamiltonian (N := N) J twiceSpin fockVacuum = 0 := by
  simp [excitationHamiltonian, LinearMap.sum_apply, excitationBond_vacuum]

theorem hamiltonian_vacuum (J : ℝ) (twiceSpin : ℕ) :
    hamiltonian (N := N) J twiceSpin fockVacuum =
      (polarizedEnergy N J twiceSpin : ℂ) • fockVacuum := by
  simp [hamiltonian, excitationHamiltonian_vacuum]

end
end Models.Heisenberg.QuadraticMagnon
