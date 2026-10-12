import LeanCondensedMatter.Models.HolsteinPrimakoff
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
The decomposition below is exact for the replaced transverse factors; it does not
identify the quadratic Hamiltonian with the exact HP Hamiltonian or bound its error.
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

/-- Exchange bond after replacing transverse square-root factors by sqrt(2s),
before dropping the longitudinal quartic term. Spins are divided by hbar.
Stancil-Prabhakar, equations (2.154)-(2.156), with each bond counted once. -/
def transverseReplacedBond (J : ℝ) (twiceSpin : ℕ) (i j : Mode) :
    Module.End ℂ (FockSpace Mode) :=
  (-2 * (J : ℂ)) •
    ((HolsteinPrimakoff.spinZ 1 twiceSpin i).comp (HolsteinPrimakoff.spinZ 1 twiceSpin j) +
      (twiceSpin / 2 : ℂ) •
        ((create i).comp (annihilate j) + (create j).comp (annihilate i)))

/-- Exact polynomial decomposition after the transverse replacement. For distinct
sites the last term is quartic in ladder operators; dropping it defines the quadratic model. -/
theorem transverseReplacedBond_eq (J : ℝ) (twiceSpin : ℕ) (i j : Mode) :
    transverseReplacedBond J twiceSpin i j =
      (-((J : ℂ) * twiceSpin ^ 2 / 2)) • LinearMap.id +
        excitationBond J twiceSpin i j -
        (2 * (J : ℂ)) • (numberOperator i).comp (numberOperator j) := by
  apply LinearMap.ext
  intro ψ
  apply Finsupp.ext
  intro n
  simp only [transverseReplacedBond, excitationBond, HolsteinPrimakoff.spinZ,
    Complex.ofReal_one, one_smul, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, map_smul,
    Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

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

/-- Summing replaced bonds gives the quadratic Hamiltonian plus the explicit
longitudinal quartic remainder. No transverse HP error is included in this identity. -/
theorem sum_transverseReplacedBond (J : ℝ) (twiceSpin : ℕ) :
    (∑ i : ZMod N, transverseReplacedBond J twiceSpin i (i + 1)) =
      hamiltonian J twiceSpin -
        (2 * (J : ℂ)) • ∑ i : ZMod N, (numberOperator i).comp (numberOperator (i + 1)) := by
  simp_rw [transverseReplacedBond_eq]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  apply LinearMap.ext
  intro ψ
  apply Finsupp.ext
  intro n
  simp [hamiltonian, excitationHamiltonian, polarizedEnergy, ZMod.card,
    LinearMap.sum_apply, Finset.sum_apply, smul_smul]
  ring

theorem excitationHamiltonian_vacuum (J : ℝ) (twiceSpin : ℕ) :
    excitationHamiltonian (N := N) J twiceSpin fockVacuum = 0 := by
  simp [excitationHamiltonian, LinearMap.sum_apply, excitationBond_vacuum]

theorem hamiltonian_vacuum (J : ℝ) (twiceSpin : ℕ) :
    hamiltonian (N := N) J twiceSpin fockVacuum =
      (polarizedEnergy N J twiceSpin : ℂ) • fockVacuum := by
  simp [hamiltonian, excitationHamiltonian_vacuum]

end
end Models.Heisenberg.QuadraticMagnon
