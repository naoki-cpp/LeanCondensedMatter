import LeanCondensedMatter.Models.Heisenberg.QuadraticMagnon
import LeanCondensedMatter.Models.HolsteinPrimakoff

set_option linter.style.header false

/-!
# Exchange bonds after transverse Holstein-Primakoff factor replacement

Transverse-factor replacement means replacing the transverse HP square-root factors
by sqrt(2s), before dropping the longitudinal number-number term. The bond and ring
identities separate the quadratic operator from the longitudinal quartic remainder.
Source: Stancil-Prabhakar, Section 2.7.1, equations (2.154)-(2.156), converted to
one count per bond as in Section 2.5.

All operators act on unrestricted algebraic bosonic Fock space. These polynomial
identities neither estimate the transverse replacement error nor identify the
quadratic model with the exact capped-spin Hamiltonian.
-/

namespace Models.Heisenberg.QuadraticMagnon

open SecondQuantization SecondQuantization.Bosonic
open scoped BigOperators

noncomputable section
variable {Mode : Type*}

/-- Exchange bond after replacing transverse square-root factors by sqrt(2s),
before dropping the longitudinal quartic term. Spins are divided by hbar.
Its interpretation as a normal-ordered exchange bond requires distinct sites.
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

variable {N : ℕ} [NeZero N]

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
    LinearMap.sum_apply, Finset.sum_apply]
  ring

end
end Models.Heisenberg.QuadraticMagnon
