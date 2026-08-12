import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoLevelExplicit
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.HermitianBondCurrent

set_option linter.style.header false

/-!
# Two-site dimer transport validation

This module equips the finite two-site hopping toy with explicit bounded Hamiltonian and current
operators on the full finite-lattice fermionic Fock space. The Hamiltonian is assembled from the two
second-quantized matrix units with conjugate coefficients. The current is the bounded oriented bond
current of the same Hermitian hopping model at `ℏ = q = 1`.

The resulting operators provide a finite tight-binding validation of the canonical pointwise
Kubo–Bastin/Středa identity. Current-orientation reversal and simultaneous current-sign reversal are
also recorded. No disorder average, numerical approximation, or limiting procedure is used.
-/

namespace SecondQuantization
namespace Fermionic
namespace Validation

open Lattice Transport

open QuantumTheory LinearResponse Transport

noncomputable section

/-- Full finite-dimensional fermionic Fock space of the two-site dimer. -/
abbrev TwoSiteHilbertFock := FiniteLatticeHilbertFock TwoSite

/-- The dimer hopping amplitudes form a Hermitian one-particle matrix. -/
theorem twoSiteDimerHopping_hasHermitianAmplitudes (t : ℂ) :
    (twoSiteDimerHopping t).HasHermitianAmplitudes := by
  intro x y
  fin_cases x <;> fin_cases y <;>
    simp [LocallyFiniteHopping.amplitude_eq]

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
  simp [twoSiteDimerHamiltonian, LocallyFiniteHopping.amplitude_eq]

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

/-- Concrete pointwise Kubo–Bastin/Středa agreement for the finite two-site dimer. -/
theorem twoSiteDimer_bastin_eq_streda
    (t : ℂ) (energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        (twoSiteDimerSystem t).hamiltonian.1
        (twoSiteDimerCurrent t) (twoSiteDimerCurrent t)
        energy broadening =
      regularizedStredaSurfacePrimitiveTraceDerivative
          (twoSiteDimerSystem t).hamiltonian.1
          (twoSiteDimerCurrent t) (twoSiteDimerCurrent t)
          energy broadening +
        regularizedStredaResidualSeaTraceKernel
          (twoSiteDimerSystem t).hamiltonian.1
          (twoSiteDimerCurrent t) (twoSiteDimerCurrent t)
          energy broadening :=
  regularizedBastinTraceIntegrand_eq_surfaceDerivative_add_residualSea
    (twoSiteDimerSystem t).hamiltonian.1
    (twoSiteDimerCurrent t) (twoSiteDimerCurrent t)
    energy broadening

/-- Simultaneous reversal of both dimer-current insertions leaves the Bastin trace unchanged. -/
theorem twoSiteDimer_currentSign_symmetry
    (t : ℂ) (energy broadening : ℝ) :
    regularizedBastinTraceIntegrand
        (twoSiteDimerSystem t).hamiltonian.1
        (-twoSiteDimerCurrent t) (-twoSiteDimerCurrent t)
        energy broadening =
      regularizedBastinTraceIntegrand
        (twoSiteDimerSystem t).hamiltonian.1
        (twoSiteDimerCurrent t) (twoSiteDimerCurrent t)
        energy broadening :=
  regularizedBastinTraceIntegrand_neg_neg
    (twoSiteDimerSystem t).hamiltonian.1
    (twoSiteDimerCurrent t) (twoSiteDimerCurrent t)
    energy broadening

end
end Validation
end Fermionic
end SecondQuantization
