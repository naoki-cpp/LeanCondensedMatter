import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.QuantumTheory.Gibbs.Eigenbasis

set_option linter.style.header false

/-!
# Finite full-occupation-Fock free-fermion Gibbs density operator

The finite free-fermion thermal state here is the generic pure-point Gibbs density operator
on the **entire** finite occupation Fock space, specialized to `fermionEnergy ε`. The weights
are equivalent to a zero-chemical-potential grand-canonical distribution with respect to the
mode-occupation count; this is **not** a sharp-`N` canonical state. Whether the underlying
physical system is canonical or grand canonical still depends on its conserved charge.

This file retains the legacy implicit-`μ = 0` finite-fermion adapter and its actual consumers
pending the explicit-`μ` API migration tracked by #3986. The module identifies density-state
expectations of transported algebraic observables with the generic finite Gibbs adapter.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The legacy full-occupation-space free-fermion Gibbs state at effective `μ = 0`.
This is not the fixed-number canonical density operator. -/
noncomputable def freeGibbsDensityOperator (ε : Mode → ℝ) (β : ℝ) :
    DensityOperator (Common.FiniteHilbertFock (Occupation Mode)) :=
  eigenbasisGibbsDensityOperator
    (Common.finiteHilbertBasis (Config := Occupation Mode)) (fermionEnergy ε) β
    (eigenbasisGibbsSummable_of_finite (fermionEnergy ε) β)

omit [LinearOrder Mode] in
/-- Evaluating the free Gibbs density state on a transported algebraic Fock operator is the
canonical finite Gibbs expectation at `fermionEnergy ε`. -/
theorem freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation
    (ε : Mode → ℝ) (β : ℝ) (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    (freeGibbsDensityOperator ε β).expectation (Common.finiteHilbertOperatorAlgEquiv A) =
      Common.finiteGibbsExpectation (fermionEnergy ε) β A := by
  rw [freeGibbsDensityOperator, Common.finiteGibbsExpectation,
    Common.finiteGibbsExpectationLinearMap, LinearMap.comp_apply]
  rfl


end Fermionic
end SecondQuantization
