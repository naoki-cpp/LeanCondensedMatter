import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.Hamiltonian
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge

set_option linter.style.header false

/-!
# Finite fermionic fixed-particle-number canonical ensemble

The occupation basis of the fixed-`N` sector consists only of configurations whose
total particle number is exactly `N`. Its free canonical density operator is the existing
generic pure-point Gibbs state, constructed on this **sector Hilbert space** with the
restriction of the physical free energy.

Unlike the full occupation Fock Gibbs state, this state has sharp particle number.
The fixed sector can be empty (for example when `N` exceeds the number of modes), so
constructing a normalized Gibbs density operator requires `[Nonempty (CanonicalOccupation Mode N)]`.

An operator that changes particle number does not act within this sector. In particular,
the sector expectation of two operators is not obtained by separately restricting
each charge-changing factor; extending the state by zero to the full Fock space and
handling general operators is separate work. Fixed-`N` Gibbs states are not
automatically quasi-free and no Wick/KMS statement is asserted here.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Free Gibbs density operator on the **fixed-number sector Hilbert space**.
The nonempty-sector hypothesis is essential; finite dimensionality alone does not
produce a normalized state on an empty sector. -/
noncomputable def canonicalFreeGibbsDensityOperator
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ) [Nonempty (CanonicalOccupation Mode N)] :
    DensityOperator (Common.FiniteHilbertFock (CanonicalOccupation Mode N)) := by
  classical
  exact eigenbasisGibbsDensityOperator
    (Common.finiteHilbertBasis (Config := CanonicalOccupation Mode N))
    (fun n : CanonicalOccupation Mode N => fermionEnergy ε n.val) β
    (eigenbasisGibbsSummable_of_finite
      (fun n : CanonicalOccupation Mode N => fermionEnergy ε n.val) β)

omit [LinearOrder Mode] in
/-- The canonical sector density operator has Gibbs probabilities on its own
fixed-`N` occupation basis. -/
theorem canonicalFreeGibbsDensityOperator_apply_basis
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ) [Nonempty (CanonicalOccupation Mode N)]
    (n : CanonicalOccupation Mode N) :
    (canonicalFreeGibbsDensityOperator ε β N).op
        (Common.finiteHilbertBasisState n) =
      (eigenbasisGibbsProbability
          (fun m : CanonicalOccupation Mode N => fermionEnergy ε m.val) β n : ℂ) •
        Common.finiteHilbertBasisState n := by
  classical
  simpa [canonicalFreeGibbsDensityOperator] using
    (eigenbasisGibbsDensityOperator_apply_basis
      (Common.finiteHilbertBasis (Config := CanonicalOccupation Mode N))
      (fun m : CanonicalOccupation Mode N => fermionEnergy ε m.val) β
      (eigenbasisGibbsSummable_of_finite
        (fun m : CanonicalOccupation Mode N => fermionEnergy ε m.val) β) n)

omit [LinearOrder Mode] in
/-- A fixed-sector density-state expectation is the existing finite Gibbs
expectation evaluated with the energy function restricted to that sector. -/
theorem canonicalFreeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ) [Nonempty (CanonicalOccupation Mode N)]
    (A : Common.AlgebraicFock (CanonicalOccupation Mode N) →ₗ[ℂ]
      Common.AlgebraicFock (CanonicalOccupation Mode N)) :
    (canonicalFreeGibbsDensityOperator ε β N).expectation
        (Common.finiteHilbertOperatorAlgEquiv A) =
      Common.finiteGibbsExpectation
        (fun n : CanonicalOccupation Mode N => fermionEnergy ε n.val) β A := by
  classical
  rw [canonicalFreeGibbsDensityOperator, Common.finiteGibbsExpectation,
    Common.finiteGibbsExpectationLinearMap, LinearMap.comp_apply]
  rfl

/-- The canonical sector has sharp particle number: its Gibbs expectation of the
sector number operator is precisely `N`. -/
omit [LinearOrder Mode] in
theorem canonicalFreeGibbsDensityOperator_number_expectation
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ) [Nonempty (CanonicalOccupation Mode N)] :
    (canonicalFreeGibbsDensityOperator ε β N).expectation
        (Common.finiteHilbertOperatorAlgEquiv
          (canonicalSectorNumberOperator (Mode := Mode) N)) = (N : ℂ) := by
  rw [canonicalSectorNumberOperator_eq_smul_id, map_smul,
    ← Module.End.one_eq_id, map_one, map_smul]
  have hid :
      (canonicalFreeGibbsDensityOperator ε β N).expectation
        (1 : Common.FiniteHilbertFock (CanonicalOccupation Mode N) →L[ℂ]
          Common.FiniteHilbertFock (CanonicalOccupation Mode N)) = 1 :=
    (canonicalFreeGibbsDensityOperator ε β N).expectation_id
  rw [hid]
  ring

/-- The fixed-number Gibbs state has zero particle-number variance. -/
omit [LinearOrder Mode] in
theorem canonicalFreeGibbsDensityOperator_number_variance_zero
    (ε : Mode → ℝ) (β : ℝ) (N : ℕ) [Nonempty (CanonicalOccupation Mode N)] :
    (canonicalFreeGibbsDensityOperator ε β N).expectation
        (Common.finiteHilbertOperatorAlgEquiv
          ((canonicalSectorNumberOperator (Mode := Mode) N).comp
            (canonicalSectorNumberOperator (Mode := Mode) N))) -
      ((canonicalFreeGibbsDensityOperator ε β N).expectation
        (Common.finiteHilbertOperatorAlgEquiv
          (canonicalSectorNumberOperator (Mode := Mode) N))) ^ 2 = 0 := by
  rw [canonicalSectorNumberOperator_sq_eq_smul_id, map_smul,
    ← Module.End.one_eq_id, map_one, map_smul]
  have hid :
      (canonicalFreeGibbsDensityOperator ε β N).expectation
        (1 : Common.FiniteHilbertFock (CanonicalOccupation Mode N) →L[ℂ]
          Common.FiniteHilbertFock (CanonicalOccupation Mode N)) = 1 :=
    (canonicalFreeGibbsDensityOperator ε β N).expectation_id
  rw [hid, canonicalFreeGibbsDensityOperator_number_expectation]
  ring

end Fermionic
end SecondQuantization
