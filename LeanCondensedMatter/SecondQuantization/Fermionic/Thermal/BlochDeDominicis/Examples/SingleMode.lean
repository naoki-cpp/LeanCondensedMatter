import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# The single-mode 4-point Wick identity for normalized diagonal weights

Phase 9, step 4 (`notes/roadmaps/second-quantization.md`): a first concrete instance of the
finite-mode fermionic Bloch–de Dominicis pairing-sum structure, for a single mode `i` and an
*arbitrary* occupation-number-diagonal weight `w`:

`⟨cᵢcᵢ†cᵢcᵢ†⟩_w = ⟨cᵢcᵢ†⟩_w² + ζ⟨cᵢcᵢ⟩_w⟨cᵢ†cᵢ†⟩_w + ⟨cᵢcᵢ†⟩_w⟨cᵢ†cᵢ⟩_w`

**This is not yet a finite-temperature theorem.** `w` is arbitrary here — no `β`, Hamiltonian, or
Boltzmann weight appears — so this is a purely algebraic identity for any normalized
occupation-number-diagonal weighted functional, not yet a genuine thermal-expectation statement
(see `Fermionic/Thermal/FreeBoltzmannWeight.lean` for the specialization that supplies a genuine Gibbs
weight). It matches the previously established four-position pairing weights `1`, `ζ`, `1` from
`Common/Thermal/BlochDeDominicis/PairingWeight.lean`'s `four_position_pairings_and_weights` term by term
(`(12)(34)`, `(13)(24)`, `(14)(23)` for the position labels `1,2,3,4 ↦ cᵢ,cᵢ†,cᵢ,cᵢ†`) — the
coefficients are hand-written here to match those weights, not obtained by summing over
`Combinatorics.Pairing 2` itself. `Common/Thermal/BlochDeDominicis/Induction.lean`'s general
`finiteGibbsExpectation_prodComp_eq_sum_pairing` now gives that genuine `Pairing 2`-sum connection
for `finiteGibbsExpectation`, the canonical finite Gibbs density-state expectation. Restating
*this* file's arbitrary-`w` identity as a `Pairing 2` sum rather than three hand-written terms
remains separate future work, because the general theorem is specific to the Gibbs density state,
not the arbitrary normalized diagonal weight `w` used here.

**Scope.** Deliberately the smallest nontrivial instance: all four operators act at the same mode
`i`, so no cross-mode independence of the weight is needed — the identity follows from CAR alone
(`annihilate_comp_create_self`, `annihilate_comp_self`, `create_comp_self`,
`annihilate_comp_create_comp_self`, `annihilate_comp_create_add_create_comp_annihilate` —
`Fermionic/Algebra/CanonicalAnticommutationRelations.lean`/`Fermionic/Algebra/NumberOperator.lean`) plus the
diagonal-functional API (`Common.normalizedWeightedDiagonal_add`/`_id`) and direct evaluation at the
zero operator. The general theorem, for operators at possibly distinct modes and a genuine free Gibbs
weight, needs the multi-mode
factorization the free partition function already exhibits
(`Fermionic/Thermal/FreePartitionFunction.lean`'s `freePartitionFunction_eq_prod`) and remains future work;
the middle `(13)(24)` term's vanishing here is a special case of
`Fermionic/Thermal/WeightedContraction.lean`'s same-type selection rule (a `U(1)`-charge argument, not a
single-mode coincidence), so that part of the argument already generalizes.
-/

namespace SecondQuantization
namespace Fermionic


variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **The single-mode 4-point Wick identity for normalized diagonal weights**:
`⟨cᵢcᵢ†cᵢcᵢ†⟩_w = ⟨cᵢcᵢ†⟩_w² + ζ⟨cᵢcᵢ⟩_w⟨cᵢ†cᵢ†⟩_w + ⟨cᵢcᵢ†⟩_w⟨cᵢ†cᵢ⟩_w`, matching
`Common/Thermal/BlochDeDominicis/PairingWeight.lean`'s four-position pairing weights `1`, `ζ`, `1` term by
term.
The middle term vanishes (`⟨cᵢcᵢ⟩_w = 0` from `annihilate_comp_self`), leaving `⟨cᵢcᵢ†⟩_w(⟨cᵢcᵢ†⟩_w
+ ⟨cᵢ†cᵢ⟩_w) = ⟨cᵢcᵢ†⟩_w · ⟨id⟩_w = ⟨cᵢcᵢ†⟩_w`, which matches the left side by `cᵢcᵢ†`'s
idempotency (`annihilate_comp_create_comp_self`). -/
theorem normalizedWeightedDiagonal_annihilate_create_annihilate_create_single_mode
    (w : Occupation Mode → ℂ) (hw : Common.weightSum w ≠ 0) (i : Mode) :
    Common.normalizedWeightedDiagonal w
        (((annihilate i).comp (create i)).comp ((annihilate i).comp (create i))) =
      Common.normalizedWeightedDiagonal w ((annihilate i).comp (create i)) *
          Common.normalizedWeightedDiagonal w ((annihilate i).comp (create i)) +
        (Common.Statistics.zetaInt Common.Statistics.fermion : ℂ) *
          (Common.normalizedWeightedDiagonal w ((annihilate i).comp (annihilate i)) *
            Common.normalizedWeightedDiagonal w ((create i).comp (create i))) +
        Common.normalizedWeightedDiagonal w ((annihilate i).comp (create i)) *
          Common.normalizedWeightedDiagonal w ((create i).comp (annihilate i)) := by
  have hzero :
      Common.normalizedWeightedDiagonal w
        (0 : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) = 0 := by
    have h := Common.normalizedWeightedDiagonal_smul (0 : ℂ) w
      (0 : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
    simpa using h
  rw [annihilate_comp_create_comp_self, annihilate_comp_self, create_comp_self,
    hzero, mul_zero, mul_zero, add_zero, ← mul_add,
    ← Common.normalizedWeightedDiagonal_add, annihilate_comp_create_add_create_comp_annihilate,
    Common.normalizedWeightedDiagonal_id w hw, mul_one]

end Fermionic
end SecondQuantization
