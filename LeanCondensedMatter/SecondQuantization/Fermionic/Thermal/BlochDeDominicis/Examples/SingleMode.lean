import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional

set_option linter.style.header false

/-!
# The single-mode 4-point Wick identity for normalized diagonal weights

A concrete finite-mode fermionic Bloch–de Dominicis pairing identity for a single mode `i` and an
arbitrary occupation-number-diagonal weight `w`:

`⟨cᵢcᵢ†cᵢcᵢ†⟩_w = ⟨cᵢcᵢ†⟩_w² + ζ⟨cᵢcᵢ⟩_w⟨cᵢ†cᵢ†⟩_w + ⟨cᵢcᵢ†⟩_w⟨cᵢ†cᵢ⟩_w`.

The weight `w` is arbitrary: no `β`, Hamiltonian, or Boltzmann weight is assumed, so the theorem is
an algebraic identity for a normalized occupation-number-diagonal functional. A genuine Gibbs
weight is supplied by the thermal specialization in `Fermionic/Thermal/FreeBoltzmannWeight.lean`.
The three terms match the four-position pairing weights `1`, `ζ`, `1` from
`Common/Thermal/BlochDeDominicis/PairingWeight.lean` for position labels
`1,2,3,4 ↦ cᵢ,cᵢ†,cᵢ,cᵢ†`. The general finite-Gibbs pairing sum is exposed by
`Common/Thermal/BlochDeDominicis/Induction.lean`'s
`finiteGibbsExpectation_prodComp_eq_sum_pairing`.

**Scope.** All four operators act at the same mode `i`, so no cross-mode independence of the
weight is needed. The identity follows from CAR (`annihilate_comp_create_self`,
`annihilate_comp_self`, `create_comp_self`, `annihilate_comp_create_comp_self`,
`annihilate_comp_create_add_create_comp_annihilate`) together with the diagonal-functional API
(`Common.normalizedWeightedDiagonal_add`/`_id`) and direct evaluation at the zero operator. The
middle `(13)(24)` term vanishes by the same-type selection rule represented here by
`annihilate_comp_self`.
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
