import LeanCondensedMatter.SecondQuantization.Fermionic.NumberOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.WeightedDiagonalFunctional

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
(see `Fermionic/FreeBoltzmannWeight.lean` for the specialization that supplies a genuine Gibbs
weight). It matches the previously established four-position pairing weights `1`, `ζ`, `1` from
`Common/BlochDeDominicis/PairingWeight.lean`'s `four_position_pairings_and_weights` term by term
(`(12)(34)`, `(13)(24)`, `(14)(23)` for the position labels `1,2,3,4 ↦ cᵢ,cᵢ†,cᵢ,cᵢ†`) — the
coefficients are hand-written here to match those weights, not obtained by summing over
`Common.BlochDeDominicis.Pairing 2` itself. `Common/BlochDeDominicis/Induction.lean`'s general
`gibbsExpectation_prodComp_eq_sum_pairing` now gives that genuine `Pairing 2`-sum connection for
`gibbsExpectation` (a specific, genuine Gibbs weight); restating *this* file's arbitrary-`w`
identity as a `Pairing 2` sum (rather than three hand-written terms) remains separate future
work, since `gibbsExpectation_prodComp_eq_sum_pairing` is specific to `gibbsExpectation`, not the
arbitrary normalized diagonal weight `w` used here.

**Scope.** Deliberately the smallest nontrivial instance: all four operators act at the same mode
`i`, so no cross-mode independence of the weight is needed — the identity follows from CAR alone
(`annihilate_comp_create_self`, `annihilate_comp_self`, `create_comp_self`,
`annihilate_comp_create_comp_self`, `annihilate_comp_create_add_create_comp_annihilate` —
`Fermionic/CanonicalAnticommutationRelations.lean`/`Fermionic/NumberOperator.lean`) plus the
diagonal-functional API (`normalizedWeightedDiagonal_add`/`_id`/`_zero`). The general theorem, for
operators at possibly distinct modes and a genuine free Gibbs weight, needs the multi-mode
factorization the free partition function already exhibits
(`Fermionic/FreePartitionFunction.lean`'s `freePartitionFunction_eq_prod`) and remains future work;
the middle `(13)(24)` term's vanishing here is a special case of
`Fermionic/WeightedContraction.lean`'s same-type selection rule (a `U(1)`-charge argument, not a
single-mode coincidence), so that part of the argument already generalizes.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The single-mode 4-point Wick identity for normalized diagonal weights**:
`⟨cᵢcᵢ†cᵢcᵢ†⟩_w = ⟨cᵢcᵢ†⟩_w² + ζ⟨cᵢcᵢ⟩_w⟨cᵢ†cᵢ†⟩_w + ⟨cᵢcᵢ†⟩_w⟨cᵢ†cᵢ⟩_w`, matching
`Common/BlochDeDominicis/PairingWeight.lean`'s four-position pairing weights `1`, `ζ`, `1` term by
term.
The middle term vanishes (`⟨cᵢcᵢ⟩_w = 0` from `annihilate_comp_self`), leaving `⟨cᵢcᵢ†⟩_w(⟨cᵢcᵢ†⟩_w
+ ⟨cᵢ†cᵢ⟩_w) = ⟨cᵢcᵢ†⟩_w · ⟨id⟩_w = ⟨cᵢcᵢ†⟩_w`, which matches the left side by `cᵢcᵢ†`'s
idempotency (`annihilate_comp_create_comp_self`). -/
theorem normalizedWeightedDiagonal_annihilate_create_annihilate_create_single_mode
    (w : FermionOccupation Mode → ℂ) (hw : weightSum w ≠ 0) (i : Mode) :
    normalizedWeightedDiagonal w
        (((annihilate i).comp (create i)).comp ((annihilate i).comp (create i))) =
      normalizedWeightedDiagonal w ((annihilate i).comp (create i)) *
          normalizedWeightedDiagonal w ((annihilate i).comp (create i)) +
        (Statistics.zetaInt Statistics.fermion : ℂ) *
          (normalizedWeightedDiagonal w ((annihilate i).comp (annihilate i)) *
            normalizedWeightedDiagonal w ((create i).comp (create i))) +
        normalizedWeightedDiagonal w ((annihilate i).comp (create i)) *
          normalizedWeightedDiagonal w ((create i).comp (annihilate i)) := by
  rw [annihilate_comp_create_comp_self, annihilate_comp_self, create_comp_self,
    normalizedWeightedDiagonal_zero, mul_zero, mul_zero, add_zero, ← mul_add,
    ← normalizedWeightedDiagonal_add, annihilate_comp_create_add_create_comp_annihilate,
    normalizedWeightedDiagonal_id w hw, mul_one]

end SecondQuantization
