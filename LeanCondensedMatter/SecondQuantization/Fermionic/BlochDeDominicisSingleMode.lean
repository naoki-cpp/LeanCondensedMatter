import LeanCondensedMatter.SecondQuantization.Fermionic.NumberOperator
import LeanCondensedMatter.SecondQuantization.Fermionic.WeightedDiagonalFunctional
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# The finite-temperature 4-point Bloch–de Dominicis identity, single-mode case

Phase 9, step 4 (`notes/roadmaps/second-quantization.md`): a first concrete instance of the
finite-mode, finite-temperature fermionic Bloch–de Dominicis theorem — the 4-point identity

`⟨A₁A₂A₃A₄⟩ = ⟨A₁A₂⟩⟨A₃A₄⟩ + ζ⟨A₁A₃⟩⟨A₂A₄⟩ + ⟨A₁A₄⟩⟨A₂A₃⟩`

for the single-mode pattern `A₁ = A₃ = cᵢ`, `A₂ = A₄ = cᵢ†` — validating the pairing-sign design
`Common/BlochDeDominicisPairing.lean`'s "four-position theorem" already established combinatorially
(the three pairings of `Fin 4`, `{(12)(34), (13)(24), (14)(23)}`, weighted `1`, `ζ`, `1` by crossing
count) against the actual fermionic operator algebra, for *any* occupation-number-diagonal weight
`w` (not yet specialized to a genuine Gibbs weight — see `Fermionic/FreeBoltzmannWeight.lean`).

**Scope.** This is deliberately the smallest nontrivial instance, not the general theorem: all four
operators act at the same mode `i`, so no cross-mode independence of the weight is needed — the
identity follows from CAR alone (`annihilate_comp_create_self`, `anticomm_annihilate_annihilate`,
`anticomm_create_create` at `i = j`) plus the diagonal-functional API
(`normalizedWeightedDiagonal_add`/`_id`). The general theorem, for operators at possibly distinct
modes and a genuine free Gibbs weight, needs the multi-mode factorization the free partition
function already exhibits (`Fermionic/FreePartitionFunction.lean`'s
`freePartitionFunction_eq_prod`) and remains future work; the middle (`13)(24)` term's vanishing
here is a special case of `Fermionic/WeightedContraction.lean`'s same-type selection rule (a
`U(1)`-charge argument, not a single-mode coincidence), so that part of the argument already
generalizes.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-! ## Operator-level identities feeding the 4-point computation -/

omit [Fintype Mode] in
/-- **`cᵢ cᵢ = 0`**: annihilating twice at the same mode is the zero operator, the same-mode
special case of CAR's `{cᵢ, cⱼ} = 0`. -/
theorem annihilate_comp_self (i : Mode) : (annihilate i).comp (annihilate i) = 0 := by
  have h := anticomm_annihilate_annihilate (Mode := Mode) i i
  rw [anticomm] at h
  have h2 : (2 : ℂ) • ((annihilate i).comp (annihilate i)) = 0 := by rw [two_smul]; exact h
  rcases smul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 (by norm_num)
  · exact h0

omit [Fintype Mode] in
/-- **`cᵢ† cᵢ† = 0`**: the creation-side mirror of `annihilate_comp_self`. -/
theorem create_comp_self (i : Mode) : (create i).comp (create i) = 0 := by
  have h := anticomm_create_create (Mode := Mode) i i
  rw [anticomm] at h
  have h2 : (2 : ℂ) • ((create i).comp (create i)) = 0 := by rw [two_smul]; exact h
  rcases smul_eq_zero.mp h2 with h0 | h0
  · exact absurd h0 (by norm_num)
  · exact h0

omit [Fintype Mode] in
/-- **`Nᵢ` is idempotent**: `Nᵢ ∘ Nᵢ = Nᵢ`, directly from the number-operator eigenvalue equation
(occupation-number basis states are simultaneous eigenvectors with eigenvalue `0` or `1`). -/
theorem numberOperator_comp_self (i : Mode) :
    (numberOperator i).comp (numberOperator i) = numberOperator i := by
  apply linearMap_ext_basisState
  intro n
  rw [LinearMap.comp_apply, numberOperator_basisState]
  split_ifs with h
  · rw [numberOperator_basisState, if_pos h]
  · rw [map_zero]

omit [Fintype Mode] in
/-- **`cᵢ cᵢ†` is idempotent**: `(cᵢ cᵢ†)(cᵢ cᵢ†) = cᵢ cᵢ†`, from `cᵢ cᵢ† = id - Nᵢ`
(`annihilate_comp_create_self`) and `Nᵢ`'s idempotency. -/
theorem annihilate_comp_create_comp_self (i : Mode) :
    ((annihilate i).comp (create i)).comp ((annihilate i).comp (create i)) =
      (annihilate i).comp (create i) := by
  simp only [annihilate_comp_create_self, LinearMap.sub_comp, LinearMap.comp_sub,
    LinearMap.id_comp, LinearMap.comp_id, numberOperator_comp_self]
  abel

omit [Fintype Mode] in
/-- **`cᵢ cᵢ† + cᵢ† cᵢ = id`**, CAR's anticommutation relation rearranged: `cᵢ cᵢ† = id - Nᵢ`
together with `Nᵢ = cᵢ† cᵢ` by definition. -/
theorem annihilate_comp_create_add_create_comp_annihilate (i : Mode) :
    (annihilate i).comp (create i) + (create i).comp (annihilate i) =
      (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) := by
  rw [annihilate_comp_create_self, show (create i).comp (annihilate i) = numberOperator i from rfl]
  abel

omit [LinearOrder Mode] in
/-- **`⟨0⟩_w = 0`**: the normalized weighted diagonal functional vanishes on the zero operator. -/
theorem normalizedWeightedDiagonal_zero (w : FermionOccupation Mode → ℂ) :
    normalizedWeightedDiagonal w
        (0 : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) = 0 := by
  have h := normalizedWeightedDiagonal_smul (0 : ℂ) w
    (0 : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
  simpa using h

/-! ## The 4-point identity -/

/-- **The finite-temperature 4-point Bloch–de Dominicis identity, single-mode case**:
`⟨cᵢcᵢ†cᵢcᵢ†⟩_w = ⟨cᵢcᵢ†⟩_w² + ζ⟨cᵢcᵢ⟩_w⟨cᵢ†cᵢ†⟩_w + ⟨cᵢcᵢ†⟩_w⟨cᵢ†cᵢ⟩_w`, matching
`Common/BlochDeDominicisPairing.lean`'s four-position pairing weights `1`, `ζ`, `1` term by term
(`(12)(34)`, `(13)(24)`, `(14)(23)` for the position labels `1,2,3,4 ↦ cᵢ,cᵢ†,cᵢ,cᵢ†`). The middle
term vanishes (`⟨cᵢcᵢ⟩_w = 0` from `annihilate_comp_self`), leaving `⟨cᵢcᵢ†⟩_w(⟨cᵢcᵢ†⟩_w +
⟨cᵢ†cᵢ⟩_w) = ⟨cᵢcᵢ†⟩_w · ⟨id⟩_w = ⟨cᵢcᵢ†⟩_w`, which matches the left side by `cᵢcᵢ†`'s
idempotency. -/
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
