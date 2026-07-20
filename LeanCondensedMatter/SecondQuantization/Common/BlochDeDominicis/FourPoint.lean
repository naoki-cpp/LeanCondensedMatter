import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.TwoPoint

set_option linter.style.header false

/-!
# The 4-point Bloch–de Dominicis expansion (concrete stepping stone toward the general induction)

Phase 9's finite-mode Bloch–de Dominicis induction (`notes/roadmaps/second-quantization.md`): the
`n = 2` (4-operator) case, obtained by the same "peel the first operator off, rotate it back around"
strategy as `Common/BlochDeDominicis/TwoPoint.lean`'s `n = 1` base case, iterated three times
instead of once. This is a concrete stepping stone toward the general `n`-point induction
(`Common/BlochDeDominicis/Induction.lean`, not yet started): it validates that the same
commutator-substitution/rotation pattern generalizes past the base case, before committing to the
general inductive statement and its connection to `Common.BlochDeDominicis.Pairing`.

**Deliberately left un-normalized/un-reduced**, matching `TwoPoint.lean`'s own choice: the RHS is a
sum of `traceFock`-of-*remaining*-operator-pairs terms (`Tr[e^{-βH₀}(C₃C₄)]` etc.), not further
reduced to pure numbers via `TwoPoint.lean`'s own theorem — doing that needs each remaining pair's
own KMS eigenvalue-shift and c-number commutator hypotheses (not assumed here, since `C₁` is the
only operator this file's hypotheses concern), and would need dividing by `traceFock D` (requiring
it nonzero) to land on genuine normalized 2-point numbers rather than un-normalized traces. Chaining
`TwoPoint.lean`'s own theorem onto each remaining-pair term, and connecting the resulting three
coefficients `1`, `ζ`, `ζ²` (which specialize to the `1`, `ζ`, `1` of
`Common.BlochDeDominicis.PairingWeight.four_position_pairings_and_weights` exactly, since `ζ² = 1`
for `ζ = ±1`) to a genuine sum over `Common.BlochDeDominicis.Pairing 2`, is future work — likely
subsumed by the general induction rather than done here specifically.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **The pure operator-algebra identity behind the 4-point expansion**: repeatedly rewriting
`C₁Cⱼ` as `c₁ⱼ • id + ζ•(CⱼC₁)` (for `j = 2, 3, 4`) and pushing the resulting `C₁` rightward through
`C₂`, then `C₃`, picks up one factor of `ζ` per operator it passes, landing `C₁` at the very end.
Pure `LinearMap` composition algebra — no `traceFock`/`Config`-finiteness involved. -/
theorem comp_comp_comp_eq_of_zetaCommutator
    (ζ c12 c13 c14 : ℂ) (C1 C2 C3 C4 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hcomm12 : C1.comp C2 - ζ • (C2.comp C1) =
      c12 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm13 : C1.comp C3 - ζ • (C3.comp C1) =
      c13 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm14 : C1.comp C4 - ζ • (C4.comp C1) =
      c14 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    C1.comp (C2.comp (C3.comp C4)) =
      c12 • (C3.comp C4) + (ζ * c13) • (C2.comp C4) + (ζ ^ 2 * c14) • (C2.comp C3) +
        ζ ^ 3 • (C2.comp (C3.comp (C4.comp C1))) := by
  have hp12 : ∀ x, C1 (C2 x) = c12 • x + ζ • C2 (C1 x) := fun x => by
    have h := DFunLike.congr_fun hcomm12 x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at h
    rwa [sub_eq_iff_eq_add] at h
  have hp13 : ∀ x, C1 (C3 x) = c13 • x + ζ • C3 (C1 x) := fun x => by
    have h := DFunLike.congr_fun hcomm13 x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at h
    rwa [sub_eq_iff_eq_add] at h
  have hp14 : ∀ x, C1 (C4 x) = c14 • x + ζ • C4 (C1 x) := fun x => by
    have h := DFunLike.congr_fun hcomm14 x
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      LinearMap.id_apply] at h
    rwa [sub_eq_iff_eq_add] at h
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hp12 (C3 (C4 x)), hp13 (C4 x), hp14 x]
  simp only [map_add, map_smul, smul_add, smul_smul]
  module

/-- **The 4-point Bloch–de Dominicis expansion**: `(1 - ζ³w₁) Tr[e^{-βH₀}(C₁C₂C₃C₄)] = c₁₂
Tr[e^{-βH₀}(C₃C₄)] + ζc₁₃ Tr[e^{-βH₀}(C₂C₄)] + ζ²c₁₄ Tr[e^{-βH₀}(C₂C₃)]` — `TwoPoint.lean`'s `n = 1`
strategy (commutator-substitution + `traceFock_diagonalEvolution_comp_rotate`, solving the
resulting self-referential equation) iterated three times to peel `C₁` all the way through
`C₂C₃C₄` before rotating it back to the front. See the module docstring for why this is left
un-normalized/un-reduced to a genuine pairing-weighted sum of numbers. -/
theorem traceFock_diagonalEvolution_comp_four_point [Fintype Config]
    (energy : Config → ℝ) (β q1 : ℝ) (ζ c12 c13 c14 : ℂ)
    (C1 C2 C3 C4 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm12 : C1.comp C2 - ζ • (C2.comp C1) =
      c12 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm13 : C1.comp C3 - ζ • (C3.comp C1) =
      c13 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm14 : C1.comp C4 - ζ • (C4.comp C1) =
      c14 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    (1 - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        traceFock ((diagonalEvolution energy (-β)).comp
          (C1.comp (C2.comp (C3.comp C4)))) =
      c12 * traceFock ((diagonalEvolution energy (-β)).comp (C3.comp C4)) +
        ζ * c13 * traceFock ((diagonalEvolution energy (-β)).comp (C2.comp C4)) +
        ζ ^ 2 * c14 * traceFock ((diagonalEvolution energy (-β)).comp (C2.comp C3)) := by
  have hopeq := comp_comp_comp_eq_of_zetaCommutator ζ c12 c13 c14 C1 C2 C3 C4
    hcomm12 hcomm13 hcomm14
  have hrot := traceFock_diagonalEvolution_comp_rotate energy β q1 (C2.comp (C3.comp C4)) C1 hC1
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc] at hrot
  have hstep : traceFock ((diagonalEvolution energy (-β)).comp
      (C1.comp (C2.comp (C3.comp C4)))) =
      c12 * traceFock ((diagonalEvolution energy (-β)).comp (C3.comp C4)) +
        ζ * c13 * traceFock ((diagonalEvolution energy (-β)).comp (C2.comp C4)) +
        ζ ^ 2 * c14 * traceFock ((diagonalEvolution energy (-β)).comp (C2.comp C3)) +
        ζ ^ 3 * traceFock ((diagonalEvolution energy (-β)).comp
          (C2.comp (C3.comp (C4.comp C1)))) := by
    conv_lhs => rw [hopeq]
    simp only [LinearMap.comp_add, LinearMap.comp_smul, traceFock_add, traceFock_smul]
  rw [hrot, smul_eq_mul] at hstep
  linear_combination hstep

end Common
end SecondQuantization
