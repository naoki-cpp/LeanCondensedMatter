import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.NormalizedOperatorFunctional

set_option linter.style.header false

/-!
# The normalized Gibbs expectation `⟨X⟩ := Tr[e^{-βH₀}X] / Tr[e^{-βH₀}]`

Every Bloch–de Dominicis theorem proved so far (`TwoPoint.lean`, `FourPointReduction.lean`,
`PeelFirst.lean`/`PeelFirstTrace.lean`) is stated in terms of the *un-normalized* `traceFock`/
`tsumTrace` of `e^{-βH₀}X`, deliberately left un-divided so callers choose whether/how to divide.
The genuine physical statement of the theorem — e.g. the 4-point expansion `⟨C₁C₂C₃C₄⟩_β =
⟨C₁C₂⟩_β⟨C₃C₄⟩_β + ζ⟨C₁C₃⟩_β⟨C₂C₄⟩_β + ⟨C₁C₄⟩_β⟨C₂C₃⟩_β` (the project's physics reference notes,
`quantum-statistical-mechanics.tex`) — is a product of *normalized* 2-point *numbers*, not
un-normalized traces. This file introduces that normalized functional (given the genuine partition
function `Tr[e^{-βH₀}] ≠ 0`) and derives the normalized 2-point value from `TwoPoint.lean`'s
un-normalized theorem, as the first step toward eventually stating the genuine (normalized)
`n`-point expansion.

**`[Fintype Config]` only, for now** — the `tsum` (bosonic) analogue needs `Common.tsumTrace D ≠ 0`
as its own hypothesis (not yet threaded through here) and is deferred to a follow-up.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*} [Fintype Config]

/-- **The normalized Gibbs expectation**, `⟨X⟩ := Tr[e^{-βH₀}X] / Tr[e^{-βH₀}]`. Well-defined
(and physically meaningful) only once `traceFock (diagonalEvolution energy (-β)) ≠ 0` — the
genuine partition function is nonzero — is supplied where needed; division by zero elsewhere is
Lean's usual junk value `0`, not asserted meaningful. -/
noncomputable def gibbsExpectation (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) : ℂ :=
  traceFock ((diagonalEvolution energy (-β)).comp A) / traceFock (diagonalEvolution energy (-β))

theorem gibbsExpectation_id (energy : Config → ℝ) (β : ℝ)
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0) :
    gibbsExpectation energy β (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) =
      1 := by
  rw [gibbsExpectation, LinearMap.comp_id, div_self hZ]

theorem gibbsExpectation_add (energy : Config → ℝ) (β : ℝ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β (A + B) =
      gibbsExpectation energy β A + gibbsExpectation energy β B := by
  simp only [gibbsExpectation, LinearMap.comp_add, traceFock_add, add_div]

theorem gibbsExpectation_smul (energy : Config → ℝ) (β : ℝ) (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β (c • A) = c * gibbsExpectation energy β A := by
  simp only [gibbsExpectation, LinearMap.comp_smul, traceFock_smul, mul_div_assoc]

/-- **The normalized Gibbs expectation, packaged as a `Common.NormalizedOperatorFunctional`.** -/
noncomputable def gibbsExpectationFunctional (energy : Config → ℝ) (β : ℝ)
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0) :
    NormalizedOperatorFunctional Config where
  toLinearMap :=
    { toFun := gibbsExpectation energy β
      map_add' := gibbsExpectation_add energy β
      map_smul' := gibbsExpectation_smul energy β }
  map_id := gibbsExpectation_id energy β hZ

/-- **The normalized 2-point Bloch–de Dominicis value**: `⟨C₁Cⱼ⟩ = c₁ⱼ/(1 - ζw₁)`, dividing
`TwoPoint.lean`'s un-normalized `(1 - ζw₁) Tr[e^{-βH₀}(C₁Cⱼ)] = c₁ⱼ Tr[e^{-βH₀}]` through by the
genuine (nonzero) partition function and by the (assumed nonzero) `1 - ζw₁` factor — the first
genuine, normalized-number Bloch–de Dominicis statement, matching the physics reference notes'
`⟨Ĉ₁Ĉⱼ⟩ = C_{1,j}/(1 - ζw₁)` letter-for-letter rather than leaving it as an un-divided trace
equation. -/
theorem gibbsExpectation_comp (energy : Config → ℝ) (β q1 : ℝ) (ζ c1j : ℂ)
    (C1 Cj : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : C1.comp Cj - ζ • (Cj.comp C1) =
      c1j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp Cj) =
      c1j / (1 - ζ * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have h := traceFock_diagonalEvolution_comp_two_point energy β q1 ζ c1j C1 Cj hC1 hcomm
  rw [gibbsExpectation, div_eq_div_iff hZ hne]
  linear_combination h

end Common
end SecondQuantization
