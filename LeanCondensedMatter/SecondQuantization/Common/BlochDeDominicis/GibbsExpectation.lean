import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.TwoPoint
import LeanCondensedMatter.SecondQuantization.Common.NormalizedOperatorFunctional

set_option linter.style.header false
set_option linter.style.openClassical false

/-!
# The normalized Gibbs expectation, as a `boltzmannWeight`-specialized `normalizedWeightedDiagonal`

Every Bloch–de Dominicis theorem proved so far (`TwoPoint.lean`, `FourPointReduction.lean`,
`PeelFirst.lean`/`PeelFirstTrace.lean`) is stated in terms of the *un-normalized* `traceFock`/
`tsumTrace` of `e^{-βH₀}X`, deliberately left un-divided so callers choose whether/how to divide.
The genuine physical statement of the theorem — e.g. the 4-point expansion `⟨C₁C₂C₃C₄⟩_β =
⟨C₁C₂⟩_β⟨C₃C₄⟩_β + ζ⟨C₁C₃⟩_β⟨C₂C₄⟩_β + ⟨C₁C₄⟩_β⟨C₂C₃⟩_β` (for `ζ = ±1`, the project's physics
reference notes, `quantum-statistical-mechanics.tex`) — is a product of *normalized* 2-point
*numbers*, not un-normalized traces. This file introduces that normalized functional.

**Not a new abstraction — a `boltzmannWeight`-specialized instance of the existing
`Common.normalizedWeightedDiagonal`** (`WeightedDiagonalFunctional.lean`), the same object
`Fermionic.freeGibbsExpectation` already specializes for the fermionic free Boltzmann weight.
`boltzmannWeight energy β n := e^{-βE(n)}` is `diagonalEvolution energy (-β)`'s own diagonal
matrix entries (`matrixCoeff_diagonalEvolution`, proved below), so `diagonalEvolution`-headed
`traceFock`/`gibbsExpectation` and `boltzmannWeight`-headed `weightedTrace`/
`normalizedWeightedDiagonal` are the *same* quantities —
`gibbsExpectation_eq_normalizedWeightedDiagonal` proves it, and `gibbsExpectation` is *defined* as
that specialization directly, so its
linearity/`map_id`/`NormalizedOperatorFunctional` packaging are inherited from
`normalizedWeightedDiagonal`'s existing proofs rather than re-derived.

**`[Fintype Config]` only — deliberately not extended to a `tsum` (bosonic) analogue here.**
Unlike `traceFock`, `tsumTrace` is *not* unconditionally additive on all of `AlgebraicFock Config
→ₗ[ℂ] AlgebraicFock Config` (`tsumTrace_add` needs summability of both operands' diagonal series),
so there is no `tsum` operator space on which a `NormalizedOperatorFunctional` (a genuine
`LinearMap` on *all* operators) can be built the same way. A bosonic normalized expectation is
therefore a fact about *specific* operators with their own summability witnesses (as
`TwoPoint.lean`'s own `tsum` theorem already requires), not a `tsum` specialization of this file's
functional-level abstraction — a structurally different, separate future addition.
-/

namespace SecondQuantization
namespace Common

open scoped Classical

variable {Config : Type*} [Fintype Config]

/-- **The multi-mode free Boltzmann weight**, `e^{-βE(n)}`, generic over the occupation-state type
`Config` and an arbitrary real-valued `energy`. The un-cast-apart form of `diagonalEvolution
energy (-β)`'s own diagonal matrix entries (`matrixCoeff_diagonalEvolution` below) — mirrors
`Fermionic/FreeBoltzmannWeight.lean`'s/`Bosonic/BoltzmannWeightFactorization.lean`'s own
`freeBoltzmannWeight`/`boltzmannWeight`, generalized off the concrete occupation-state type. -/
noncomputable def boltzmannWeight (energy : Config → ℝ) (β : ℝ) (n : Config) : ℂ :=
  Complex.exp (((-β) * energy n : ℝ) : ℂ)

omit [Fintype Config] in
/-- **`diagonalEvolution` is diagonal**: its `(m, n)` matrix entry is `boltzmannWeight` at `m`
when `m = n`, and `0` off the diagonal. -/
theorem matrixCoeff_diagonalEvolution (energy : Config → ℝ) (β : ℝ) (m n : Config) :
    matrixCoeff (diagonalEvolution energy (-β)) m n =
      if m = n then boltzmannWeight energy β m else 0 := by
  rw [matrixCoeff, diagonalEvolution_basisState, boltzmannWeight]
  by_cases h : m = n
  · simp only [if_pos h]
    rw [h, smul_basisState_apply_self]
  · simp only [if_neg h]
    exact smul_basisState_apply_of_ne _ (Ne.symm h)

/-- **`Tr[e^{-βH₀}A] = Tr_{boltzmannWeight}(A)`**: `traceFock` of `diagonalEvolution energy
(-β)`-composed operators is the `boltzmannWeight`-weighted trace, since `diagonalEvolution` is
diagonal with those entries. -/
theorem traceFock_diagonalEvolution_comp_eq_weightedTrace (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    traceFock ((diagonalEvolution energy (-β)).comp A) = weightedTrace (boltzmannWeight energy β) A
    := by
  simp only [traceFock, weightedTrace, matrixCoeff_comp, matrixCoeff_diagonalEvolution, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem traceFock_diagonalEvolution_eq_weightSum (energy : Config → ℝ) (β : ℝ) :
    traceFock (diagonalEvolution energy (-β)) = weightSum (boltzmannWeight energy β) := by
  simp only [traceFock, weightSum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [matrixCoeff_diagonalEvolution]
  simp

/-- **The normalized Gibbs expectation**, `⟨X⟩ := Tr[e^{-βH₀}X] / Tr[e^{-βH₀}]`, defined directly
as the `boltzmannWeight`-specialization of `Common.normalizedWeightedDiagonal` — see the module
docstring for why this isn't a new abstraction. -/
noncomputable def gibbsExpectation (energy : Config → ℝ) (β : ℝ) :
    (AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) → ℂ :=
  normalizedWeightedDiagonal (boltzmannWeight energy β)

theorem gibbsExpectation_eq_normalizedWeightedDiagonal (energy : Config → ℝ) (β : ℝ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β A = normalizedWeightedDiagonal (boltzmannWeight energy β) A := rfl

theorem gibbsExpectation_id (energy : Config → ℝ) (β : ℝ)
    (hZ : weightSum (boltzmannWeight energy β) ≠ 0) :
    gibbsExpectation energy β
      (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 1 :=
  normalizedWeightedDiagonal_id (boltzmannWeight energy β) hZ

theorem gibbsExpectation_add (energy : Config → ℝ) (β : ℝ)
    (A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β (A + B) =
      gibbsExpectation energy β A + gibbsExpectation energy β B :=
  normalizedWeightedDiagonal_add (boltzmannWeight energy β) A B

theorem gibbsExpectation_smul (energy : Config → ℝ) (β : ℝ) (c : ℂ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) :
    gibbsExpectation energy β (c • A) = c * gibbsExpectation energy β A :=
  normalizedWeightedDiagonal_smul c (boltzmannWeight energy β) A

/-- **The normalized Gibbs expectation, packaged as a `Common.NormalizedOperatorFunctional`** —
directly `normalizedWeightedDiagonalFunctional` at `w := boltzmannWeight energy β`. -/
noncomputable def gibbsExpectationFunctional (energy : Config → ℝ) (β : ℝ)
    (hZ : weightSum (boltzmannWeight energy β) ≠ 0) :
    NormalizedOperatorFunctional Config :=
  normalizedWeightedDiagonalFunctional (boltzmannWeight energy β) hZ

/-- **The genuine normalized 2-point Bloch–de Dominicis value**: `⟨C₁Cⱼ⟩ = c₁ⱼ/(1 - ζw₁)`,
dividing `TwoPoint.lean`'s un-normalized `(1 - ζw₁) Tr[e^{-βH₀}(C₁Cⱼ)] = c₁ⱼ Tr[e^{-βH₀}]` through
by the genuine (nonzero) partition function and by the (assumed nonzero) `1 - ζw₁` factor — the
first genuine, normalized-number Bloch–de Dominicis statement, matching the physics reference
notes' `⟨Ĉ₁Ĉⱼ⟩ = C_{1,j}/(1 - ζw₁)` letter-for-letter rather than leaving it as an un-divided trace
equation. -/
theorem gibbsExpectation_comp_eq_div_of_zetaCommutator (energy : Config → ℝ) (β q1 : ℝ)
    (ζ c1j : ℂ) (C1 Cj : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : C1.comp Cj - ζ • (Cj.comp C1) =
      c1j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hZ : traceFock (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    gibbsExpectation energy β (C1.comp Cj) =
      c1j / (1 - ζ * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have h := traceFock_diagonalEvolution_comp_two_point energy β q1 ζ c1j C1 Cj hC1 hcomm
  rw [gibbsExpectation_eq_normalizedWeightedDiagonal, normalizedWeightedDiagonal,
    ← traceFock_diagonalEvolution_comp_eq_weightedTrace, ← traceFock_diagonalEvolution_eq_weightSum,
    div_eq_div_iff hZ hne]
  linear_combination h

end Common
end SecondQuantization
