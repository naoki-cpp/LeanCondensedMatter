import LeanCondensedMatter.SecondQuantization.Common.Algebra.AlgebraicFock

set_option linter.style.header false

/-!
# The particle-number selection rule, generic over the occupation-state type

`Fermionic/Thermal/WeightedContraction.lean` proved, by direct case analysis on `Fermionic.Occupation Mode`
cardinality, that composing two annihilation operators (or two creation operators) always yields
an operator with vanishing diagonal matrix coefficients. That argument never actually used
fermionic exchange statistics: it is the general fact that an operator changing the particle
number by a nonzero amount cannot connect a basis state back to itself, so it has no diagonal
matrix coefficients at all — a `U(1)` particle-number selection rule. This file extracts that
argument to `Common.AlgebraicFock`, generic over the occupation-state type `Config`, so both the
fermionic and bosonic lines can instantiate it instead of repeating the case analysis.

`CarriesGradingDegree grading A q` says `A` only ever connects basis states `m`/`n` whose
`grading`-difference is exactly `q`, for an *arbitrary* `ℤ`-valued `grading : Config → ℤ` — the
statement and its proofs below never use that `grading` specifically counts particles, so the same
API applies unchanged to any other `ℤ`-grading one might put on `Config` (spin projection, a
sublattice grading, ...). The name is generic for that reason; `Fermionic/Algebra/ParticleNumberCharge.lean`
and `Bosonic/ParticleNumberCharge.lean` are what actually specialize `grading` to
`Fermionic.particleNumber`/`particleNumber` (cast to `ℤ`) to get the physical particle-number
selection rule, e.g. `q = 1` for `create i`, `q = -1` for `annihilate i`. `q` need not be `±1`: it
composes additively under `LinearMap.comp` (`CarriesGradingDegree.comp`), so e.g.
`annihilate i |>.comp (annihilate j)` carries degree `-2`.
-/

namespace SecondQuantization
namespace Common

/-- **`A` carries grading degree `q`** with respect to `grading : Config → ℤ`: `A` only ever
connects basis states `m`, `n` (i.e. has a nonzero `(m, n)` matrix coefficient) when
`grading m = grading n + q`. -/
def CarriesGradingDegree {Config : Type*} (grading : Config → ℤ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (q : ℤ) : Prop :=
  ∀ m n, matrixCoeff A m n ≠ 0 → grading m = grading n + q

/-- Grading degrees compose additively under `LinearMap.comp`: if `A` carries degree `qA` and `B`
carries degree `qB`, their composite `A.comp B` carries degree `qA + qB`. -/
theorem CarriesGradingDegree.comp {Config : Type*} {grading : Config → ℤ}
    {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {qA qB : ℤ}
    (hA : CarriesGradingDegree grading A qA) (hB : CarriesGradingDegree grading B qB) :
    CarriesGradingDegree grading (A.comp B) (qA + qB) := by
  intro m n hmn
  by_contra hcharge
  apply hmn
  rw [matrixCoeff_comp_support]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hAk : matrixCoeff A m k = 0
  · simp [hAk]
  · by_cases hBk : matrixCoeff B k n = 0
    · simp [hBk]
    · exfalso
      apply hcharge
      rw [hA m k hAk, hB k n hBk]
      ring

/-- **The particle-number selection rule.** An operator that carries a nonzero grading degree has
vanishing diagonal matrix coefficients everywhere: it can never map a basis state back to a
multiple of itself, since that would force its degree to be `0`. -/
theorem diagonalCoeff_eq_zero_of_carriesGradingDegree {Config : Type*} {grading : Config → ℤ}
    {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : ℤ}
    (hA : CarriesGradingDegree grading A q) (hq : q ≠ 0) (n : Config) :
    diagonalCoeff A n = 0 := by
  unfold diagonalCoeff
  by_contra h
  have := hA n n h
  omega

end Common
end SecondQuantization
