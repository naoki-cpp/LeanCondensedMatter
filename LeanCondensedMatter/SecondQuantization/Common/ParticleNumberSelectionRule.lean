import LeanCondensedMatter.SecondQuantization.Common.AlgebraicFock

set_option linter.style.header false

/-!
# The particle-number selection rule, generic over the occupation-state type

`Fermionic/ThermalContraction.lean` proved, by direct case analysis on `FermionOccupation Mode`
cardinality, that composing two annihilation operators (or two creation operators) always yields
an operator with vanishing diagonal matrix coefficients. That argument never actually used
fermionic exchange statistics: it is the general fact that an operator changing the particle
number by a nonzero amount cannot connect a basis state back to itself, so it has no diagonal
matrix coefficients at all — a `U(1)` particle-number selection rule. This file extracts that
argument to `Common.AlgebraicFock`, generic over the occupation-state type `Config`, so both the
fermionic and bosonic lines can instantiate it instead of repeating the case analysis.

`CarriesParticleNumberCharge grading A q` says `A` only ever connects basis states `m`/`n` whose
`grading`-difference is exactly `q` — e.g. `grading = fermionParticleNumber` (cast to `ℤ`) and
`q = 1` for `create i`, `q = -1` for `annihilate i`. `q` need not be `±1`: it composes additively
under `LinearMap.comp` (`CarriesParticleNumberCharge.comp`), so e.g. `annihilate i |>.comp
(annihilate j)` carries charge `-2`.
-/

namespace SecondQuantization
namespace Common

/-- **`A` carries particle-number charge `q`** with respect to `grading : Config → ℤ`: `A` only
ever connects basis states `m`, `n` (i.e. has a nonzero `(m, n)` matrix coefficient) when
`grading m = grading n + q`. -/
def CarriesParticleNumberCharge {Config : Type*} (grading : Config → ℤ)
    (A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) (q : ℤ) : Prop :=
  ∀ m n, matrixCoeff A m n ≠ 0 → grading m = grading n + q

/-- Carrying a nonzero particle-number charge composes additively under `LinearMap.comp`: if `A`
carries charge `qA` and `B` carries charge `qB`, their composite `A.comp B` carries charge
`qA + qB`. -/
theorem CarriesParticleNumberCharge.comp {Config : Type*} {grading : Config → ℤ}
    {A B : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {qA qB : ℤ}
    (hA : CarriesParticleNumberCharge grading A qA)
    (hB : CarriesParticleNumberCharge grading B qB) :
    CarriesParticleNumberCharge grading (A.comp B) (qA + qB) := by
  intro m n hmn
  by_contra hcharge
  apply hmn
  rw [matrixCoeff, LinearMap.comp_apply]
  have hx : B (basisState n) =
      ∑ k ∈ (B (basisState n)).support, matrixCoeff B k n • basisState k := by
    conv_lhs => rw [← Finsupp.sum_single (B (basisState n))]
    rw [Finsupp.sum]
    exact Finset.sum_congr rfl fun k _ => (Finsupp.smul_single_one k _).symm
  rw [hx, map_sum]
  simp only [map_smul]
  rw [Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k _
  simp only [Finsupp.smul_apply, smul_eq_mul]
  change matrixCoeff B k n * matrixCoeff A m k = 0
  by_cases hBk : matrixCoeff B k n = 0
  · rw [hBk, zero_mul]
  · by_cases hAk : matrixCoeff A m k = 0
    · rw [hAk, mul_zero]
    · exact absurd (by rw [hA m k hAk, hB k n hBk]; ring) hcharge

/-- **The particle-number selection rule.** An operator that carries a nonzero particle-number
charge has vanishing diagonal matrix coefficients everywhere: it can never map a basis state back
to a multiple of itself, since that would force its charge to be `0`. -/
theorem diagonalCoeff_eq_zero_of_carriesParticleNumberCharge {Config : Type*}
    {grading : Config → ℤ} {A : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config} {q : ℤ}
    (hA : CarriesParticleNumberCharge grading A q) (hq : q ≠ 0) (n : Config) :
    diagonalCoeff A n = 0 := by
  rw [diagonalCoeff_eq_matrixCoeff]
  by_contra h
  have := hA n n h
  omega

end Common
end SecondQuantization
