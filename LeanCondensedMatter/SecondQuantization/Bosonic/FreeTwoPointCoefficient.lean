import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTimeEvolution

set_option linter.style.header false

/-!
# The free bosonic two-point function's basis coefficient

Phase B3d of Track D's bosonic line (`notes/roadmaps/second-quantization.md`): the algebraic
coefficient `⟨n| a_i(τ) a_j† |n⟩` — a route to the free bosonic Green function/Bose–Einstein
distribution that works directly on the occupation-number basis and needs no thermal sum, no
operator trace, and no Hilbert-space completion.

**Naming.** `diagonalCoeff A n` is a coordinate evaluation, `A (basisState n) n`, not an inner
product — `FockSpaceBosonic Mode` has none. It is the algebraic, finite-particle *dense
subspace* of a would-be Hilbert-completed bosonic Fock space, not that completed space itself
(where an orthonormal `basisState` family would make `A (basisState n) n` and `⟨n|A|n⟩`
coincide). This is deliberately not named `operatorTrace`/`thermalTrace`: no trace (a sum of
diagonal coefficients weighted by a genuine density-matrix-normalized Gibbs weight) is built here,
only the single-basis-state coefficient itself.
-/

namespace SecondQuantization
namespace Bosonic

variable {Mode : Type*} [DecidableEq Mode]

/-- **The coefficient of basis state `n`** in `A (basisState n)`. See the module docstring for why
this is a coordinate evaluation, not an inner product. Delegates to `Common.diagonalCoeff`, so the
meaning is guaranteed to match the fermionic line's `Fermionic.matrixCoeff`. -/
noncomputable def diagonalCoeff (A : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode)
    (n : Occupation Mode) : ℂ :=
  Common.diagonalCoeff A n

theorem diagonalCoeff_eq (A : FockSpaceBosonic Mode →ₗ[ℂ] FockSpaceBosonic Mode)
    (n : Occupation Mode) : diagonalCoeff A n = A (basisState n) n :=
  rfl

@[simp]
theorem diagonalCoeff_smul_basisState (c : ℂ) (n : Occupation Mode) :
    (c • basisState n : FockSpaceBosonic Mode) n = c := by
  simp [basisState]

/-- **`⟨n| a_i(τ) a_i† |n⟩ = e^{-τεᵢ}(n_i + 1)`**: the free bosonic two-point function's diagonal
coefficient at equal mode `i`, combining the evolved-annihilation-operator formula
(`imaginaryTimeEvolve_annihilate`) with the diagonal CCR telescoping identity
(`annihilate_create_basisState_same`). This is the algebraic core of the free bosonic Green
function's equal-mode value, before any thermal (Boltzmann-weighted) sum over `n` is taken. -/
theorem diagonalCoeff_evolve_annihilate_comp_create_same (ε : Mode → ℝ) (τ : ℝ) (i : Mode)
    (n : Occupation Mode) :
    diagonalCoeff (((imaginaryTimeEvolve ε τ (annihilate i)).comp (create i)))
      n = Complex.exp (-(τ : ℂ) * (ε i : ℂ)) * ((n i : ℂ) + 1) := by
  rw [diagonalCoeff_eq, LinearMap.comp_apply, imaginaryTimeEvolve_annihilate,
    LinearMap.smul_apply, annihilate_create_basisState_same, smul_smul, basisState,
    Common.smul_basisState_apply_self]

/-- **`⟨n| a_i(τ) a_j† |n⟩ = 0` for `i ≠ j`**: the off-diagonal case, from the coordinate
independence of distinct modes — creating a particle at `j` then annihilating (or failing to
annihilate) at `i ≠ j` never lands back on `n` itself: mode `i`'s coordinate strictly decreases. -/
theorem diagonalCoeff_evolve_annihilate_comp_create_of_ne (ε : Mode → ℝ) (τ : ℝ) {i j : Mode}
    (hij : i ≠ j) (n : Occupation Mode) :
    diagonalCoeff ((imaginaryTimeEvolve ε τ (annihilate i)).comp (create j)) n = 0 := by
  rw [diagonalCoeff_eq, LinearMap.comp_apply, imaginaryTimeEvolve_annihilate,
    LinearMap.smul_apply, create_basisState_eq, map_smul]
  by_cases hi : (createOccupation j n) i = 0
  · simp [annihilate_basisState_of_zero hi]
  · have hni : n i ≠ 0 := by rwa [createOccupation_apply_ne hij] at hi
    have hswap :
        removeOccupation i (createOccupation j n) = createOccupation j (removeOccupation i n) :=
      removeOccupation_createOccupation_of_ne hij n
    rw [annihilate_basisState_of_pos hi, smul_smul, smul_smul, hswap]
    have hne : createOccupation j (removeOccupation i n) ≠ n := by
      intro heq
      have hcoord := congrArg (· i) heq
      rw [createOccupation_apply_ne hij, removeOccupation_apply_same] at hcoord
      omega
    simp [basisState, Common.basisState, hne]

end Bosonic
end SecondQuantization
