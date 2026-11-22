import Mathlib.Basic.Real.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Outer-product and transverse matrix numerators

For a vector `k` over any commutative ring with finite coordinate index, define the rank-one
unnormalized longitudinal numerator `k kᵀ` and its transverse complement
`(k ⬝ᵥ k) I - k kᵀ`. Their squared-norm-scaled idempotence and mutual
annihilation follow without division by `k ⬝ᵥ k`, so the identities
also hold at `k = 0`.

These are elementary finite-dimensional matrix identities; no orbital
Hamiltonian, band interpretation, or physical momentum measure is assumed.
-/

namespace CartesianProjectors

open scoped Matrix

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- Coordinate squared norm, defined as an ordinary finite dot product. -/
def normSq (k : ι → R) : R := (k ⬝ᵥ k)

/-- The unnormalized rank-one longitudinal matrix `k kᵀ`. -/
def outer (k : ι → R) : Matrix ι ι R := Matrix.vecMulVec k k

theorem outer_mul_self (k : ι → R) :
    outer k * outer k = normSq k • outer k := by
  change Matrix.vecMulVec k k * Matrix.vecMulVec k k =
    (k ⬝ᵥ k) • Matrix.vecMulVec k k
  rw [Matrix.vecMulVec_mul_vecMulVec]
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

variable [DecidableEq ι]

/-- The unnormalized matrix transverse to `k`. -/
def transverse (k : ι → R) : Matrix ι ι R :=
  normSq k • (1 : Matrix ι ι R) - outer k

theorem outer_add_transverse (k : ι → R) :
    outer k + transverse k = normSq k • (1 : Matrix ι ι R) := by
  unfold transverse
  abel

theorem outer_mul_transverse (k : ι → R) :
    outer k * transverse k = 0 := by
  calc
    outer k * transverse k =
        outer k * (normSq k • (1 : Matrix ι ι R) - outer k) := rfl
    _ = normSq k • outer k - outer k * outer k := by simp [mul_sub]
    _ = 0 := by rw [outer_mul_self]; exact sub_self _

theorem transverse_mul_outer (k : ι → R) :
    transverse k * outer k = 0 := by
  calc
    transverse k * outer k =
        (normSq k • (1 : Matrix ι ι R) - outer k) * outer k := rfl
    _ = normSq k • outer k - outer k * outer k := by simp [sub_mul]
    _ = 0 := by rw [outer_mul_self]; exact sub_self _

theorem transverse_mul_self (k : ι → R) :
    transverse k * transverse k = normSq k • transverse k := by
  calc
    transverse k * transverse k =
        transverse k * (normSq k • (1 : Matrix ι ι R) - outer k) := rfl
    _ = normSq k • transverse k - transverse k * outer k := by simp [mul_sub]
    _ = normSq k • transverse k := by rw [transverse_mul_outer]; simp

end CartesianProjectors
