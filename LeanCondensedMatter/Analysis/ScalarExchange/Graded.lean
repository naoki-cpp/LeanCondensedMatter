import LeanCondensedMatter.Analysis.ScalarExchange.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

set_option linter.style.header false

/-!
# Parity-graded scalar exchange

The exchange sign for homogeneous elements of a Z₂-graded algebra depends on
both degrees, rather than on a single particle-statistics choice. The underlying
bracket is the canonical `ScalarExchange.zetaCommutator`; Mathlib's
`GradedAlgebra` provides the actual decomposition into homogeneous submodules.

These algebraic statements do not assign a degree to an arbitrary (possibly
inhomogeneous) element and do not assert anything about operator domains.
-/

namespace ScalarExchange

/-- Koszul exchange sign: it is negative precisely for two odd degrees. -/
def paritySign (i j : ZMod 2) : ℂ :=
  if i = 1 ∧ j = 1 then -1 else 1

@[simp]
theorem paritySign_zero_left (j : ZMod 2) : paritySign 0 j = 1 := by
  simp [paritySign]

@[simp]
theorem paritySign_zero_right (i : ZMod 2) : paritySign i 0 = 1 := by
  simp [paritySign]

@[simp]
theorem paritySign_one_one : paritySign 1 1 = -1 := by
  simp [paritySign]

theorem paritySign_comm (i j : ZMod 2) :
    paritySign i j = paritySign j i := by
  simp only [paritySign, and_comm]

theorem paritySign_mul_self (i j : ZMod 2) :
    paritySign i j * paritySign i j = 1 := by
  by_cases h : i = 1 ∧ j = 1
  · simp [paritySign, h]
  · simp [paritySign, h]

/-- A homogeneous factor of degree `i` sees the product of degrees `j`
and `k` with the product of the two individual exchange signs. -/
theorem paritySign_add_right (i j k : ZMod 2) :
    paritySign i (j + k) = paritySign i j * paritySign i k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [paritySign]

theorem paritySign_add_left (i j k : ZMod 2) :
    paritySign (i + j) k = paritySign i k * paritySign j k := by
  rw [paritySign_comm, paritySign_add_right, paritySign_comm k i,
    paritySign_comm k j]

/-- Graded commutator of homogeneous elements with explicit parity indices.
For an internally graded algebra, use elements in the corresponding Mathlib
`GradedAlgebra` homogeneous submodules. -/
noncomputable def gradedCommutator {A : Type*} [Ring A] [Algebra ℂ A]
    (i j : ZMod 2) (a b : A) : A :=
  zetaCommutator (paritySign i j) a b

@[simp]
theorem gradedCommutator_even_left {A : Type*} [Ring A] [Algebra ℂ A]
    (j : ZMod 2) (a b : A) :
    gradedCommutator 0 j a b = zetaCommutator 1 a b := by
  simp [gradedCommutator]

@[simp]
theorem gradedCommutator_even_right {A : Type*} [Ring A] [Algebra ℂ A]
    (i : ZMod 2) (a b : A) :
    gradedCommutator i 0 a b = zetaCommutator 1 a b := by
  simp [gradedCommutator]

@[simp]
theorem gradedCommutator_odd_odd {A : Type*} [Ring A] [Algebra ℂ A]
    (a b : A) :
    gradedCommutator 1 1 a b = zetaCommutator (-1) a b := by
  simp [gradedCommutator]

/-- The graded bracket of two homogeneous elements lies in the sum degree.
This reuses Mathlib's grading, rather than introducing another graded-algebra
class or a global degree function on arbitrary elements. -/
theorem gradedCommutator_mem {A : Type*} [Ring A] [Algebra ℂ A]
    (𝒜 : ZMod 2 → Submodule ℂ A) [GradedAlgebra 𝒜]
    {i j : ZMod 2} (a : 𝒜 i) (b : 𝒜 j) :
    gradedCommutator i j (a : A) (b : A) ∈ 𝒜 (i + j) := by
  change (a : A) * b - paritySign i j • ((b : A) * a) ∈ 𝒜 (i + j)
  apply Submodule.sub_mem
  · exact SetLike.mul_mem_graded a.property b.property
  · apply Submodule.smul_mem
    simpa only [add_comm j i] using
      (SetLike.mul_mem_graded b.property a.property)

/-- Graded antisymmetry, including odd-odd symmetry, from the involutive
fixed-sign exchange law. -/
theorem gradedCommutator_swap {A : Type*} [Ring A] [Algebra ℂ A]
    (i j : ZMod 2) (a b : A) :
    gradedCommutator j i b a =
      (-paritySign i j) • gradedCommutator i j a b := by
  simpa only [gradedCommutator, paritySign_comm i j] using
    zetaCommutator_swap_of_sq_eq_one (paritySign i j)
      (paritySign_mul_self i j) a b

/-- Graded Leibniz identity in the right argument, with the parity of the
product expressed by addition in `ZMod 2`. -/
theorem gradedCommutator_mul_right {A : Type*} [Ring A] [Algebra ℂ A]
    (i j k : ZMod 2) (a b c : A) :
    gradedCommutator i (j + k) a (b * c) =
      gradedCommutator i j a b * c +
        paritySign i j • (b * gradedCommutator i k a c) := by
  change zetaCommutator (paritySign i (j + k)) a (b * c) =
    zetaCommutator (paritySign i j) a b * c +
      paritySign i j • (b * zetaCommutator (paritySign i k) a c)
  rw [paritySign_add_right]
  exact zetaCommutator_mul_right (paritySign i j) (paritySign i k) a b c

/-- Graded Leibniz identity in the left argument. -/
theorem gradedCommutator_mul_left {A : Type*} [Ring A] [Algebra ℂ A]
    (i j k : ZMod 2) (a b c : A) :
    gradedCommutator (i + j) k (a * b) c =
      a * gradedCommutator j k b c +
        paritySign j k • (gradedCommutator i k a c * b) := by
  change zetaCommutator (paritySign (i + j) k) (a * b) c =
    a * zetaCommutator (paritySign j k) b c +
      paritySign j k • (zetaCommutator (paritySign i k) a c * b)
  rw [paritySign_add_left]
  exact zetaCommutator_mul_left (paritySign i k) (paritySign j k) a b c

end ScalarExchange
