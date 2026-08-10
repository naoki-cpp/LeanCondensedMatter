import Mathlib.GroupTheory.Perm.Sign

set_option linter.style.header false

/-!
# The sign of a block permutation

Permuting `n` blocks of `k` elements each, keeping every block internally ordered, gives a
permutation of `n * k` elements whose sign is the `k`-th power of the sign of the block permutation.

In particular a permutation of **even-sized** blocks is always even, whatever the block permutation
is. This is the reason a fermionic weight factors over a decomposition into blocks that each carry
an even number of positions: the shuffle interleaving the blocks costs nothing.

Note that even *cardinality* of the moved sets is not enough — the blocks must genuinely be blocks.
Interleaving `{0, 2}` with `{1, 3}` moves two even sets past each other and is an odd permutation.

Mathlib has `Equiv.Perm.sign_prodCongrRight` for a permutation acting fibrewise on the second
factor; this is the complementary statement for a permutation acting on the first factor.
-/

namespace Combinatorics

open Equiv

variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β]

/-- Permuting the blocks of `α × β` indexed by `α`, keeping each block internally ordered. -/
def blockPerm (π : Equiv.Perm α) : Equiv.Perm (α × β) :=
  Equiv.prodCongr π (Equiv.refl β)

@[simp]
theorem blockPerm_apply (π : Equiv.Perm α) (x : α × β) :
    blockPerm (β := β) π x = (π x.1, x.2) :=
  rfl

/-- **The sign of a block permutation.** Permuting blocks of size `Fintype.card β` multiplies the
sign of the block permutation by itself once per element of a block. -/
theorem sign_blockPerm (π : Equiv.Perm α) :
    Equiv.Perm.sign (blockPerm (β := β) π) = Equiv.Perm.sign π ^ Fintype.card β := by
  have h : Equiv.Perm.sign (blockPerm (β := β) π) =
      Equiv.Perm.sign (Equiv.Perm.prodCongrRight (fun _ : β => π)) :=
    Equiv.Perm.sign_eq_sign_of_equiv _ _ (Equiv.prodComm α β) (fun x => by simp [blockPerm])
  rw [h, Equiv.Perm.sign_prodCongrRight, Finset.prod_const, Finset.card_univ]

/-- **Permuting even-sized blocks is even.** When each block carries an even number of positions,
the shuffle interleaving the blocks contributes no sign. -/
theorem sign_blockPerm_of_even (π : Equiv.Perm α) (h : Even (Fintype.card β)) :
    Equiv.Perm.sign (blockPerm (β := β) π) = 1 := by
  obtain ⟨r, hr⟩ := h
  rw [sign_blockPerm, hr, ← two_mul, pow_mul, sq, Int.units_mul_self, one_pow]

end Combinatorics
