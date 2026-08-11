import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Conv

set_option linter.style.header false

/-!
# Involutive exchange scalars

Elementary algebra for an exchange scalar `ζ` satisfying `ζ * ζ = 1`.

This module is intentionally small. It owns only facts that are shared independently by the
perfect-pairing recursion and by the statistics-facing second-quantized code. More specialized
sign-transport machinery belongs with the exchange-sum implementation and should remain private
there unless it acquires a real cross-module consumer.
-/

namespace Combinatorics

/-- A power of an involutive scalar (`ζ * ζ = 1`) only depends on the exponent's parity. -/
theorem pow_eq_of_mod_two_eq {R : Type*} [CommSemiring R] {ζ : R} (hζ : ζ * ζ = 1) {a b : ℕ}
    (h : a % 2 = b % 2) : ζ ^ a = ζ ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 2]
  conv_rhs => rw [← Nat.div_add_mod b 2, ← h]
  rw [pow_add, pow_add, pow_mul, pow_mul, sq, hζ, one_pow, one_pow]

end Combinatorics
