module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic

public section

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
theorem pow_eq_of_mod_two_eq {R : Type*} [Monoid R] {ζ : R} (hζ : ζ * ζ = 1) {a b : ℕ}
    (h : a % 2 = b % 2) : ζ ^ a = ζ ^ b := by
  have hζ2 : ζ ^ 2 = 1 := by
    simpa only [pow_two] using hζ
  calc
    ζ ^ a = ζ ^ (a % 2) := pow_eq_pow_mod a hζ2
    _ = ζ ^ (b % 2) := by rw [h]
    _ = ζ ^ b := (pow_eq_pow_mod b hζ2).symm

end Combinatorics
