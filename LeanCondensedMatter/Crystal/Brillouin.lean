/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Lattice
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Brillouin quotient and Bloch phase

The Brillouin torus is the additive quotient of momentum space by a reciprocal lattice. The
quotient itself is Mathlib's `QuotientAddGroup`; this file adds only the physical name and the
Bloch-phase bridge implied by the `2π` reciprocal-lattice convention from `Crystal.Lattice`.
-/

namespace LeanCondensedMatter.Crystal

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- The Brillouin torus associated with a reciprocal lattice. This is a thin alias for Mathlib's
additive quotient, so all quotient-group structure is inherited directly from `QuotientAddGroup`. -/
abbrev BrillouinTorus (Lstar : Submodule ℤ K) :=
  K ⧸ Lstar.toAddSubgroup

/-- The Bloch phase `exp (i k · R)` for wave vector `k` and real-space translation `R`. -/
noncomputable def blochPhase (k R : K) : ℂ :=
  Complex.exp ((inner ℝ k R : ℂ) * Complex.I)

/-- A reciprocal-lattice vector has trivial Bloch phase on every real-space lattice vector. -/
theorem blochPhase_eq_one_of_mem_reciprocalLattice
    {L : Submodule ℤ K} {G R : K}
    (hG : G ∈ reciprocalLattice L) (hR : R ∈ L) :
    blochPhase G R = 1 := by
  obtain ⟨n, hn⟩ := (mem_reciprocalLattice.mp hG) R hR
  rw [blochPhase, hn]
  convert Complex.exp_int_mul_two_pi_mul_I n using 1
  push_cast
  ring_nf

/-- Shifting a wave vector by a reciprocal-lattice vector leaves every lattice Bloch phase
unchanged. -/
theorem blochPhase_add_eq_of_mem_reciprocalLattice
    {L : Submodule ℤ K} (k : K) {G R : K}
    (hG : G ∈ reciprocalLattice L) (hR : R ∈ L) :
    blochPhase (k + G) R = blochPhase k R := by
  calc
    blochPhase (k + G) R = blochPhase k R * blochPhase G R := by
      simp [blochPhase, inner_add_left, add_mul, Complex.exp_add]
    _ = blochPhase k R := by
      rw [blochPhase_eq_one_of_mem_reciprocalLattice hG hR, mul_one]

end LeanCondensedMatter.Crystal
