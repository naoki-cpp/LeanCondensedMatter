import Mathlib.Data.Finset.Basic

set_option linter.style.header false

/-!
# Normalized finite-set functions

This module owns only the lightweight data structure of a finite-set function normalized to `1`
on the empty set. Moment/cumulant transforms and their inversion theorems live downstream in
`Combinatorics.Cumulant.Normalized`.

Keeping this core independent of Möbius inversion lets proof tracks that intentionally avoid
cumulant inversion still share the same normalized finite-set interface.
-/

namespace Combinatorics

/-- A finite-set function normalized to `1` on the empty set. -/
structure NormalizedSetFunction (α R : Type*) [One R] where
  /-- The underlying function on finite subsets. -/
  toFun : Finset α → R
  map_empty : toFun ∅ = 1

instance [One R] : CoeFun (NormalizedSetFunction α R) (fun _ => Finset α → R) :=
  ⟨NormalizedSetFunction.toFun⟩

@[ext]
theorem NormalizedSetFunction.ext [One R]
    {f g : NormalizedSetFunction α R} (h : ∀ S, f S = g S) : f = g := by
  cases f
  cases g
  simp only [mk.injEq]
  funext S
  exact h S

end Combinatorics
