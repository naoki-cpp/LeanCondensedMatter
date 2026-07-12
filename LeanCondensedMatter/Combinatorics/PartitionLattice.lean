import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

/-!
# The partition lattice and its Möbius function

Adapts Mathlib's `Finpartition s` (the lattice of partitions of a finite set `s`, ordered by
refinement) to Mathlib's general `IncidenceAlgebra` (Möbius function / Möbius inversion)
machinery.

**Scope note:** this is pure combinatorics (Track B of `notes/roadmap.md`), independent of the
physics content elsewhere in this project. See `notes/model-and-assumptions.md` for the survey
of what Mathlib/PhysLean already provide here.
-/

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The partition lattice `Finpartition s` is locally finite: it is already a `Fintype`
(Mathlib), and its `≤` (refinement) is decidable, so every interval is a finite set. This is
the adapter needed to apply Mathlib's `IncidenceAlgebra` (Möbius function, Möbius inversion) to
the partition lattice. -/
noncomputable instance : LocallyFiniteOrder (Finpartition s) := by
  classical
  exact Fintype.toLocallyFiniteOrder
