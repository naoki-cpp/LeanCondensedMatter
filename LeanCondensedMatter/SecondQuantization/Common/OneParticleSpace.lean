import Mathlib.Data.Fintype.Card

set_option linter.style.header false

/-!
# The one-particle mode space

The starting point of second quantization (Track D, `notes/roadmaps/second-quantization.md`):
an abstract type of one-particle "modes" (momentum modes, lattice sites, or any other
single-particle label). This deliberately carries no linear or Hilbert-space structure yet —
that structure appears once modes are combined into occupation-number states
(`BosonOccupation.lean`/`FermionOccupation.lean`) and then Fock space.

`Fintype Mode` is assumed for now to avoid analytical complications (summability, completions);
the countably-infinite-mode case is deferred to a later generalization, mirroring the same
finite-first approach already used for `Finpartition`/`IncidenceAlgebra` in Track B.
-/

namespace SecondQuantization

-- **One-particle mode space.** An abstract label set for single-particle states (momentum
-- modes, lattice sites, spin components, ...). No algebraic structure beyond `Fintype` and
-- decidable equality is assumed at this stage.
variable (Mode : Type*) [Fintype Mode] [DecidableEq Mode]

/-- The number of one-particle modes. -/
abbrev modeCount : ℕ := Fintype.card Mode

end SecondQuantization
