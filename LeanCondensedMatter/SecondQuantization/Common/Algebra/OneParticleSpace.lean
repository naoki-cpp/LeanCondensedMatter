set_option linter.style.header false

/-!
# One-particle mode labels

The occupation-basis algebra is parameterized by an arbitrary type `Mode`. A mode may represent a
momentum label, lattice site, internal spin/orbital label, or any other one-particle identifier.
The foundational label boundary deliberately imposes no finiteness, decidable-equality, linear, or
Hilbert-space structure.

Individual fermionic and bosonic occupation configurations remain finite-support objects even when
the mode type is infinite. Additional assumptions belong only on operations that need them:
decidable equality for concrete membership operations, finiteness for sums over every mode, and
analytic or Hilbert-space hypotheses for completed and thermal constructions.

There is therefore no project-wide mode count in the foundational API. Finite-mode cardinalities are
local data of explicitly finite specializations.
-/
