import LeanCondensedMatter.SecondQuantization.Fermionic.Field.FiniteParticleFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Creation

set_option linter.style.header false

/-!
# Fermionic fields

Basis-independent fermionic finite-particle Fock spaces, smeared fields, second quantization, and
continuity-derived currents. The current slices contain the finite-particle Fock foundation and the
basis-independent smeared creation operator; later issue #524 slices add annihilation by contraction,
the full smeared CAR, `dΓ`, and current equivalence theorems.
-/
