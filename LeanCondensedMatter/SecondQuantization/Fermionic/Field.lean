import LeanCondensedMatter.SecondQuantization.Fermionic.Field.FiniteParticleFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Creation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Annihilation

set_option linter.style.header false

/-!
# Fermionic fields

Basis-independent fermionic finite-particle Fock spaces, smeared fields, second quantization, and
continuity-derived currents. The current F2 slice contains exterior-multiplication creation,
inner-product contraction annihilation, and the three smeared canonical anticommutation relations.
Later issue #524 slices add the basis comparison, `dΓ`, and current equivalence theorems.
-/
