import LeanCondensedMatter.SecondQuantization.Fermionic.Field.FiniteParticleFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Creation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Annihilation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Mode

set_option linter.style.header false

/-!
# Fermionic fields

Basis-independent fermionic finite-particle Fock spaces, smeared fields, second quantization, and
continuity-derived currents. The completed F2 core contains exterior-multiplication creation,
inner-product contraction annihilation, the three smeared canonical anticommutation relations, and
their Kronecker-delta specialization along an orthonormal one-particle family. Later issue #524
slices add the representation comparison, `dΓ`, and current equivalence theorems.
-/
