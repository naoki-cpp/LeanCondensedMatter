import LeanCondensedMatter.SecondQuantization.Fermionic.Field.FiniteParticleFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Creation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Annihilation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Mode
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.OccupationEquivalence

set_option linter.style.header false

/-!
# Fermionic fields

Basis-independent fermionic finite-particle Fock spaces, smeared fields, second quantization, and
continuity-derived currents. The completed F2 layer contains exterior-multiplication creation,
inner-product contraction annihilation, the three smeared canonical anticommutation relations,
their Kronecker-delta specialization along an orthonormal one-particle family, and the basis-induced
linear equivalence with the existing occupation-subset Fock representation. Later issue #524 slices
add `dΓ` and current equivalence theorems.
-/
