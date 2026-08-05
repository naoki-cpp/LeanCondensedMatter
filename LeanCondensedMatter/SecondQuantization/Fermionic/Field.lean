import LeanCondensedMatter.SecondQuantization.Fermionic.Field.FiniteParticleFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Creation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Annihilation
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Mode
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.OccupationEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.SecondQuantization
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.SecondQuantizationLinearity

set_option linter.style.header false

/-!
# Fermionic fields

Basis-independent fermionic finite-particle Fock spaces, smeared fields, second quantization, and
continuity-derived currents. The completed F2 layer contains creation and annihilation fields,
smeared and mode CAR, and the basis-induced equivalence with the occupation-subset representation.
The F3 layer defines the algebraic second-quantization map `dGamma` by its basis-independent Leibniz
rule and packages its linear dependence on the one-particle operator. Later issue #524 slices add
commutator functoriality, the number operator, and current equivalence theorems.
-/
