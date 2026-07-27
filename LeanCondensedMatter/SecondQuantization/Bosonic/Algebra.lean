import LeanCondensedMatter.SecondQuantization.Bosonic.Foundations.FockSpace
import LeanCondensedMatter.SecondQuantization.Bosonic.OperatorAlgebra.NumberOperator

set_option linter.style.header false

/-!
# Bosonic algebra

Public umbrella for the algebraic bosonic layer:

- occupation-number states and the algebraic Fock space;
- creation and annihilation operators;
- canonical commutation and exchange-algebra instances;
- particle-number grading and number operators.

The underlying declarations remain split into small proof files under `Foundations/` and
`OperatorAlgebra/`; consumers normally import this module instead of those internal groups.
-/
