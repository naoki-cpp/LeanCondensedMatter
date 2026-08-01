import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.FockSpace
import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.NumberOperator

set_option linter.style.header false

/-!
# Bosonic algebra

Public umbrella for the algebraic bosonic layer:

- occupation-number states and the algebraic Fock space;
- creation and annihilation operators;
- canonical commutation and exchange-algebra instances;
- particle-number grading and number operators.

The underlying declarations live in small proof files under `Algebra/`; consumers normally
import this module instead of those internal files. The former split module groups are intentionally
not retained as compatibility paths.
-/
