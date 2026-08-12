import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.FiniteToys
import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoLevelExplicit
import LeanCondensedMatter.SecondQuantization.Fermionic.Validation.TwoSiteDimer

set_option linter.style.header false

/-!
# Fermionic validation models

Finite toy models and explicit checks for the fermionic transport stack. This is a terminal consumer
of the public algebra, lattice, and transport construction layers, not part of their ownership;
upstream fermionic modules must not import this validation tree.
-/
