import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.FreeGibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.GibbsLadderIntertwining
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalLadder
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalPeel
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalPeelIndexed
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalKMS
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalFirstPair
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.ThermalRecursion
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.GibbsModeTruncation
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.GibbsModeTruncationExpectation

set_option linter.style.header false

/-!
# Completed fermionic thermal theory

Public routing module for the completed-Hilbert free-fermion thermal stack selected by
`Fermionic.Thermal`: free Gibbs operators, ladder intertwining, KMS/peel recursion, and finite-mode
Gibbs convergence.
-/
