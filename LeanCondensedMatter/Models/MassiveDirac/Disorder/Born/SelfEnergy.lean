import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.SelfEnergy.Core
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.SelfEnergy.PolarProvenance
import LeanCondensedMatter.Models.MassiveDirac.Disorder.Born.SelfEnergy.DenominatorIntegral

set_option linter.style.header false

/-!
# Continuum Born self-energy

Public import surface for the finite-cutoff Born self-energy: channelized radial Green integrals,
explicit polar-angle `2π` provenance, and the shared denominator integral factorization.
The split preserves the existing declarations and keeps downstream `Born.SelfEnergy` imports stable.
-/
