import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PoleWindowBound
import LeanCondensedMatter.Transport.Analysis.LorentzianPole

set_option linter.style.header false

/-!
# Compatibility shell for retired massive-Dirac pole-error plumbing

The model-local epsilon/error decomposition previously owned by this module is now internal to the
generic `Transport.Analysis.LorentzianPole` theorem.  The file is retained temporarily so historical
module paths continue to resolve while compatibility shims are cleaned up separately.

No declarations are owned here.
-/
