import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin.PoleWindowBound
import LeanCondensedMatter.Transport.Analysis.LorentzianPole

set_option linter.style.header false

/-!
# Compatibility shell for retired massive-Dirac pole-error plumbing

The Lorentzian-weighted error preparation formerly implemented here is now internal to the generic
`Transport.Analysis.LorentzianPole` theorem.  The nonnegative compact-window bound has moved to its
model-specific owner, `Bastin.PoleWindowBound`.

This file is retained temporarily so historical module paths continue to resolve.  No declarations
are owned here.
-/
