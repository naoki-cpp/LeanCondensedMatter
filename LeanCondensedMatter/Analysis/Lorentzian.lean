import LeanCondensedMatter.Analysis.Lorentzian.Kernel
import LeanCondensedMatter.Analysis.Lorentzian.RadialQuadratic
import LeanCondensedMatter.Analysis.Lorentzian.Weighted
import LeanCondensedMatter.Analysis.Lorentzian.Pole

set_option linter.style.header false

/-!
# Lorentzian analysis

Mathlib-style mathematical Lorentzian calculus: a scalar spectral kernel, weighted integral
identities, and complex regular-factor pole extraction in the `Lorentzian` namespace. The
radial-quadratic real integral and arctangent limits remain in the sibling `RadialQuadratic` module.
Physical Fermi-edge occupation and transport response remain downstream.
-/
