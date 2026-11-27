import LeanCondensedMatter.Models.MassiveDirac.Propagator.Basic
import LeanCondensedMatter.Models.MassiveDirac.Propagator.Symmetry
import LeanCondensedMatter.Models.MassiveDirac.Propagator.AngularReduction
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.HankelScaling
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.ResolventDifference

set_option linter.style.header false

/-!
# Massive-Dirac propagator and radial Fourier analysis

The clean massive-Dirac Green operator, its momentum-inversion symmetry, and exact polar-angle
reduction. The `Basic` module owns complex radial Green-function denominators
without a Born or Fourier-integral dependency. The `RadialFourier` modules own fixed-complex-center quadratic Fourier resolvent
identities, ultraviolet estimates, Bessel-J representations, and conditional outgoing Hankel
reductions. These general results do not import disorder-specific Born or Dyson data.

The upper-half-plane Hankel transform identity remains an explicit hypothesis; its unconditional
proof is not asserted by the conditional reduction theorems.
-/
