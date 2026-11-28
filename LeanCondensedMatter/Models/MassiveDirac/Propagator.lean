import LeanCondensedMatter.Models.MassiveDirac.Propagator.Basic
import LeanCondensedMatter.Models.MassiveDirac.Propagator.Symmetry
import LeanCondensedMatter.Models.MassiveDirac.Propagator.AngularReduction
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.HankelScaling
import LeanCondensedMatter.Models.MassiveDirac.Propagator.RadialFourier.ResolventDifference

set_option linter.style.header false

/-!
# Massive-Dirac propagator and radial Fourier analysis

Clean Green operators, momentum-inversion symmetry, angular reduction, and fixed-center
radial Fourier resolvents with ultraviolet estimates and Bessel representations.
The outgoing Hankel reduction assumes the upper-half-plane transform identity.
-/
