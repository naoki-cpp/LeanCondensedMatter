import LeanCondensedMatter.Transport.Models.MassiveDirac.Model
import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.PropagatorSymmetry
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal

set_option linter.style.header false

/-!
# Massive-Dirac transport benchmark

Model-owned public entry point for the two-dimensional massive-Dirac transport benchmark. It exposes
the clean model, propagator and its momentum-inversion symmetry, intrinsic Hall benchmark, Středa
and Bastin representations, disorder specialization, and longitudinal response.
-/
