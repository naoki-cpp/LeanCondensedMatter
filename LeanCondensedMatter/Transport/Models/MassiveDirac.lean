import LeanCondensedMatter.Transport.Models.MassiveDirac.Model
import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.PropagatorSymmetry
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall.Intrinsic
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall

set_option linter.style.header false

/-!
# Massive-Dirac transport benchmark

Model-owned public entry point for the two-dimensional massive-Dirac transport benchmark. It exposes
the clean model, propagator and its momentum-inversion symmetry, intrinsic Hall benchmark, Středa
and Bastin representations, disorder specialization, and physically normalized longitudinal/Hall
conductivity results.
-/
