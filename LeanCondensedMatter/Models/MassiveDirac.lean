import LeanCondensedMatter.Models.MassiveDirac.Model
import LeanCondensedMatter.Models.MassiveDirac.ManyBody.PointwiseHall
import LeanCondensedMatter.Models.MassiveDirac.Propagator
import LeanCondensedMatter.Models.MassiveDirac.Streda
import LeanCondensedMatter.Models.MassiveDirac.Bastin
import LeanCondensedMatter.Models.MassiveDirac.Disorder
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Longitudinal
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall
import LeanCondensedMatter.Models.MassiveDirac.Scaling.Longitudinal
import LeanCondensedMatter.Models.MassiveDirac.Scaling.Pair

set_option linter.style.header false

/-!
# Massive-Dirac transport benchmark

Two-dimensional massive-Dirac spectral and Berry geometry, propagators, Kubo–Bastin
and Středa representations, Born and ladder disorder approximations, longitudinal and Hall
conductivity benchmarks, and scaling relations.
-/
