import LeanCondensedMatter.Models.MassiveDirac.Model
import LeanCondensedMatter.Models.MassiveDirac.CurrentBridge
import LeanCondensedMatter.Models.MassiveDirac.Propagator
import LeanCondensedMatter.Models.MassiveDirac.Streda
import LeanCondensedMatter.Models.MassiveDirac.Bastin
import LeanCondensedMatter.Models.MassiveDirac.Disorder
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Longitudinal
import LeanCondensedMatter.Models.MassiveDirac.Conductivity.Hall
import LeanCondensedMatter.Models.MassiveDirac.Scaling.Longitudinal
import LeanCondensedMatter.Models.MassiveDirac.Scaling.Pair
import LeanCondensedMatter.Models.MassiveDirac.ContinuumMeasureProvenance

set_option linter.style.header false

/-!
# Massive-Dirac transport benchmark

Public entry point for the two-dimensional massive-Dirac transport benchmark. It exposes the clean
model, propagator and its momentum-inversion symmetry, intrinsic Hall benchmark, Středa and Bastin
representations, disorder specialization, physically normalized longitudinal/Hall conductivity
results, and the model-local provenance bridges relating continuum measure, angular reduction,
disorder-line, and conductivity prefactors.
-/
