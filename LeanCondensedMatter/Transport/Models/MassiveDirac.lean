import LeanCondensedMatter.Transport.Models.MassiveDirac.Model
import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.Models.MassiveDirac.Streda
import LeanCondensedMatter.Transport.Models.MassiveDirac.Bastin
import LeanCondensedMatter.Transport.Models.MassiveDirac.Disorder
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Longitudinal
import LeanCondensedMatter.Transport.Models.MassiveDirac.Conductivity.Hall
import LeanCondensedMatter.Transport.Models.MassiveDirac.ContinuumMeasureProvenance

set_option linter.style.header false

/-!
# Massive-Dirac transport benchmark

Public entry point for the two-dimensional massive-Dirac transport benchmark. It exposes the clean
model, propagator and its momentum-inversion symmetry, intrinsic Hall benchmark, Středa and Bastin
representations, disorder specialization, physically normalized longitudinal/Hall conductivity
results, and the model-local provenance bridges relating continuum measure, angular reduction,
disorder-line, and conductivity prefactors.
-/
