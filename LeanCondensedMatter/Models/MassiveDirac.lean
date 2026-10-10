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

set_option linter.style.header false

/-!
# Massive-Dirac transport benchmark

Public entry point for the two-dimensional massive-Dirac transport benchmark. It exposes the clean
model, propagator and its momentum-inversion symmetry, intrinsic Hall benchmark, Středa and Bastin
representations, disorder specialization, physically normalized longitudinal/Hall conductivity
results. The model-specific Born disorder stage attaches its scalar disorder line to the
shared physical-momentum continuum measure; generic trace/current normalization stays upstream.
-/
