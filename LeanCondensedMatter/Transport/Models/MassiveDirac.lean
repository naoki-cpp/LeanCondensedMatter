import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Model
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Longitudinal

set_option linter.style.header false

/-!
# Massive-Dirac transport benchmark

Model-owned public entry point for the two-dimensional massive-Dirac transport benchmark. It exposes
the clean model, intrinsic Hall benchmark, Středa and Bastin representations, disorder specialization,
and longitudinal response as sibling/downstream layers of one concrete model.

The implementation leaf modules are being relocated from their historical `AnomalousHall` path under
#1840. This routing change establishes the model-owned public track without changing physical formulas,
normalizations, assumptions, or declaration namespaces.
-/
