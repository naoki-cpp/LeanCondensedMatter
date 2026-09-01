import LeanCondensedMatter.Transport.Models.MassiveDirac.Model
import LeanCondensedMatter.Transport.Models.MassiveDirac.Propagator
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Bastin
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Disorder
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Longitudinal

set_option linter.style.header false

/-!
# Massive-Dirac transport benchmark

Model-owned public entry point for the two-dimensional massive-Dirac transport benchmark. It exposes
the clean model and clean propagator, intrinsic Hall benchmark, Středa and Bastin representations,
disorder specialization, and longitudinal response as sibling/downstream layers of one concrete model.

The clean model kernel and propagator are canonically owned under `Transport/Models/MassiveDirac`.
Remaining response and disorder leaves are migrated independently under #1840.
-/
