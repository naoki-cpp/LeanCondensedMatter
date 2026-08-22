import LeanCondensedMatter.Transport.FiniteVolume
import LeanCondensedMatter.Transport.ConductivityNormalization
import LeanCondensedMatter.Transport.FiniteConductivityTable
import LeanCondensedMatter.Transport.FiniteTrace

set_option linter.style.header false

/-!
# Transport foundations

Public umbrella for representation-independent finite transport data and normalization:
positive physical volume, conductivity normalization, finite scalar conductivity tables, and
ordinary finite-dimensional trace infrastructure.

This module is intentionally model-independent. Resolvent, Kubo–Bastin, Středa, disorder, and
concrete transport models remain downstream.
-/
