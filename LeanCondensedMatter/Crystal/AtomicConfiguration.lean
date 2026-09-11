/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Topology.MetricSpace.MetricSeparated

/-!
# Atomic configurations

This file introduces a deliberately weak starting point for crystal geometry. An atomic
configuration consists only of occupied sites and a species label on each occupied site.
Periodicity, lattice data, unit cells, and crystallographic groups are properties or derived
structures rather than primitive fields.

Metric discreteness is likewise kept separate from the primitive configuration. Uniform
discreteness is expressed through Mathlib's quantitative `Metric.IsSeparated` predicate rather
than by introducing a second point-separation relation.
-/

namespace LeanCondensedMatter.Crystal

/-- A labeled set of occupied points in an ambient space `E`.

No discreteness or periodicity hypothesis is bundled into the data. -/
structure AtomicConfiguration (E : Type*) (Species : Type*) where
  /-- The occupied points of the configuration. -/
  occupied : Set E
  /-- The species label attached to each occupied point. -/
  species : occupied → Species

namespace AtomicConfiguration

variable {E Species : Type*}

/-- The subtype of sites occupied by a configuration. -/
abbrev Site (X : AtomicConfiguration E Species) := X.occupied

/-- An unordered pair of distinct occupied sites.

This is only the geometric two-site object. It does not assert that the two sites are physically
bonded; a model-specific bond network can be represented later as a subset of this type. -/
abbrev Bond (X : AtomicConfiguration E Species) :=
  {b : Sym2 X.Site // ¬ b.IsDiag}

/-- Construct the unordered bond determined by two distinct occupied sites. -/
def bond (X : AtomicConfiguration E Species) (x y : X.Site) (hxy : x ≠ y) : X.Bond :=
  ⟨Sym2.mk x y, by simpa using hxy⟩

section Metric

variable [MetricSpace E]

open scoped NNReal

/-- A configuration is uniformly discrete if its occupied set is `ε`-separated for some
strictly positive metric scale `ε`. -/
def UniformlyDiscrete (X : AtomicConfiguration E Species) : Prop :=
  ∃ ε : ℝ≥0, 0 < ε ∧ Metric.IsSeparated ε X.occupied

/-- A configuration is locally finite if every closed metric ball contains only finitely many
occupied sites. -/
def LocallyFinite (X : AtomicConfiguration E Species) : Prop :=
  ∀ x : E, ∀ r : ℝ, Set.Finite (X.occupied ∩ Metric.closedBall x r)

end Metric

end AtomicConfiguration

end LeanCondensedMatter.Crystal
