/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Atomic configurations

This file introduces a deliberately weak geometric starting point for crystal structures.
A configuration consists only of occupied points and a label (for example, an atomic
species) attached to each occupied point. Periodicity, a lattice, a unit cell, and a
space group are *not* part of the primitive data.

The eventual goal is to recover the usual lattice-plus-finite-motif description from
properties of a configuration, rather than assuming that description at the outset.
-/

namespace LeanCondensedMatter
namespace Crystal

/-- A labeled set of occupied points in an ambient space `E`.

No discreteness or periodicity hypothesis is bundled into the data. Those are properties
of an `AtomicConfiguration`, so that the same primitive can also describe defects,
surfaces, and non-periodic configurations. -/
structure AtomicConfiguration (E : Type*) (Species : Type*) where
  /-- The occupied points of the configuration. -/
  occupied : Set E
  /-- The label/species attached to each occupied point. -/
  species : occupied → Species

namespace AtomicConfiguration

variable {E Species : Type*}

/-- The subtype of sites occupied by a configuration. -/
abbrev Site (X : AtomicConfiguration E Species) := X.occupied

section Metric

variable [MetricSpace E]

/-- A configuration is uniformly discrete if distinct occupied sites have a common
positive lower bound on their separation. -/
def UniformlyDiscrete (X : AtomicConfiguration E Species) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x y : X.Site, x ≠ y → ε ≤ dist (x : E) (y : E)

/-- Local finiteness expressed metrically: every closed ball contains only finitely many
occupied sites.

For proper metric spaces this is equivalent to the usual compact-set formulation and is
convenient to use without making compact subsets part of the primitive structure. -/
def LocallyFinite (X : AtomicConfiguration E Species) : Prop :=
  ∀ x : E, ∀ r : ℝ, Set.Finite (X.occupied ∩ Metric.closedBall x r)

end Metric

end AtomicConfiguration

end Crystal
end LeanCondensedMatter
