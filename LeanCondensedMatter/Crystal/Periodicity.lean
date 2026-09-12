/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Translation
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Periodicity of atomic configurations

Periodicity is derived from the translation-symmetry subgroup rather than stored as unit-cell data.
The finite-motif condition is finiteness of the quotient of occupied sites by translation orbits.
Full periodicity additionally requires the translation subgroup, viewed canonically as a
`ℤ`-submodule, to be discrete and full-rank.
-/

namespace LeanCondensedMatter.Crystal

namespace AtomicConfiguration

variable {V E Species : Type*}

section FiniteModuloTranslations

variable [AddGroup V] [MetricSpace E] [AddAction V E] [IsIsometricVAdd V E]

/-- An atomic configuration has finitely many site classes modulo its translation symmetries.

This is the finite-motif condition only. By itself it does not imply periodicity: for example, a
finite configuration with trivial translation subgroup also satisfies this predicate. -/
def FiniteModuloTranslations (X : AtomicConfiguration E Species) : Prop :=
  Finite (AddAction.orbitRel.Quotient (X.translationSubgroup (V := V)) X.Site)

end FiniteModuloTranslations

section Periodic

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace E] [AddAction V E] [IsIsometricVAdd V E]

/-- A full-dimensional periodic atomic configuration.

The translation subgroup is interpreted through Mathlib's canonical equivalence between additive
subgroups and `ℤ`-submodules. Periodicity requires that this `ℤ`-submodule is discrete, spans the
full real vector space, and has only finitely many occupied-site orbits. -/
def Periodic (X : AtomicConfiguration E Species) : Prop :=
  let L := AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))
  DiscreteTopology L ∧
    Submodule.span ℝ (L : Set V) = ⊤ ∧
    X.FiniteModuloTranslations (V := V)

namespace Periodic

variable {X : AtomicConfiguration E Species}

/-- A periodic configuration has discrete translation vectors. -/
theorem discrete_translations (h : X.Periodic (V := V)) :
    DiscreteTopology (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) := by
  simpa only [Periodic] using h.1

/-- The translation vectors of a periodic configuration span the full ambient vector space. -/
theorem span_translations_eq_top (h : X.Periodic (V := V)) :
    Submodule.span ℝ
        ((AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) : Submodule ℤ V) : Set V) =
      ⊤ := by
  simpa only [Periodic] using h.2.1

/-- A periodic configuration has finitely many occupied-site classes modulo translations. -/
theorem finite_modulo_translations (h : X.Periodic (V := V)) :
    X.FiniteModuloTranslations (V := V) := by
  simpa only [Periodic] using h.2.2

/-- The translation subgroup of a periodic configuration is a Mathlib full `ℤ`-lattice. -/
theorem translationSubgroup_isZLattice (h : X.Periodic (V := V)) :
    @IsZLattice ℝ inferInstance V inferInstance inferInstance
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) h.discrete_translations := by
  letI : DiscreteTopology (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) :=
    h.discrete_translations
  exact ⟨h.span_translations_eq_top⟩

end Periodic

end Periodic

end AtomicConfiguration

end LeanCondensedMatter.Crystal
