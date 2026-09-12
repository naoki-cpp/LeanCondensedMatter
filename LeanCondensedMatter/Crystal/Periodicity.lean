/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Translation
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Data.Set.Finite.Range

/-!
# Periodicity of atomic configurations

Periodicity is derived from the translation-symmetry subgroup rather than stored as unit-cell data.
The finite-motif condition is finiteness of the quotient of occupied sites by translation orbits.
Full periodicity additionally requires the translation subgroup, viewed canonically as a
`ℤ`-submodule, to be a Mathlib full `ℤ`-lattice.
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

namespace FiniteModuloTranslations

variable {X : AtomicConfiguration E Species}

/-- A configuration with finitely many translation-orbit classes admits a finite motif whose
translation orbits cover every occupied site. The motif is derived noncomputably from orbit
representatives and is not stored as part of the atomic configuration. -/
theorem exists_finite_translation_motif (h : X.FiniteModuloTranslations (V := V)) :
    ∃ M : Set X.Site,
      M.Finite ∧
        ∀ x : X.Site,
          ∃ m ∈ M, ∃ v : X.translationSubgroup (V := V), v +ᵥ m = x := by
  let Q := AddAction.orbitRel.Quotient (X.translationSubgroup (V := V)) X.Site
  letI : Finite Q := h
  refine ⟨Set.range (fun q : Q => q.out), Set.finite_range _, ?_⟩
  intro x
  let q : Q := Quotient.mk'' x
  refine ⟨q.out, ⟨q, rfl⟩, ?_⟩
  have hq : (Quotient.mk'' x : Q) = Quotient.mk'' q.out := (Quotient.out_eq' q).symm
  obtain ⟨v, hv⟩ := Quotient.exact hq
  exact ⟨v, hv⟩

/-- If ambient translations act freely, finiteness modulo translation symmetries gives a finite
motif with a unique translation-motif decomposition of every occupied site. -/
theorem exists_finite_translation_normal_form [IsCancelVAdd V E]
    (h : X.FiniteModuloTranslations (V := V)) :
    ∃ M : Set X.Site,
      M.Finite ∧
        ∀ x : X.Site,
          ∃! p : X.translationSubgroup (V := V) × X.Site,
            p.2 ∈ M ∧ p.1 +ᵥ p.2 = x := by
  let Q := AddAction.orbitRel.Quotient (X.translationSubgroup (V := V)) X.Site
  letI : Finite Q := h
  refine ⟨Set.range (fun q : Q => q.out), Set.finite_range _, ?_⟩
  intro x
  let q : Q := Quotient.mk'' x
  have hq : (Quotient.mk'' x : Q) = Quotient.mk'' q.out := (Quotient.out_eq' q).symm
  obtain ⟨v, hv⟩ := Quotient.exact hq
  refine ⟨⟨v, q.out⟩, ⟨⟨q, rfl⟩, hv⟩, ?_⟩
  rintro ⟨w, m⟩ ⟨hm, hwm⟩
  rcases hm with ⟨r, rfl⟩
  have hrq : r = q := by
    calc
      r = Quotient.mk'' r.out := (Quotient.out_eq' r).symm
      _ = Quotient.mk'' x := (Quotient.sound (show
        AddAction.orbitRel (X.translationSubgroup (V := V)) X.Site x r.out from
          ⟨w, hwm⟩)).symm
      _ = q := rfl
  subst r
  apply Prod.ext
  · exact IsCancelVAdd.right_cancel w v q.out (hwm.trans hv.symm)
  · rfl

end FiniteModuloTranslations

end FiniteModuloTranslations

section Periodic

variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace E] [NormedAddTorsor V E]

/-- A full-dimensional periodic atomic configuration.

The ambient positions form a normed affine torsor for the translation-vector space, so translations
act freely and the ambient metric agrees with the norm of displacement vectors. The translation
subgroup is interpreted through Mathlib's canonical equivalence between additive subgroups and
`ℤ`-submodules. Periodicity requires that this `ℤ`-submodule be a Mathlib full `ℤ`-lattice and have
only finitely many occupied-site orbits. -/
structure Periodic (X : AtomicConfiguration E Species) : Prop where
  /-- The translation vectors form a discrete subgroup. -/
  discreteTranslations :
    DiscreteTopology (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)))
  /-- The translation vectors form a full `ℤ`-lattice in the translation-vector space. -/
  isZLattice :
    @IsZLattice ℝ inferInstance V inferInstance inferInstance
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) discreteTranslations
  /-- There are finitely many occupied-site classes modulo translations. -/
  finiteModuloTranslations : X.FiniteModuloTranslations (V := V)

end Periodic

end AtomicConfiguration

end LeanCondensedMatter.Crystal
