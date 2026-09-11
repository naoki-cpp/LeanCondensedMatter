/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.AtomicConfiguration
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Symmetries of atomic configurations

This file derives the full species-preserving geometric symmetry group of an atomic
configuration. A symmetry is not stored in the primitive configuration: it is an ambient
isometry that preserves the set of sites of every species.
-/

namespace LeanCondensedMatter.Crystal

namespace AtomicConfiguration

variable {E Species : Type*}

/-- The ambient points occupied by atoms of species `s`. -/
def sitesOfSpecies (X : AtomicConfiguration E Species) (s : Species) : Set E :=
  {x | ∃ hx : x ∈ X.occupied, X.species ⟨x, hx⟩ = s}

@[simp]
theorem mem_sitesOfSpecies {X : AtomicConfiguration E Species} {s : Species} {x : E} :
    x ∈ X.sitesOfSpecies s ↔ ∃ hx : x ∈ X.occupied, X.species ⟨x, hx⟩ = s :=
  Iff.rfl

/-- The occupied set is the union of the species-resolved site sets. -/
theorem occupied_eq_iUnion_sitesOfSpecies (X : AtomicConfiguration E Species) :
    X.occupied = ⋃ s, X.sitesOfSpecies s := by
  ext x
  constructor
  · intro hx
    refine Set.mem_iUnion.2 ⟨X.species ⟨x, hx⟩, ?_⟩
    exact ⟨hx, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨s, hx⟩
    rcases hx with ⟨hoccupied, _⟩
    exact hoccupied

section Symmetry

variable [MetricSpace E]

/-- The full species-preserving geometric symmetry group of an atomic configuration.

An ambient isometry is a symmetry exactly when it preserves the set of occupied sites of each
species. Using Mathlib's isometry group keeps composition and inversion in the ambient geometry
rather than reimplementing group structure locally. -/
def symmetryGroup (X : AtomicConfiguration E Species) : Subgroup (E ≃ᵢ E) where
  carrier := {g | ∀ s, g '' X.sitesOfSpecies s = X.sitesOfSpecies s}
  one_mem' := by
    intro s
    simp
  mul_mem' {g h} hg hh := by
    intro s
    calc
      (g * h : E ≃ᵢ E) '' X.sitesOfSpecies s = g '' (h '' X.sitesOfSpecies s) := by
        rw [Set.image_image]
        rfl
      _ = g '' X.sitesOfSpecies s := by rw [hh s]
      _ = X.sitesOfSpecies s := hg s
  inv_mem' {g} hg := by
    intro s
    calc
      (g⁻¹ : E ≃ᵢ E) '' X.sitesOfSpecies s =
          (g⁻¹ : E ≃ᵢ E) '' (g '' X.sitesOfSpecies s) := by rw [hg s]
      _ = X.sitesOfSpecies s := by
        change g.symm '' (g '' X.sitesOfSpecies s) = X.sitesOfSpecies s
        exact g.toEquiv.symm_image_image _

@[simp]
theorem mem_symmetryGroup {X : AtomicConfiguration E Species} {g : E ≃ᵢ E} :
    g ∈ X.symmetryGroup ↔ ∀ s, g '' X.sitesOfSpecies s = X.sitesOfSpecies s :=
  Iff.rfl

/-- Every species-preserving symmetry preserves the total occupied set. -/
theorem image_occupied_eq {X : AtomicConfiguration E Species} {g : E ≃ᵢ E}
    (hg : g ∈ X.symmetryGroup) : g '' X.occupied = X.occupied := by
  rw [X.occupied_eq_iUnion_sitesOfSpecies, Set.image_iUnion]
  simp_rw [hg]

/-- The action of a configuration symmetry on one occupied site. -/
def mapSite (X : AtomicConfiguration E Species) (g : X.symmetryGroup) (x : X.Site) : X.Site :=
  ⟨(g : E ≃ᵢ E) x, by
    have hx : (g : E ≃ᵢ E) x ∈ (g : E ≃ᵢ E) '' X.occupied :=
      ⟨x, x.property, rfl⟩
    rwa [X.image_occupied_eq g.property] at hx⟩

@[simp]
theorem coe_mapSite (X : AtomicConfiguration E Species) (g : X.symmetryGroup) (x : X.Site) :
    (X.mapSite g x : E) = (g : E ≃ᵢ E) x :=
  rfl

/-- A configuration symmetry induces a permutation of occupied sites. -/
def siteEquiv (X : AtomicConfiguration E Species) (g : X.symmetryGroup) : X.Site ≃ X.Site where
  toFun := X.mapSite g
  invFun := X.mapSite g⁻¹
  left_inv x := by
    apply Subtype.ext
    simp [mapSite]
  right_inv x := by
    apply Subtype.ext
    simp [mapSite]

@[simp]
theorem coe_siteEquiv (X : AtomicConfiguration E Species) (g : X.symmetryGroup) (x : X.Site) :
    (X.siteEquiv g x : E) = (g : E ≃ᵢ E) x :=
  rfl

/-- The induced site permutation preserves the species label. -/
@[simp]
theorem species_siteEquiv (X : AtomicConfiguration E Species) (g : X.symmetryGroup) (x : X.Site) :
    X.species (X.siteEquiv g x) = X.species x := by
  have hx : (x : E) ∈ X.sitesOfSpecies (X.species x) := ⟨x.property, rfl⟩
  have hgx : (g : E ≃ᵢ E) x ∈ X.sitesOfSpecies (X.species x) := by
    rw [← g.property (X.species x)]
    exact ⟨x, hx, rfl⟩
  rcases hgx with ⟨hoccupied, hs⟩
  simpa [siteEquiv, mapSite] using hs

end Symmetry

end AtomicConfiguration

end LeanCondensedMatter.Crystal
