/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.AtomicConfiguration
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.GroupAction.Defs
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
  have hspecies : ∀ s, g '' X.sitesOfSpecies s = X.sitesOfSpecies s :=
    mem_symmetryGroup.1 hg
  rw [X.occupied_eq_iUnion_sitesOfSpecies, Set.image_iUnion]
  simp_rw [hspecies]

/-- Configuration symmetries act canonically on occupied sites. -/
instance siteMulAction (X : AtomicConfiguration E Species) : MulAction X.symmetryGroup X.Site where
  smul g x :=
    ⟨(g : E ≃ᵢ E) x, by
      have hx : (g : E ≃ᵢ E) x ∈ (g : E ≃ᵢ E) '' X.occupied :=
        ⟨x, x.property, rfl⟩
      rwa [X.image_occupied_eq g.property] at hx⟩
  one_smul x := by
    apply Subtype.ext
    rfl
  mul_smul g h x := by
    apply Subtype.ext
    rfl

@[simp]
theorem coe_smul_site (X : AtomicConfiguration E Species) (g : X.symmetryGroup) (x : X.Site) :
    ((g • x : X.Site) : E) = (g : E ≃ᵢ E) x :=
  rfl

/-- Membership in a site orbit is exactly reachability by an ambient configuration symmetry. -/
@[simp]
theorem mem_site_orbit_iff (X : AtomicConfiguration E Species) (x y : X.Site) :
    y ∈ MulAction.orbit X.symmetryGroup x ↔
      ∃ g : X.symmetryGroup, (g : E ≃ᵢ E) x = (y : E) := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, h⟩
    refine ⟨g, ?_⟩
    exact congrArg (fun z : X.Site => (z : E)) h
  · rintro ⟨g, h⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact h

/-- Fixing a site under the canonical action is exactly fixing its underlying ambient point. -/
@[simp]
theorem smul_site_eq_self_iff (X : AtomicConfiguration E Species) (g : X.symmetryGroup)
    (x : X.Site) :
    g • x = x ↔ (g : E ≃ᵢ E) x = x := by
  constructor
  · intro h
    have hcoe := congrArg (fun y : X.Site => (y : E)) h
    simpa using hcoe
  · intro h
    apply Subtype.ext
    simpa using h

/-- The canonical site action preserves the species label. -/
@[simp]
theorem species_smul (X : AtomicConfiguration E Species) (g : X.symmetryGroup) (x : X.Site) :
    X.species (g • x) = X.species x := by
  have hx : (x : E) ∈ X.sitesOfSpecies (X.species x) := ⟨x.property, rfl⟩
  have hgx : (g : E ≃ᵢ E) x ∈ X.sitesOfSpecies (X.species x) := by
    rw [← g.property (X.species x)]
    exact ⟨x, hx, rfl⟩
  rcases hgx with ⟨hoccupied, hs⟩
  have hsite : g • x = (⟨(g : E ≃ᵢ E) x, hoccupied⟩ : X.Site) := by
    apply Subtype.ext
    rfl
  rw [hsite]
  exact hs

/-- Sites in the same symmetry orbit have the same species label. -/
theorem species_eq_of_mem_site_orbit (X : AtomicConfiguration E Species) {x y : X.Site}
    (hy : y ∈ MulAction.orbit X.symmetryGroup x) : X.species y = X.species x := by
  rcases MulAction.mem_orbit_iff.1 hy with ⟨g, rfl⟩
  exact X.species_smul g x

/-- Configuration symmetries act canonically on unordered bonds. -/
instance bondMulAction (X : AtomicConfiguration E Species) : MulAction X.symmetryGroup X.Bond where
  smul g b :=
    ⟨Sym2.map (fun x : X.Site => g • x) b.1, by
      have hinj : Function.Injective (fun x : X.Site => g • x) := by
        intro x y hxy
        have h := congrArg (fun z : X.Site => (g⁻¹ : X.symmetryGroup) • z) hxy
        simpa using h
      simpa only [Sym2.isDiag_map hinj] using b.2⟩
  one_smul b := by
    apply Subtype.ext
    refine Sym2.inductionOn (b : Sym2 X.Site) ?_
    intro x y
    simp
  mul_smul g h b := by
    apply Subtype.ext
    refine Sym2.inductionOn (b : Sym2 X.Site) ?_
    intro x y
    simp [mul_smul]

@[simp]
theorem coe_smul_bond (X : AtomicConfiguration E Species) (g : X.symmetryGroup) (b : X.Bond) :
    ((g • b : X.Bond) : Sym2 X.Site) =
      Sym2.map (fun x : X.Site => g • x) (b : Sym2 X.Site) :=
  rfl

/-- Fixing a bond under the canonical action is exactly fixing its underlying unordered pair. -/
@[simp]
theorem smul_bond_eq_self_iff (X : AtomicConfiguration E Species) (g : X.symmetryGroup)
    (b : X.Bond) :
    g • b = b ↔
      Sym2.map (fun x : X.Site => g • x) (b : Sym2 X.Site) = (b : Sym2 X.Site) := by
  constructor
  · intro h
    simpa using congrArg (fun c : X.Bond => (c : Sym2 X.Site)) h
  · intro h
    apply Subtype.ext
    exact h

/-- Membership in a bond orbit is exactly reachability of the underlying unordered pair. -/
@[simp]
theorem mem_bond_orbit_iff (X : AtomicConfiguration E Species) (b c : X.Bond) :
    c ∈ MulAction.orbit X.symmetryGroup b ↔
      ∃ g : X.symmetryGroup,
        Sym2.map (fun x : X.Site => g • x) (b : Sym2 X.Site) = (c : Sym2 X.Site) := by
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, h⟩
    refine ⟨g, ?_⟩
    simpa using congrArg (fun d : X.Bond => (d : Sym2 X.Site)) h
  · rintro ⟨g, h⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    exact h

end Symmetry

end AtomicConfiguration

end LeanCondensedMatter.Crystal
