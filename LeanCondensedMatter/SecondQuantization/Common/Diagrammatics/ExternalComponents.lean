import LeanCondensedMatter.Combinatorics.SimpleGraphComponentPartition
import Mathlib.Data.Finset.Sum

set_option linter.style.header false

/-!
# External-sector component semantics

For a finite graph on vertices of the form `External ⊕ Internal`, this module classifies connected
components by whether they meet the external summand. The definitions are independent of any
particular diagram family and are shared by two-point and general external-insertion diagrams.
-/

namespace SecondQuantization
namespace Common

variable {External Internal : Type*}

/-- A finite vertex set meets the external sector when it contains a left-summand vertex. -/
def ComponentMeetsExternal (B : Finset (External ⊕ Internal)) : Prop :=
  ∃ e : External, (Sum.inl e : External ⊕ Internal) ∈ B

/-- A finite vertex set is vacuum when it contains no external vertex. -/
def ComponentIsVacuum (B : Finset (External ⊕ Internal)) : Prop :=
  ¬ ComponentMeetsExternal B

/-- Every internal vertex belongs to a graph component meeting the external sector. -/
def HasNoVacuumComponent (G : SimpleGraph (External ⊕ Internal)) : Prop :=
  ∀ v : Internal, ∃ e : External,
    G.Reachable (Sum.inl e : External ⊕ Internal) (Sum.inr v)

/-- External support is equivalent to nonemptiness of Mathlib's left-summand extraction. -/
theorem componentMeetsExternal_iff_toLeft_nonempty
    (B : Finset (External ⊕ Internal)) :
    ComponentMeetsExternal B ↔ B.toLeft.Nonempty := by
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, Finset.mem_toLeft.2 he⟩
  · rintro ⟨e, he⟩
    exact ⟨e, Finset.mem_toLeft.1 he⟩

/-- A preconnected external/internal graph has no vacuum component when its external type is
nonempty. -/
theorem hasNoVacuumComponent_of_preconnected [Nonempty External]
    (G : SimpleGraph (External ⊕ Internal)) (h : G.Preconnected) :
    HasNoVacuumComponent G := by
  intro v
  let e : External := Classical.choice inferInstance
  exact ⟨e, h _ _⟩

section Finite

variable [Fintype External] [Fintype Internal]
  [DecidableEq External] [DecidableEq Internal]

/-- A connected component meets the external sector exactly when it is the component block of some
external vertex. -/
theorem componentMeetsExternal_iff_exists_eq_componentBlock
    (G : SimpleGraph (External ⊕ Internal))
    (B : G.componentPartition.parts) :
    ComponentMeetsExternal (B : Finset (External ⊕ Internal)) ↔
      ∃ e : External,
        (B : Finset (External ⊕ Internal)) = G.componentBlock (Sum.inl e) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    exact ((G.componentBlock_eq_iff_mem B.2 (Sum.inl e)).2 he).symm
  · rintro ⟨e, hB⟩
    refine ⟨e, ?_⟩
    rw [hB]
    exact G.self_mem_componentBlock (Sum.inl e)

/-- Vacuum-freeness is equivalent to every connected component meeting the external sector. -/
theorem hasNoVacuumComponent_iff_forall_component_meetsExternal
    (G : SimpleGraph (External ⊕ Internal)) :
    HasNoVacuumComponent G ↔
      ∀ B : G.componentPartition.parts,
        ComponentMeetsExternal (B : Finset (External ⊕ Internal)) := by
  constructor
  · intro h B
    obtain ⟨v, -, hv⟩ := G.componentPartition.part_surjOn B.2
    cases v with
    | inl e =>
        refine ⟨e, ?_⟩
        rw [← hv]
        exact G.self_mem_componentBlock (Sum.inl e)
    | inr v =>
        obtain ⟨e, he⟩ := h v
        refine ⟨e, ?_⟩
        rw [← hv]
        exact (G.mem_componentBlock (Sum.inr v) (Sum.inl e)).2 he
  · intro h v
    let B : G.componentPartition.parts :=
      ⟨G.componentBlock (Sum.inr v),
        G.componentBlock_mem_componentPartition (Sum.inr v)⟩
    obtain ⟨e, he⟩ := h B
    refine ⟨e, ?_⟩
    change (Sum.inl e : External ⊕ Internal) ∈
      G.componentBlock (Sum.inr v) at he
    exact (G.mem_componentBlock (Sum.inr v) (Sum.inl e)).1 he

open Classical in
/-- The finite set of component parts meeting the external sector. -/
noncomputable def externallySupportedComponentParts
    (G : SimpleGraph (External ⊕ Internal)) :
    Finset G.componentPartition.parts :=
  Finset.univ.filter fun B =>
    ComponentMeetsExternal (B : Finset (External ⊕ Internal))

@[simp]
theorem mem_externallySupportedComponentParts
    (G : SimpleGraph (External ⊕ Internal))
    (B : G.componentPartition.parts) :
    B ∈ externallySupportedComponentParts G ↔
      ComponentMeetsExternal (B : Finset (External ⊕ Internal)) := by
  simp [externallySupportedComponentParts]

open Classical in
/-- The finite set of component parts containing no external vertex. -/
noncomputable def vacuumComponentParts
    (G : SimpleGraph (External ⊕ Internal)) :
    Finset G.componentPartition.parts :=
  Finset.univ.filter fun B =>
    ComponentIsVacuum (B : Finset (External ⊕ Internal))

@[simp]
theorem mem_vacuumComponentParts
    (G : SimpleGraph (External ⊕ Internal))
    (B : G.componentPartition.parts) :
    B ∈ vacuumComponentParts G ↔
      ComponentIsVacuum (B : Finset (External ⊕ Internal)) := by
  simp [vacuumComponentParts]

/-- Every connected component is either externally supported or vacuum. -/
theorem univ_componentParts_eq_supported_union_vacuum
    (G : SimpleGraph (External ⊕ Internal)) :
    (Finset.univ : Finset G.componentPartition.parts) =
      externallySupportedComponentParts G ∪ vacuumComponentParts G := by
  classical
  ext B
  by_cases h : ComponentMeetsExternal (B : Finset (External ⊕ Internal)) <;>
    simp [ComponentIsVacuum, h]

/-- Externally supported and vacuum components are disjoint. -/
theorem externallySupportedComponentParts_disjoint_vacuumComponentParts
    (G : SimpleGraph (External ⊕ Internal)) :
    Disjoint (externallySupportedComponentParts G) (vacuumComponentParts G) := by
  classical
  rw [Finset.disjoint_left]
  intro B hSupported hVacuum
  exact ((mem_vacuumComponentParts G B).1 hVacuum)
    ((mem_externallySupportedComponentParts G B).1 hSupported)

/-- A graph has no vacuum component exactly when its finite set of vacuum component parts is empty. -/
theorem hasNoVacuumComponent_iff_vacuumComponentParts_eq_empty
    (G : SimpleGraph (External ⊕ Internal)) :
    HasNoVacuumComponent G ↔ vacuumComponentParts G = ∅ := by
  rw [hasNoVacuumComponent_iff_forall_component_meetsExternal]
  constructor
  · intro h
    ext B
    rw [mem_vacuumComponentParts]
    simp [ComponentIsVacuum, h B]
  · intro h B
    by_contra hB
    have hmem : B ∈ vacuumComponentParts G :=
      (mem_vacuumComponentParts G B).2 hB
    rw [h] at hmem
    simpa using hmem

end Finite

end Common
end SecondQuantization
