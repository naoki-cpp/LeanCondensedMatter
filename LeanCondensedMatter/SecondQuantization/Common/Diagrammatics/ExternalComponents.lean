import LeanCondensedMatter.Combinatorics.SetPartition.SingleBlock
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

/-- Every pair of external vertices belongs to the same connected component.

This property allows disconnected purely internal (vacuum) components. It is
therefore distinct from both vacuum-freeness and whole-graph
preconnectedness when more than two external legs are present. -/
def AllExternalVerticesConnected (G : SimpleGraph (External ⊕ Internal)) : Prop :=
  ∀ a b : External,
    G.Reachable (Sum.inl a : External ⊕ Internal) (Sum.inl b)

/-- Vacuum-freeness is invariant under a graph isomorphism preserving the external and
internal sectors up to relabeling. -/
theorem hasNoVacuumComponent_congr_iff
    {External' Internal' : Type*}
    {G : SimpleGraph (External ⊕ Internal)}
    {H : SimpleGraph (External' ⊕ Internal')}
    (φ : G ≃g H) (eExt : External ≃ External') (eInt : Internal ≃ Internal')
    (hext : ∀ x : External, φ (Sum.inl x) = Sum.inl (eExt x))
    (hint : ∀ x : Internal, φ (Sum.inr x) = Sum.inr (eInt x)) :
    HasNoVacuumComponent H ↔ HasNoVacuumComponent G := by
  constructor
  · intro h v
    obtain ⟨f, hf⟩ := h (eInt v)
    refine ⟨eExt.symm f, ?_⟩
    apply (SimpleGraph.Iso.reachable_iff
      (φ := φ) (u := Sum.inl (eExt.symm f)) (v := Sum.inr v)).mp
    simpa only [hext, hint, Equiv.apply_symm_apply] using hf
  · intro h v
    obtain ⟨f, hf⟩ := h (eInt.symm v)
    refine ⟨eExt f, ?_⟩
    have hreach := (SimpleGraph.Iso.reachable_iff
      (φ := φ) (u := Sum.inl f) (v := Sum.inr (eInt.symm v))).mpr hf
    simpa only [hext, hint, Equiv.apply_symm_apply] using hreach

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

/-- Full connectivity factors into two logically independent conditions:
no vacuum component, and mutual connectivity of all external vertices.

The nonempty external sector supplies an external anchor for every internal
vertex. This holds independently of the graph's diagrammatic realization. -/
theorem preconnected_iff_hasNoVacuumComponent_and_allExternalVerticesConnected
    [Nonempty External] (G : SimpleGraph (External ⊕ Internal)) :
    G.Preconnected ↔
      HasNoVacuumComponent G ∧ AllExternalVerticesConnected G := by
  constructor
  · intro h
    exact ⟨hasNoVacuumComponent_of_preconnected G h, fun _ _ => h _ _⟩
  · rintro ⟨hVacuum, hExternal⟩
    intro x y
    cases x with
    | inl a =>
        cases y with
        | inl b => exact hExternal a b
        | inr v =>
            obtain ⟨b, hb⟩ := hVacuum v
            exact (hExternal a b).trans hb
    | inr v =>
        obtain ⟨a, ha⟩ := hVacuum v
        cases y with
        | inl b => exact ha.symm.trans (hExternal a b)
        | inr w =>
            obtain ⟨b, hb⟩ := hVacuum w
            exact ha.symm.trans ((hExternal a b).trans hb)

/-- External connectivity alone can be expressed using any distinguished
external vertex as an anchor, without reference to vacuum components. -/
theorem allExternalVerticesConnected_iff_reachable_anchor
    (G : SimpleGraph (External ⊕ Internal)) (anchor : External) :
    AllExternalVerticesConnected G ↔
      ∀ e : External,
        G.Reachable (Sum.inl anchor : External ⊕ Internal) (Sum.inl e) := by
  constructor
  · intro h e
    exact h anchor e
  · intro h a b
    exact (h a).symm.trans (h b)

section ExternalPartition

variable [Fintype External] [DecidableEq External]

open Classical in
/-- The partition of external vertices according to reachability in the full
external/internal graph. Internal paths are retained when deciding whether two
external vertices belong to the same block. -/
noncomputable def externalComponentPartition
    (G : SimpleGraph (External ⊕ Internal)) :
    Finpartition (Finset.univ : Finset External) :=
  Finpartition.ofSetoid {
    r := fun a b => G.Reachable (Sum.inl a) (Sum.inl b)
    iseqv := ⟨fun _ => SimpleGraph.Reachable.refl _,
      fun h => h.symm,
      fun hab hbc => hab.trans hbc⟩
  }

/-- An external vertex lies in the block of another exactly when they are
connected through the full graph, including its internal vertices. -/
theorem mem_externalComponentPartition_part
    (G : SimpleGraph (External ⊕ Internal)) (a b : External) :
    b ∈ (externalComponentPartition G).part a ↔
      G.Reachable (Sum.inl a) (Sum.inl b) := by
  classical
  unfold externalComponentPartition
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

/-- For a nonempty external sector, mutual external connectivity means that
the external-component partition consists of exactly the full external set.

Internal (vacuum) components do not appear in this partition. -/
theorem allExternalVerticesConnected_iff_externalComponentPartition_parts_eq_singleton
    [Nonempty External] (G : SimpleGraph (External ⊕ Internal)) :
    AllExternalVerticesConnected G ↔
      (externalComponentPartition G).parts =
        {(Finset.univ : Finset External)} := by
  classical
  let a : External := Classical.choice inferInstance
  constructor
  · intro h
    have hPart : (externalComponentPartition G).part a =
        (Finset.univ : Finset External) := by
      ext b
      simp only [Finset.mem_univ, iff_true]
      exact (mem_externalComponentPartition_part G a b).2 (h a b)
    ext B
    constructor
    · intro hB
      obtain ⟨b, -, hb⟩ :=
        (externalComponentPartition G).part_surjOn hB
      apply Finset.mem_singleton.mpr
      rw [← hb]
      ext e
      simp only [Finset.mem_univ, iff_true]
      exact (mem_externalComponentPartition_part G b e).2 (h b e)
    · intro hB
      have hEq : B = (Finset.univ : Finset External) :=
        Finset.mem_singleton.mp hB
      rw [hEq.trans hPart.symm]
      exact (externalComponentPartition G).part_mem.2 (Finset.mem_univ a)
  · intro h a b
    have hPart :
        (externalComponentPartition G).part a =
          (Finset.univ : Finset External) := by
      have hMem :
          (externalComponentPartition G).part a ∈
            (externalComponentPartition G).parts :=
        (externalComponentPartition G).part_mem.2 (Finset.mem_univ a)
      rw [h] at hMem
      exact Finset.mem_singleton.mp hMem
    apply (mem_externalComponentPartition_part G a b).1
    rw [hPart]
    exact Finset.mem_univ b

/-- A nonempty external sector is mutually connected precisely when its
external-component partition has one block. This is the graph-level
single-block criterion used by finite-set cumulant extraction. -/
theorem allExternalVerticesConnected_iff_externalComponentPartition_parts_card_eq_one
    [Nonempty External] (G : SimpleGraph (External ⊕ Internal)) :
    AllExternalVerticesConnected G ↔
      (externalComponentPartition G).parts.card = 1 := by
  rw [allExternalVerticesConnected_iff_externalComponentPartition_parts_eq_singleton]
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    exact Finpartition.parts_eq_singleton_of_card_eq_one
      (externalComponentPartition G) h

end ExternalPartition

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

/-- All external vertices are mutually reachable exactly when there is one
externally supported component, namely the component containing a chosen external anchor.

Pure-vacuum components are unrestricted. This characterizes the component
selection needed for external cumulants without conflating it with
whole-graph preconnectedness. -/
theorem allExternalVerticesConnected_iff_supportedComponentParts_eq_singleton
    (G : SimpleGraph (External ⊕ Internal)) (anchor : External) :
    AllExternalVerticesConnected G ↔
      externallySupportedComponentParts G =
        { (⟨G.componentBlock (Sum.inl anchor),
            G.componentBlock_mem_componentPartition (Sum.inl anchor)⟩ :
              G.componentPartition.parts) } := by
  classical
  rw [allExternalVerticesConnected_iff_reachable_anchor G anchor]
  constructor
  · intro h
    ext B
    constructor
    · intro hB
      obtain ⟨e, he⟩ :=
        (componentMeetsExternal_iff_exists_eq_componentBlock G B).mp
          ((mem_externallySupportedComponentParts G B).mp hB)
      apply Finset.mem_singleton.mpr
      apply Subtype.ext
      change (B : Finset (External ⊕ Internal)) =
        G.componentBlock (Sum.inl anchor)
      rw [he]
      exact (G.componentBlock_eq_iff_mem
        (G.componentBlock_mem_componentPartition (Sum.inl anchor))
        (Sum.inl e)).2
          ((G.mem_componentBlock (Sum.inl anchor) (Sum.inl e)).2 (h e).symm)
    · intro hB
      have heq : B =
          (⟨G.componentBlock (Sum.inl anchor),
              G.componentBlock_mem_componentPartition (Sum.inl anchor)⟩ :
                G.componentPartition.parts) :=
        Finset.mem_singleton.mp hB
      subst B
      exact (mem_externallySupportedComponentParts G _).2
        ⟨anchor, G.self_mem_componentBlock (Sum.inl anchor)⟩
  · intro h e
    let B : G.componentPartition.parts :=
      ⟨G.componentBlock (Sum.inl e),
        G.componentBlock_mem_componentPartition (Sum.inl e)⟩
    have hB : B ∈ externallySupportedComponentParts G :=
      (mem_externallySupportedComponentParts G B).2
        ⟨e, G.self_mem_componentBlock (Sum.inl e)⟩
    rw [h] at hB
    have heq : G.componentBlock (Sum.inl e) =
        G.componentBlock (Sum.inl anchor) :=
      congrArg Subtype.val (Finset.mem_singleton.mp hB)
    have hreach : G.Reachable (Sum.inl e) (Sum.inl anchor) := by
      apply (G.mem_componentBlock (Sum.inl anchor) (Sum.inl e)).1
      rw [← heq]
      exact G.self_mem_componentBlock (Sum.inl e)
    exact hreach.symm

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
