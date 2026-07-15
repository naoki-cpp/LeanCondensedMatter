import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# The partition lattice and its Möbius function

Adapts Mathlib's `Finpartition s` (the lattice of partitions of a finite set `s`, ordered by
refinement) to Mathlib's general `IncidenceAlgebra` (Möbius function / Möbius inversion)
machinery.

**Scope note:** this is pure combinatorics (Track B of `notes/roadmap.md`), independent of the
physics content elsewhere in this project. See `notes/model-and-assumptions.md` for the survey
of what Mathlib/PhysLean already provide here.
-/

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The partition lattice `Finpartition s` is locally finite: it is already a `Fintype`
(Mathlib), and its `≤` (refinement) is decidable, so every interval is a finite set. This is
the adapter needed to apply Mathlib's `IncidenceAlgebra` (Möbius function, Möbius inversion) to
the partition lattice. -/
noncomputable instance : LocallyFiniteOrder (Finpartition s) := by
  classical
  exact Fintype.toLocallyFiniteOrder

namespace Finpartition

variable {a : Finset α}

/-- `P.bind Q` (the partition obtained by further splitting each part of `P` according to `Q`)
refines `P`. -/
theorem bind_le (P : Finpartition a) (Q : ∀ i ∈ P.parts, Finpartition i) : P.bind Q ≤ P := by
  intro d hd
  obtain ⟨A, hA, hdA⟩ := mem_bind.1 hd
  exact ⟨A, hA, (Q A hA).le hdA⟩

/-- Membership in a restricted partition, unfolded: `d` is a part of `P` restricted to `b` iff
`d` is nonempty and equals some part of `P` intersected with `b`. Named so later proofs don't
each need to unfold `Finpartition.restrict`'s definition by hand. -/
theorem mem_restrict_iff {P : Finpartition a} {hb : b ≤ a} {d : Finset α} :
    d ∈ (P.restrict hb).parts ↔ d ≠ ⊥ ∧ ∃ A ∈ P.parts, A ⊓ b = d := by
  simp only [restrict, Finset.mem_erase, Finset.mem_image]

/-- If a nonempty part `A` is contained in both `B` and `B'`, two parts of the same partition
`σ`, then `B = B'`: distinct parts of a partition are disjoint, so their common refinement with a
nonempty set forces them to coincide. The core "no two parts of `σ` can both host a given nonzero
overlap" fact driving `bind_restrict_eq_of_le`/`restrict_bind_eq`. -/
theorem eq_of_inf_ne_bot {σ : Finpartition a} {A B B' : Finset α} (hB : B ∈ σ.parts)
    (hB' : B' ∈ σ.parts) (hAB : A ≤ B) (hAB' : A ≤ B') (hA : A ≠ ⊥) : B = B' := by
  by_contra hne
  have hdisj : Disjoint B B' := σ.disjoint hB hB' hne
  have hle : A ≤ B ⊓ B' := le_inf hAB hAB'
  rw [hdisj.eq_bot] at hle
  exact hA (bot_unique hle)

/-- The key bijection underlying the moment-cumulant / Möbius-inversion formula on the partition
lattice: if `π` refines `σ`, then splitting `σ` by restricting `π` to each of `σ`'s parts and
gluing the pieces back together via `bind` recovers `π`. Combined with `restrict_bind_eq`, this
witnesses `refinementsEquivFiberPartitions : {π // π ≤ σ} ≃ Π B ∈ σ.parts, Finpartition B`. -/
theorem bind_restrict_eq_of_le {σ π : Finpartition a} (h : π ≤ σ) :
    σ.bind (fun _B hB => π.restrict (σ.le hB)) = π := by
  ext d
  rw [mem_bind]
  constructor
  · rintro ⟨B, hB, hd⟩
    rw [mem_restrict_iff] at hd
    obtain ⟨hd0, A, hA, rfl⟩ := hd
    obtain ⟨B', hB', hAB'⟩ := h hA
    have hBB' : B = B' := eq_of_inf_ne_bot hB hB' inf_le_right (inf_le_left.trans hAB') hd0
    rwa [hBB', inf_eq_left.2 hAB']
  · intro hd
    obtain ⟨B, hB, hdB⟩ := h hd
    refine ⟨B, hB, ?_⟩
    rw [mem_restrict_iff]
    exact ⟨π.ne_bot hd, d, hd, inf_eq_left.2 hdB⟩

/-- The other half of `bind_restrict_eq_of_le`: given a partition `B ↦ Q B hB` of each part `B`
of `σ`, gluing them together via `bind` and then restricting back to a single part `B` recovers
`Q B hB` exactly. Distinct parts of `σ`.bind `Q` only intersect nontrivially with the `σ`-part
they came from, by `eq_of_inf_ne_bot`. -/
theorem restrict_bind_eq (σ : Finpartition a) (Q : ∀ B ∈ σ.parts, Finpartition B) {B : Finset α}
    (hB : B ∈ σ.parts) : (σ.bind Q).restrict (σ.le hB) = Q B hB := by
  ext d
  rw [mem_restrict_iff]
  constructor
  · rintro ⟨hd0, A, hA, rfl⟩
    obtain ⟨C, hC, hAC⟩ := mem_bind.1 hA
    have hAleC : A ≤ C := (Q C hC).le hAC
    have hCB : C = B := eq_of_inf_ne_bot hC hB (inf_le_left.trans hAleC) inf_le_right hd0
    subst hCB
    rwa [inf_eq_left.2 hAleC]
  · intro hd
    exact ⟨(Q B hB).ne_bot hd, d, mem_bind.2 ⟨B, hB, hd⟩, inf_eq_left.2 ((Q B hB).le hd)⟩

/-- **The refinement fiber decomposition.** The refinements of `σ` (partitions `π ≤ σ`, i.e.
finer than `σ`) correspond exactly to choosing, independently, a partition of each part `B` of
`σ`: forward via `restrict` (splitting `π` by intersecting with each part of `σ`), backward via
`bind` (gluing the chosen per-part partitions back together). This exhibits the interval
`[⊥, σ]` in the partition lattice as (in bijection with) the product `Π B ∈ σ.parts,
Finpartition B` — the structural fact underlying the moment-cumulant / Möbius-inversion formula
on the partition lattice (`notes/roadmap.md`, Linked Cluster Theorem target). -/
def refinementsEquivFiberPartitions (σ : Finpartition a) :
    {π : Finpartition a // π ≤ σ} ≃ (∀ B : σ.parts, Finpartition (B : Finset α)) where
  toFun π B := π.1.restrict (σ.le B.2)
  invFun Q := ⟨σ.bind (fun B hB => Q ⟨B, hB⟩), bind_le σ _⟩
  left_inv π := Subtype.ext (bind_restrict_eq_of_le π.2)
  right_inv Q := funext fun B => restrict_bind_eq σ (fun C hC => Q ⟨C, hC⟩) B.2

end Finpartition
