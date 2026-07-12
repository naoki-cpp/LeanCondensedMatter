import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra

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

/-- The key bijection underlying the moment-cumulant / Möbius-inversion formula on the partition
lattice: if `π` refines `σ`, then splitting `σ` by restricting `π` to each of `σ`'s parts and
gluing the pieces back together via `bind` recovers `π`. Combined with `bind_le`, this witnesses
`{π // π ≤ σ} ≃ Π B ∈ σ.parts, Finpartition B`. -/
theorem bind_restrict_eq_of_le {σ π : Finpartition a} (h : π ≤ σ) :
    σ.bind (fun B hB => π.restrict (σ.le hB)) = π := by
  ext d
  rw [mem_bind]
  constructor
  · rintro ⟨B, hB, hd⟩
    simp only [restrict, Finset.mem_erase, Finset.mem_image] at hd
    obtain ⟨hd0, A, hA, rfl⟩ := hd
    obtain ⟨B', hB', hAB'⟩ := h hA
    have hBB' : B = B' := by
      by_contra hne
      apply hd0
      have hdisj : Disjoint B' B := σ.disjoint hB' hB (Ne.symm hne)
      have hle : A ⊓ B ≤ B' ⊓ B := inf_le_inf_right B hAB'
      rw [hdisj.eq_bot] at hle
      exact bot_unique hle
    rwa [hBB', inf_eq_left.2 hAB']
  · intro hd
    obtain ⟨B, hB, hdB⟩ := h hd
    have heq : d ⊓ B = d := inf_eq_left.2 hdB
    refine ⟨B, hB, ?_⟩
    simp only [restrict, Finset.mem_erase, Finset.mem_image]
    exact ⟨π.ne_bot hd, d, hd, heq⟩

end Finpartition
