import LeanCondensedMatter.Combinatorics.MomentCumulant

set_option linter.style.header false

/-!
# Moment factorization under independence (towards connected cumulants)

A first, deliberately abstract step towards the Linked Cluster Theorem's "only connected
diagrams survive in `log Z`" statement: if a moment function `m` factors independently across a
disjoint pair of finite sets `A`, `B` (`IsIndependentAcross`), then the partition-block product
`partitionProduct m π` itself factors as a product over the restrictions of `π` to `A` and to
`B`, for every partition `π` of `A ⊔ B`.

**Scope.** This file stops at the partition-level factorization
(`partitionProduct_eq_mul_of_isIndependentAcross`). It does *not* yet prove the deeper "cumulants
vanish across independence" theorem (`cumulantFromMoment m (A ⊔ B) = 0` under independence) — that
needs summing over the fiber structure of `π ↦ (π.restrict hA, π.restrict hB)`, which is a
*matching* between `(π.restrict hA).parts` and `(π.restrict hB).parts` rather than a bijection,
and is a genuinely harder combinatorial argument not attempted here. See
`notes/roadmaps/combinatorics.md` for what remains.
-/

open IncidenceAlgebra

variable {α : Type*} [DecidableEq α]

namespace Finpartition

/-- **`m` factors independently across the disjoint pair `(A, B)`.** For every `T ⊆ A ⊔ B`,
`m T = m (T ⊓ A) * m (T ⊓ B)` — the moment-level statement of "data indexed by `A` and data
indexed by `B` are independent". `m ⊥ = 1` is required explicitly (not derivable from the
factorization alone, which only forces `m ⊥ ∈ {0, 1}`: the `m ⊥ = 0` branch would force `m T = 0`
for every `T ⊆ A ⊔ B`, a degenerate solution this definition deliberately excludes). -/
def IsIndependentAcross (m : Finset α → ℂ) (A B : Finset α) : Prop :=
  Disjoint A B ∧ m ⊥ = 1 ∧ ∀ T ≤ A ⊔ B, m T = m (T ⊓ A) * m (T ⊓ B)

/-- **A partition's block product, restricted to a sub-lattice-element `b`, equals the product
of `m (C ⊓ b)` over all of `π`'s original blocks.** General fact about `Finpartition.restrict`,
independent of `IsIndependentAcross`: blocks `C` with `C ⊓ b = ⊥` don't appear in
`(π.restrict hb).parts` at all, and contribute `m ⊥ = 1` (a no-op factor) on the other side; among
the blocks with `C ⊓ b ≠ ⊥`, `C ↦ C ⊓ b` is injective (distinct blocks of `π` are disjoint, so
their intersections with `b` are too, hence distinct when both nonempty) and its image is exactly
`(π.restrict hb).parts` (`Finpartition.mem_restrict_iff`). -/
theorem partitionProduct_restrict_eq_prod_inf {S : Finset α} (π : Finpartition S) {b : Finset α}
    (hb : b ≤ S) {m : Finset α → ℂ} (hm0 : m ⊥ = 1) :
    partitionProduct m (π.restrict hb) = ∏ C ∈ π.parts, m (C ⊓ b) := by
  classical
  have hinj : Set.InjOn (fun C => C ⊓ b)
      (π.parts.filter (fun C => C ⊓ b ≠ ⊥) : Finset (Finset α)) := by
    intro C1 hC1 C2 hC2 heq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hC1 hC2
    have heq' : C1 ⊓ b = C2 ⊓ b := heq
    have hle : C1 ⊓ b ≤ C2 := by rw [heq']; exact inf_le_left
    exact eq_of_inf_ne_bot hC1.1 hC2.1 inf_le_left hle hC1.2
  have himg : (π.parts.filter (fun C => C ⊓ b ≠ ⊥)).image (fun C => C ⊓ b) =
      (π.restrict hb).parts := by
    ext d
    rw [Finset.mem_image, mem_restrict_iff]
    constructor
    · rintro ⟨C, hC, rfl⟩
      rw [Finset.mem_filter] at hC
      exact ⟨hC.2, C, hC.1, rfl⟩
    · rintro ⟨hd0, C, hC, rfl⟩
      exact ⟨C, Finset.mem_filter.2 ⟨hC, hd0⟩, rfl⟩
  rw [partitionProduct, ← himg, Finset.prod_image hinj,
    ← Finset.prod_filter_mul_prod_filter_not π.parts (fun C => C ⊓ b ≠ ⊥) (fun C => m (C ⊓ b))]
  have h2 : (∏ C ∈ π.parts.filter (fun C => ¬C ⊓ b ≠ ⊥), m (C ⊓ b)) = 1 := by
    apply Finset.prod_eq_one
    intro C hC
    rw [Finset.mem_filter, not_not] at hC
    rw [hC.2, hm0]
  rw [h2, mul_one]

/-- **Independent factorization at the level of a single partition's block product.** If `m`
factors independently across `(A, B)`, then for any partition `π` of `A ⊔ B`, the product of `m`
over `π`'s blocks factors as the product of `m` over `π`'s restriction to `A` times the product
of `m` over `π`'s restriction to `B`. -/
theorem partitionProduct_eq_mul_of_isIndependentAcross {m : Finset α → ℂ} {A B : Finset α}
    (hind : IsIndependentAcross m A B) (π : Finpartition (A ⊔ B)) :
    partitionProduct m π = partitionProduct m (π.restrict le_sup_left) *
      partitionProduct m (π.restrict le_sup_right) := by
  obtain ⟨-, hm0, hfact⟩ := hind
  rw [partitionProduct_restrict_eq_prod_inf π le_sup_left hm0,
    partitionProduct_restrict_eq_prod_inf π le_sup_right hm0, ← Finset.prod_mul_distrib,
    partitionProduct]
  exact Finset.prod_congr rfl fun C hC => hfact C (π.le hC)

end Finpartition
