import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import LeanCondensedMatter.Combinatorics.IncidenceAlgebraMu

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

open IncidenceAlgebra

variable {α : Type*} [DecidableEq α] {s : Finset α}

/-- The partition lattice `Finpartition s` is locally finite: it is already a `Fintype`
(Mathlib), and its `≤` (refinement) is decidable, so every interval is a finite set. This is
the adapter needed to apply Mathlib's `IncidenceAlgebra` (Möbius function, Möbius inversion) to
the partition lattice. -/
noncomputable instance instLocallyFiniteOrder : LocallyFiniteOrder (Finpartition s) := by
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
`Q B hB` exactly. A part of `σ.bind Q` only intersects nontrivially with the `σ`-part it came
from, by `eq_of_inf_ne_bot`. -/
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

/-- **`restrict` is monotone**: refining `P` to `P'` also refines each of their restrictions to a
common `b ≤ a`. Needed to show `refinementsEquivFiberPartitions` is an order isomorphism, not
just a bijection. -/
theorem restrict_mono {P P' : Finpartition a} (h : P ≤ P') {b : Finset α} (hb : b ≤ a) :
    P.restrict hb ≤ P'.restrict hb := by
  intro d hd
  rw [mem_restrict_iff] at hd
  obtain ⟨hd0, A, hA, rfl⟩ := hd
  obtain ⟨C, hC, hAC⟩ := h hA
  refine ⟨C ⊓ b, ?_, inf_le_inf_right b hAC⟩
  rw [mem_restrict_iff]
  exact ⟨ne_bot_of_le_ne_bot hd0 (inf_le_inf_right b hAC), C, hC, rfl⟩

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

/-- **`refinementsEquivFiberPartitions` as an order isomorphism.** The subtype order on
`{π // π ≤ σ}` (inherited from refinement on `Finpartition a`) corresponds to the pointwise order
on `∀ B, Finpartition B` under the bijection: `≥` (`restrict_mono`) is immediate, and `≤` follows
by testing membership of a part `A` of `π` at the `σ`-part `B` containing it (via `π.2 : π ≤ σ`),
transporting the pointwise hypothesis there. This is the structure needed to factor the
partition lattice's Möbius function as a product over `σ`'s parts. -/
def refinementsOrderIsoFiberPartitions (σ : Finpartition a) :
    {π : Finpartition a // π ≤ σ} ≃o (∀ B : σ.parts, Finpartition (B : Finset α)) where
  toEquiv := refinementsEquivFiberPartitions σ
  map_rel_iff' := by
    intro π π'
    refine ⟨fun h A hA => ?_, fun h B => restrict_mono h (σ.le B.2)⟩
    obtain ⟨B, hB, hAB⟩ := π.2 hA
    have hAmem : A ∈ (π.1.restrict (σ.le hB)).parts := by
      rw [mem_restrict_iff]
      exact ⟨π.1.ne_bot hA, A, hA, inf_eq_left.2 hAB⟩
    obtain ⟨D, hD, hAD⟩ := h ⟨B, hB⟩ hAmem
    have hD' : D ∈ (π'.1.restrict (σ.le hB)).parts := hD
    rw [mem_restrict_iff] at hD'
    obtain ⟨-, C, hC, rfl⟩ := hD'
    exact ⟨C, hC, hAD.trans inf_le_left⟩

/-- **A partition restricted to one of its own parts is the indiscrete (single-part) partition
of that part.** `σ.restrict (σ.le hB) = ⊤` for `B ∈ σ.parts`: both sides have `parts = {B}` —
`σ`'s restriction because every other part of `σ` is disjoint from `B` (so intersects it to
`⊥`, discarded), and `⊤` by `Finpartition.parts_top_subset`/`parts_nonempty_iff`. The final piece
needed to identify `refinementsOrderIsoFiberPartitions σ ⟨σ, le_rfl⟩` (the top refinement of
`σ`, itself) with the all-`⊤` element under the fiber-partition correspondence. -/
theorem restrict_self_part_eq_top (σ : Finpartition a) {B : Finset α} (hB : B ∈ σ.parts) :
    σ.restrict (σ.le hB) = (⊤ : Finpartition B) := by
  classical
  have hparts : (σ.restrict (σ.le hB)).parts = {B} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨mem_restrict_iff.2 ⟨σ.ne_bot hB, B, hB, inf_idem B⟩, fun d hd => ?_⟩
    rw [mem_restrict_iff] at hd
    obtain ⟨hd0, C, hC, rfl⟩ := hd
    by_contra hne
    exact hd0 (bot_unique (σ.disjoint hC hB (fun h => hne (h ▸ inf_idem B))).le_bot)
  have htop : (⊤ : Finpartition B).parts = {B} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    refine ⟨?_, fun d hd => Finset.mem_singleton.1 (Finpartition.parts_top_subset B hd)⟩
    obtain ⟨x, hx⟩ := (Finpartition.parts_nonempty_iff (P := (⊤ : Finpartition B))).2
      (σ.ne_bot hB)
    rwa [Finset.mem_singleton.1 (Finpartition.parts_top_subset B hx)] at hx
  exact Finpartition.ext (hparts.trans htop.symm)

/-- **The Möbius function of the partition lattice factors as a product over the parts of a
coarser partition.** For `π ≤ σ`, `mu ℤ π σ = ∏ B ∈ σ.parts, mu ℤ (π|_B) ⊤`, where `π|_B` is
`π` restricted to `B` and `⊤` is `B`'s indiscrete partition. Combines
`refinementsOrderIsoFiberPartitions` with the general facts in `IncidenceAlgebraMu.lean`:
`mu_subtype_le_apply` moves the computation into the down-set `{τ // τ ≤ σ}`,
`mu_orderIso_apply` transports it across `refinementsOrderIsoFiberPartitions`, `mu_pi_finset_apply`
splits the resulting product-type Möbius function into a product over `σ.parts`, and
`restrict_self_part_eq_top` identifies `σ`'s own image (`refinementsOrderIsoFiberPartitions σ`
applied to the top element `⟨σ, le_rfl⟩`) with the all-`⊤` element. This is the moment-cumulant
formula's structural core; the explicit factorial formula for each `mu ℤ (π|_B) ⊤` is not proved
here — see `notes/roadmaps/combinatorics.md`. -/
theorem mu_eq_prod_restrict {π σ : Finpartition a} (h : π ≤ σ) :
    mu ℤ π σ = ∏ B : σ.parts, mu ℤ (π.restrict (σ.le B.2)) (⊤ : Finpartition (B : Finset α)) := by
  classical
  have hstep1 : mu ℤ π σ = mu ℤ (⟨π, h⟩ : {τ : Finpartition a // τ ≤ σ}) ⟨σ, le_refl σ⟩ :=
    (mu_subtype_le_apply (⟨π, h⟩ : {τ : Finpartition a // τ ≤ σ}) ⟨σ, le_refl σ⟩).symm
  have hstep2 : mu ℤ (⟨π, h⟩ : {τ : Finpartition a // τ ≤ σ}) ⟨σ, le_refl σ⟩ =
      mu ℤ (refinementsOrderIsoFiberPartitions σ ⟨π, h⟩)
        (refinementsOrderIsoFiberPartitions σ ⟨σ, le_refl σ⟩) :=
    (mu_orderIso_apply _ _ _).symm
  have hstep3 := mu_pi_finset_apply (fun B : Finset α => Finpartition B) σ.parts
    (refinementsOrderIsoFiberPartitions σ ⟨π, h⟩)
    (refinementsOrderIsoFiberPartitions σ ⟨σ, le_refl σ⟩)
  rw [hstep1, hstep2, hstep3]
  refine Finset.prod_congr rfl fun B _ => ?_
  change mu ℤ (π.restrict (σ.le B.2)) (σ.restrict (σ.le B.2)) = mu ℤ (π.restrict (σ.le B.2)) ⊤
  rw [restrict_self_part_eq_top σ B.2]

/-- **`ℂ`-coefficient version of `mu_eq_prod_restrict`**, obtained by casting rather than
reproving: `IncidenceAlgebraMu.mu_intCast_eq_complex` shows `mu ℤ`'s value agrees with `mu ℂ`'s
after casting, since `mu`'s recursive definition only uses `+`, `-`, `1`. Needed so
`MomentCumulant.lean` (which fixes coefficients to `ℂ`, matching the Fock-space side of the
project) can reuse this block-factorization fact directly. -/
theorem mu_eq_prod_restrict_complex {π σ : Finpartition a} (h : π ≤ σ) :
    mu ℂ π σ = ∏ B : σ.parts, mu ℂ (π.restrict (σ.le B.2)) (⊤ : Finpartition (B : Finset α)) := by
  rw [← mu_intCast_eq_complex, mu_eq_prod_restrict h]
  push_cast
  exact Finset.prod_congr rfl fun B _ => mu_intCast_eq_complex _ _

end Finpartition
