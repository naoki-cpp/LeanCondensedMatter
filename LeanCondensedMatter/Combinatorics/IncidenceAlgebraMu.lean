import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Pi.Interval

-- No project files currently carry a Mathlib-style copyright/author header; a
-- project-wide policy for this is a separate open item (see notes/conventions.md).
set_option linter.style.header false

/-!
# The Möbius function is invariant under order isomorphism, and multiplicative over finite products

General facts about `IncidenceAlgebra.mu` (fixed to coefficient ring `ℤ`) needed to factor the
partition lattice's Möbius function as a product over the parts of a coarser partition
(`PartitionLattice.lean`), stated here independently of `Finpartition` since they have no
partition-specific content:

- `mu_orderIso_apply`: `mu` is preserved by any order isomorphism.
- `mu_subtype_le_apply`: `mu` computed inside the down-set `{t // t ≤ z}` agrees with `mu`
  computed in the ambient order.
- `mu_pi_finset_apply`: `mu` on a finite dependent product `∀ i : t, β i` (`t : Finset ι`) is the
  product of the `mu`'s of each factor.

**Coefficients fixed to `ℤ`.** `IncidenceAlgebra.mu` is defined for any `[AddCommGroup 𝕜] [One
𝕜]`; the proofs below generalize immediately (they never use more than `ℤ`'s structure), but are
stated for `ℤ` since that's all the partition-lattice application needs — see `notes/roadmap.md`.
-/

open Finset IncidenceAlgebra

/-- **The Möbius function is invariant under order isomorphism.** `mu 𝕜 (e x) (e y) = mu 𝕜 x y`
for any order isomorphism `e`. Proved by strong induction on `(Icc x y).card`, mirroring `mu`'s
own recursive definition (`mu_eq_neg_sum_Ico_of_ne`): an order isomorphism carries `Ico x y`
bijectively onto `Ico (e x) (e y)`, so the recursion transports term by term. -/
theorem mu_orderIso_apply {α β : Type*} [PartialOrder α] [PartialOrder β]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β]
    (e : α ≃o β) (x y : α) :
    mu ℤ (e x) (e y) = mu ℤ x y := by
  induction hn : (Finset.Icc x y).card using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    subst hn
    by_cases hxy : x = y
    · subst hxy; simp
    have hexy : e x ≠ e y := fun h => hxy (e.injective h)
    have himg : Finset.Ico (e x) (e y) = (Finset.Ico x y).image e := by
      ext w
      simp only [Finset.mem_image, Finset.mem_Ico]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨e.symm w, ⟨?_, ?_⟩, e.apply_symm_apply w⟩
        · rwa [← e.le_iff_le, e.apply_symm_apply]
        · rwa [← e.lt_iff_lt, e.apply_symm_apply]
      · rintro ⟨z, ⟨h1, h2⟩, rfl⟩
        exact ⟨e.le_iff_le.2 h1, e.lt_iff_lt.2 h2⟩
    rw [mu_eq_neg_sum_Ico_of_ne hexy, mu_eq_neg_sum_Ico_of_ne hxy, himg,
      Finset.sum_image (fun z1 _ z2 _ h => e.injective h)]
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.mem_Ico] at hz
    have hcard : (Finset.Icc x z).card < (Finset.Icc x y).card :=
      Finset.card_lt_card (Finset.Icc_ssubset_Icc_right (hz.1.trans hz.2.le) le_rfl hz.2)
    exact ih _ hcard x z rfl

/-- `LocallyFiniteOrder` on the down-set `{t // t ≤ z}` of a `Fintype`. Needed so
`mu_subtype_le_apply`'s statement (Möbius function *inside* the down-set) even typechecks.
Requires `[Fintype α]`, matching this file's intended use (`α := Finpartition a`, already a
`Fintype`) rather than a general `LocallyFiniteOrderBot`. -/
noncomputable instance instLocallyFiniteOrderSubtypeLe {α : Type*} [Fintype α] [PartialOrder α]
    [LocallyFiniteOrder α] [DecidableEq α] {z : α} : LocallyFiniteOrder {t : α // t ≤ z} := by
  classical
  exact Fintype.toLocallyFiniteOrder

/-- **The Möbius function computed inside a down-set agrees with the ambient Möbius function.**
For `x y : {t // t ≤ z}`, `mu ℤ x y = mu ℤ x.1 y.1`. Proved by strong induction on
`(Icc x.1 y.1).card`, mirroring `mu_orderIso_apply`: every `w` with `x ≤ w < y` in `α` already
satisfies `w ≤ z` (via `y.2` and transitivity), so `Ico x y` (in the subtype) bijects with
`Ico x.1 y.1` (in `α`) via the coercion. -/
theorem mu_subtype_le_apply {α : Type*} [Fintype α] [PartialOrder α] [LocallyFiniteOrder α]
    [DecidableEq α] {z : α} (x y : {t : α // t ≤ z}) :
    mu ℤ x y = mu ℤ x.1 y.1 := by
  induction hn : (Finset.Icc x.1 y.1).card using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    subst hn
    by_cases hxy : x = y
    · subst hxy; simp
    have hxy1 : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hIco : ∀ w : {t : α // t ≤ z}, w ∈ Finset.Ico x y ↔ w.1 ∈ Finset.Ico x.1 y.1 := by
      intro w
      simp only [Finset.mem_Ico, Subtype.coe_lt_coe, Subtype.coe_le_coe]
    have hsum : ∑ w ∈ Finset.Ico x y, mu ℤ x w = ∑ t ∈ Finset.Ico x.1 y.1, mu ℤ x.1 t := by
      refine Finset.sum_bij' (fun w _ => w.1)
        (fun t ht => (⟨t, (Finset.mem_Ico.1 ht).2.le.trans y.2⟩ : {t : α // t ≤ z}))
        ?_ ?_ ?_ ?_ ?_
      · intro w hw; exact (hIco w).1 hw
      · intro t ht; exact (hIco _).2 (by simpa using ht)
      · intro w _; rfl
      · intro t _; rfl
      · intro w hw
        have hw' : w ∈ Finset.Ico x y := hw
        rw [Finset.mem_Ico] at hw'
        have hcard : (Finset.Icc x.1 w.1).card < (Finset.Icc x.1 y.1).card :=
          Finset.card_lt_card (Finset.Icc_ssubset_Icc_right
            ((Subtype.coe_le_coe.2 hw'.1).trans (Subtype.coe_lt_coe.2 hw'.2).le) le_rfl
            (Subtype.coe_lt_coe.2 hw'.2))
        exact ih _ hcard x w rfl
    rw [mu_eq_neg_sum_Ico_of_ne hxy, mu_eq_neg_sum_Ico_of_ne hxy1, hsum]

/-- **Splitting a dependent product Möbius function at one index, as an order isomorphism.**
`∀ i : insert j s, β i ≃o β j × ∀ i : s, β i`, for `j ∉ s`. The order-theoretic analogue of
`Equiv.piSplitAt` restricted to a `Finset`, used (via `mu_orderIso_apply`) to induct
`mu_pi_finset_apply` one index at a time. -/
noncomputable def piInsertOrderIso {ι : Type*} [DecidableEq ι] (β : ι → Type*)
    [∀ i, Preorder (β i)] {j : ι} {s : Finset ι} (hjs : j ∉ s) :
    (∀ i : (insert j s : Finset ι), β i) ≃o β j × ∀ i : s, β i where
  toFun f := (f ⟨j, mem_insert_self j s⟩, fun i => f ⟨i.1, mem_insert_of_mem i.2⟩)
  invFun p i := if h : i.1 = j then cast (congrArg β h.symm) p.1
      else p.2 ⟨i.1, (mem_insert.1 i.2).resolve_left h⟩
  left_inv f := by
    funext i
    obtain ⟨i1, hi2⟩ := i
    by_cases h : i1 = j
    · subst h; simp
    · simp [h]
  right_inv p := by
    ext x
    · simp
    · obtain ⟨i1, hi2⟩ := x
      have h : i1 ≠ j := fun he => hjs (he ▸ hi2)
      simp [h]
  map_rel_iff' := by
    intro f g
    simp only [Prod.le_def]
    constructor
    · rintro ⟨h1, h2⟩ i
      obtain ⟨i1, hi2⟩ := i
      by_cases hij : i1 = j
      · subst hij; exact h1
      · exact h2 ⟨i1, (mem_insert.1 hi2).resolve_left hij⟩
    · intro h
      exact ⟨h ⟨j, mem_insert_self j s⟩, fun i => h ⟨i.1, mem_insert_of_mem i.2⟩⟩

/-- **A finite dependent product `∀ i : insert j s, β i`, reindexed via `Subtype.val`, splits
its product over `j` and `s`.** The `Finset`-level bookkeeping (`Finset.attach_insert`,
`Finset.prod_insert`, `Finset.prod_image`) needed to turn `piInsertOrderIso`'s index split into a
`Finset.prod` recursion in `mu_pi_finset_apply`. -/
theorem prod_subtype_insert_eq {ι M : Type*} [DecidableEq ι] [CommMonoid M] {j : ι} {s : Finset ι}
    (hjs : j ∉ s) (g : ∀ _i : ↥(insert j s), M) :
    ∏ i : ↥(insert j s), g i =
      g ⟨j, mem_insert_self j s⟩ * ∏ i : s, g ⟨i.1, mem_insert_of_mem i.2⟩ := by
  rw [Finset.prod_coe_sort_eq_attach, Finset.attach_insert,
    Finset.prod_insert (by simp [hjs]),
    Finset.prod_image (fun a _ b _ h => Subtype.ext (by simpa using congrArg Subtype.val h)),
    Finset.prod_coe_sort_eq_attach]

/-- **The Möbius function of a finite dependent product is the product of the Möbius functions
of its factors.** `mu ℤ x y = ∏ i : t, mu ℤ (x i) (y i)`, for `x y : ∀ i : t, β i` (`t : Finset
ι`). Proved by induction on `t` (`Finset.induction_on`): the empty case is trivial (`mu` of a
`Subsingleton` type is `1`), and the `insert j s` case combines `piInsertOrderIso` (via
`mu_orderIso_apply`) with `IncidenceAlgebra.mu_prod_mu` (Mathlib) to split off `j`'s factor, then
the induction hypothesis and `prod_subtype_insert_eq` reassemble the product. -/
theorem mu_pi_finset_apply {ι : Type*} [DecidableEq ι] (β : ι → Type*) [∀ i, PartialOrder (β i)]
    [∀ i, LocallyFiniteOrder (β i)] [∀ i, DecidableEq (β i)] (t : Finset ι) (x y : ∀ i : t, β i) :
    mu ℤ x y = ∏ i : t, mu ℤ (x i) (y i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have hxy : x = y := Subsingleton.elim x y
    subst hxy; simp
  | @insert j s hjs ih =>
    have hmu := (mu_orderIso_apply (piInsertOrderIso β hjs) x y).symm
    rw [← mu_prod_mu, IncidenceAlgebra.prod_apply,
      show (piInsertOrderIso β hjs x).1 = x ⟨j, mem_insert_self j s⟩ from rfl,
      show (piInsertOrderIso β hjs y).1 = y ⟨j, mem_insert_self j s⟩ from rfl,
      show (piInsertOrderIso β hjs x).2 = fun i : s => x ⟨i.1, mem_insert_of_mem i.2⟩ from rfl,
      show (piInsertOrderIso β hjs y).2 = fun i : s => y ⟨i.1, mem_insert_of_mem i.2⟩ from rfl]
      at hmu
    rw [hmu, ih (fun i => x ⟨i.1, mem_insert_of_mem i.2⟩) (fun i => y ⟨i.1, mem_insert_of_mem i.2⟩),
      prod_subtype_insert_eq hjs (fun i => mu ℤ (x i) (y i))]
