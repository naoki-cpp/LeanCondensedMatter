import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Pi.Interval

set_option linter.style.header false

/-!
# Structural properties of the incidence-algebra Möbius function

The Möbius function is invariant under order isomorphism, agrees with the ambient order when
computed in a finite down-set, and is multiplicative over finite dependent products. The
coefficient ring is an arbitrary commutative ring; no partition-lattice or complex-number
specialization is built into this module.
-/

open Finset

namespace IncidenceAlgebra

/-- The Möbius function is invariant under an order isomorphism. -/
theorem mu_orderIso_apply {R α β : Type*} [CommRing R]
    [PartialOrder α] [PartialOrder β]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β]
    (e : α ≃o β) (x y : α) :
    mu R (e x) (e y) = mu R x y := by
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

/-- A finite down-set inherits a locally finite order. -/
@[nolint unusedArguments]
noncomputable instance instLocallyFiniteOrderSubtypeLe {α : Type*} [Fintype α] [PartialOrder α]
    [LocallyFiniteOrder α] [DecidableEq α] {z : α} : LocallyFiniteOrder {t : α // t ≤ z} := by
  classical
  exact Fintype.toLocallyFiniteOrder

/-- The Möbius function computed in a finite down-set agrees with the ambient Möbius function. -/
theorem mu_subtype_le_apply {R α : Type*} [CommRing R]
    [Fintype α] [PartialOrder α] [LocallyFiniteOrder α]
    [DecidableEq α] {z : α} (x y : {t : α // t ≤ z}) :
    mu R x y = mu R x.1 y.1 := by
  induction hn : (Finset.Icc x.1 y.1).card using Nat.strong_induction_on generalizing x y with
  | _ n ih =>
    subst hn
    by_cases hxy : x = y
    · subst hxy; simp
    have hxy1 : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
    have hIco : ∀ w : {t : α // t ≤ z}, w ∈ Finset.Ico x y ↔ w.1 ∈ Finset.Ico x.1 y.1 := by
      intro w
      simp only [Finset.mem_Ico, Subtype.coe_lt_coe, Subtype.coe_le_coe]
    have hsum : ∑ w ∈ Finset.Ico x y, mu R x w = ∑ t ∈ Finset.Ico x.1 y.1, mu R x.1 t := by
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

end IncidenceAlgebra

/-- Split a finite dependent product at one distinguished index. -/
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

/-- Split a product over the subtype of an inserted finite set. -/
theorem prod_subtype_insert_eq {ι M : Type*} [DecidableEq ι] [CommMonoid M] {j : ι} {s : Finset ι}
    (hjs : j ∉ s) (g : ∀ _i : ↥(insert j s), M) :
    ∏ i : ↥(insert j s), g i =
      g ⟨j, mem_insert_self j s⟩ * ∏ i : s, g ⟨i.1, mem_insert_of_mem i.2⟩ := by
  rw [Finset.prod_coe_sort_eq_attach, Finset.attach_insert,
    Finset.prod_insert (by simp [hjs]),
    Finset.prod_image (fun a _ b _ h => Subtype.ext (by simpa using congrArg Subtype.val h)),
    Finset.prod_coe_sort_eq_attach]

namespace IncidenceAlgebra

/-- The Möbius function of a finite dependent product is the product of the factor Möbius
functions. -/
theorem mu_pi_finset_apply {R ι : Type*} [CommRing R] [DecidableEq ι]
    (β : ι → Type*) [∀ i, PartialOrder (β i)]
    [∀ i, LocallyFiniteOrder (β i)] [∀ i, DecidableEq (β i)]
    (t : Finset ι) (x y : ∀ i : t, β i) :
    mu R x y = ∏ i : t, mu R (x i) (y i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    have hxy : x = y := Subsingleton.elim x y
    subst hxy
    simp
  | @insert j s hjs ih =>
    have hmu := (mu_orderIso_apply (R := R) (piInsertOrderIso β hjs) x y).symm
    rw [← mu_prod_mu, IncidenceAlgebra.prod_apply,
      show (piInsertOrderIso β hjs x).1 = x ⟨j, mem_insert_self j s⟩ from rfl,
      show (piInsertOrderIso β hjs y).1 = y ⟨j, mem_insert_self j s⟩ from rfl,
      show (piInsertOrderIso β hjs x).2 = fun i : s => x ⟨i.1, mem_insert_of_mem i.2⟩ from rfl,
      show (piInsertOrderIso β hjs y).2 = fun i : s => y ⟨i.1, mem_insert_of_mem i.2⟩ from rfl]
      at hmu
    rw [hmu,
      ih (fun i => x ⟨i.1, mem_insert_of_mem i.2⟩)
        (fun i => y ⟨i.1, mem_insert_of_mem i.2⟩),
      prod_subtype_insert_eq hjs (fun i => mu R (x i) (y i))]

end IncidenceAlgebra
