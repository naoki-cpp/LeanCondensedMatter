import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Pi.Interval

set_option linter.style.header false

/-!
# Structural properties of the incidence-algebra Möbius function

The Möbius function is invariant under order isomorphism, agrees with the ambient order when
computed in a finite principal interval, and is multiplicative over finite dependent products. The
coefficient ring is an arbitrary commutative ring; no partition-lattice or complex-number
specialization is built into this module.
-/

open Finset

namespace IncidenceAlgebra

private theorem eq_mu_of_mul_zeta_eq_one {R α : Type*} [Ring R]
    [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]
    (f : IncidenceAlgebra R α) (hleft : f * zeta R = 1) :
    f = mu R := by
  exact left_inv_eq_right_inv hleft (zeta_mul_mu (𝕜 := R) (α := α))

/-- The Möbius function is invariant under an order isomorphism. -/
theorem mu_orderIso_apply {R α β : Type*} [CommRing R]
    [PartialOrder α] [PartialOrder β]
    [LocallyFiniteOrder α] [LocallyFiniteOrder β] [DecidableEq α] [DecidableEq β]
    (e : α ≃o β) (x y : α) :
    mu R (e x) (e y) = mu R x y := by
  classical
  letI : DecidableLE α := Classical.decRel _
  letI : DecidableLE β := Classical.decRel _
  let pulledMu : IncidenceAlgebra R α :=
    { toFun := fun a b => mu R (e a) (e b)
      eq_zero_of_not_le' := by
        intro a b hab
        exact (mu R : IncidenceAlgebra R β).eq_zero_of_not_le'
          (fun h => hab (e.le_iff_le.mp h)) }
  have hleft : pulledMu * zeta R = 1 := by
    ext a b
    have hsum :
        (∑ t ∈ Finset.Icc a b, mu R (e a) (e t)) =
          ∑ u ∈ Finset.Icc (e a) (e b), mu R (e a) u := by
      refine Finset.sum_bij' (fun t _ => e t) (fun u _ => e.symm u) ?_ ?_ ?_ ?_ ?_
      · intro t ht
        exact Finset.mem_Icc.2 ⟨
          e.le_iff_le.2 (Finset.mem_Icc.1 ht).1,
          e.le_iff_le.2 (Finset.mem_Icc.1 ht).2⟩
      · intro u hu
        exact Finset.mem_Icc.2 ⟨
          e.le_iff_le.mp (by simpa using (Finset.mem_Icc.1 hu).1),
          e.le_iff_le.mp (by simpa using (Finset.mem_Icc.1 hu).2)⟩
      · intro t _
        simp
      · intro u _
        simp
      · intro t _
        simp
    calc
      (pulledMu * (zeta R : IncidenceAlgebra R α)) a b =
          ∑ t ∈ Finset.Icc a b, mu R (e a) (e t) := by
        rw [mul_apply]
        apply Finset.sum_congr rfl
        intro t ht
        rw [zeta_of_le (Finset.mem_Icc.1 ht).2, mul_one]
        rfl
      _ = ∑ u ∈ Finset.Icc (e a) (e b), mu R (e a) u := hsum
      _ = (1 : IncidenceAlgebra R β) (e a) (e b) := sum_Icc_mu_right ..
      _ = (1 : IncidenceAlgebra R α) a b := by
        by_cases h : a = b
        · subst b
          simp
        · have he : e a ≠ e b := fun he => h (e.injective he)
          simp [one_apply, h, he]
  have hpulled : pulledMu = mu R :=
    eq_mu_of_mul_zeta_eq_one pulledMu hleft
  have h := congrArg (fun f : IncidenceAlgebra R α => f x y) hpulled
  simpa [pulledMu] using h

/-- Ring homomorphisms preserve the Möbius function. -/
theorem map_mu_apply {R S α : Type*} [Ring R] [Ring S]
    [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
    (φ : R →+* S) (x y : α) :
    φ (mu R x y) = mu S x y := by
  classical
  letI : DecidableLE α := Classical.decRel _
  let mappedMu : IncidenceAlgebra S α :=
    { toFun := fun a b => φ (mu R a b)
      eq_zero_of_not_le' := by
        intro a b hab
        have hmu : mu R a b = 0 :=
          apply_eq_zero_of_not_le hab (mu R : IncidenceAlgebra R α)
        simp [hmu] }
  have hleft : mappedMu * zeta S = 1 := by
    ext a b
    calc
      (mappedMu * (zeta S : IncidenceAlgebra S α)) a b =
          ∑ t ∈ Finset.Icc a b, φ (mu R a t) := by
        rw [mul_apply]
        apply Finset.sum_congr rfl
        intro t ht
        rw [zeta_of_le (Finset.mem_Icc.1 ht).2, mul_one]
        rfl
      _ = φ (∑ t ∈ Finset.Icc a b, mu R a t) := by rw [map_sum]
      _ = (1 : IncidenceAlgebra S α) a b := by
        rw [sum_Icc_mu_right]
        by_cases h : a = b
        · subst b
          simp
        · simp [one_apply, h]
  have hmapped : mappedMu = mu S :=
    eq_mu_of_mul_zeta_eq_one mappedMu hleft
  have h := congrArg (fun f : IncidenceAlgebra S α => f x y) hmapped
  simpa [mappedMu] using h

/-- Restricting the ambient Möbius function to an order-convex subtype gives the subtype Möbius
function. The proof uses uniqueness of the inverse of `zeta`, rather than repeating the recursive
construction of `mu` inside the subtype. -/
private theorem mu_subtype_apply_of_interval_closed {R α : Type*} [CommRing R]
    [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]
    {p : α → Prop} [LocallyFiniteOrder {t : α // p t}]
    (hclosed : ∀ {a b : {t : α // p t}} {t : α}, a.1 ≤ t → t ≤ b.1 → p t)
    (x y : {t : α // p t}) :
    mu R x y = mu R x.1 y.1 := by
  classical
  letI : DecidableLE {t : α // p t} := Classical.decRel _
  let restrictedMu : IncidenceAlgebra R {t : α // p t} :=
    { toFun := fun a b => (mu R : IncidenceAlgebra R α) a.1 b.1
      eq_zero_of_not_le' := by
        intro a b hab
        exact (mu R : IncidenceAlgebra R α).eq_zero_of_not_le'
          (fun h => hab (Subtype.coe_le_coe.2 h)) }
  have hleft : restrictedMu * zeta R = 1 := by
    ext a b hab
    have hsum :
        (∑ w ∈ Finset.Icc a b, mu R a.1 w.1) =
          ∑ t ∈ Finset.Icc a.1 b.1, mu R a.1 t := by
      have hIcc : ∀ w : {t : α // p t},
          w ∈ Finset.Icc a b ↔ w.1 ∈ Finset.Icc a.1 b.1 := by
        intro w
        simp only [Finset.mem_Icc, Subtype.coe_le_coe]
      refine Finset.sum_bij' (fun w _ => w.1)
        (fun t ht => (⟨t, hclosed (Finset.mem_Icc.1 ht).1 (Finset.mem_Icc.1 ht).2⟩ :
          {t : α // p t})) ?_ ?_ ?_ ?_ ?_
      · intro w hw
        exact (hIcc w).1 hw
      · intro t ht
        exact (hIcc _).2 (by simpa using ht)
      · intro w _
        rfl
      · intro t _
        rfl
      · intro w _
        rfl
    calc
      (restrictedMu * (zeta R : IncidenceAlgebra R {t : α // p t})) a b =
          ∑ w ∈ Finset.Icc a b, mu R a.1 w.1 := by
        rw [mul_apply]
        apply Finset.sum_congr rfl
        intro w hw
        rw [zeta_of_le (Finset.mem_Icc.1 hw).2, mul_one]
        rfl
      _ = ∑ t ∈ Finset.Icc a.1 b.1, mu R a.1 t := hsum
      _ = (1 : IncidenceAlgebra R α) a.1 b.1 := sum_Icc_mu_right ..
      _ = (1 : IncidenceAlgebra R {t : α // p t}) a b := by
        by_cases h : a = b
        · subst b
          simp
        · have hv : a.1 ≠ b.1 := fun hv => h (Subtype.ext hv)
          simp [one_apply, h, hv]
  have hrestricted : restrictedMu = mu R :=
    eq_mu_of_mul_zeta_eq_one restrictedMu hleft
  have h := congrArg
    (fun f : IncidenceAlgebra R {t : α // p t} => f x y) hrestricted
  simpa [restrictedMu] using h.symm

/-- A finite principal lower interval inherits a locally finite order. -/
noncomputable instance instLocallyFiniteOrderSubtypeLe {α : Type*} [Fintype α]
    [PartialOrder α] {z : α} : LocallyFiniteOrder {t : α // t ≤ z} := by
  classical
  exact Fintype.toLocallyFiniteOrder

/-- The Möbius function computed in a finite principal lower interval agrees with the ambient
Möbius function. -/
theorem mu_subtype_le_apply {R α : Type*} [CommRing R]
    [Fintype α] [PartialOrder α] [LocallyFiniteOrder α]
    [DecidableEq α] {z : α} (x y : {t : α // t ≤ z}) :
    mu R x y = mu R x.1 y.1 :=
  mu_subtype_apply_of_interval_closed (fun {_a b _t} _ htb => htb.trans b.2) x y

/-- A finite principal upper interval inherits a locally finite order. -/
noncomputable instance instLocallyFiniteOrderSubtypeGe {α : Type*} [Fintype α]
    [PartialOrder α] {z : α} : LocallyFiniteOrder {t : α // z ≤ t} := by
  classical
  exact Fintype.toLocallyFiniteOrder

/-- The Möbius function computed in a finite principal upper interval agrees with the ambient
Möbius function. -/
theorem mu_subtype_ge_apply {R α : Type*} [CommRing R]
    [Fintype α] [PartialOrder α] [LocallyFiniteOrder α]
    [DecidableEq α] {z : α} (x y : {t : α // z ≤ t}) :
    mu R x y = mu R x.1 y.1 :=
  mu_subtype_apply_of_interval_closed (fun {a _b _t} hat _ => a.2.trans hat) x y

end IncidenceAlgebra

/-- Split a finite dependent product at one distinguished index. -/
noncomputable def piInsertOrderIso {ι : Type*} [DecidableEq ι] (β : ι → Type*)
    [∀ i, Preorder (β i)] {j : ι} {s : Finset ι} (hjs : j ∉ s) :
    (∀ i : (insert j s : Finset ι), β i) ≃o β j × ∀ i : s, β i := by
  rw [Finset.insert_eq]
  let hdis : Disjoint ({j} : Finset ι) s := Finset.disjoint_singleton_left.mpr hjs
  let e : (∀ i : ({j} ∪ s : Finset ι), β i) ≃ β j × ∀ i : s, β i :=
    (Equiv.piFinsetUnion β hdis).symm.trans <|
      Equiv.prodCongr (Equiv.piUnique fun i : ({j} : Finset ι) => β i) (Equiv.refl _)
  refine { toEquiv := e, map_rel_iff' := ?_ }
  intro f g
  change
    (f ⟨j, by simp⟩ ≤ g ⟨j, by simp⟩ ∧
      ∀ i : s, f ⟨i.1, by simp [i.2]⟩ ≤ g ⟨i.1, by simp [i.2]⟩) ↔
      ∀ i, f i ≤ g i
  constructor
  · rintro ⟨h1, h2⟩ ⟨i, hi⟩
    simp only [Finset.mem_union, Finset.mem_singleton] at hi
    rcases hi with rfl | hi
    · exact h1
    · exact h2 ⟨i, hi⟩
  · intro h
    exact ⟨h _, fun i => h _⟩

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
      (show (piInsertOrderIso β hjs x).1 = x ⟨j, mem_insert_self j s⟩ from rfl),
      (show (piInsertOrderIso β hjs y).1 = y ⟨j, mem_insert_self j s⟩ from rfl),
      (show (piInsertOrderIso β hjs x).2 = fun i : s => x ⟨i.1, mem_insert_of_mem i.2⟩ from rfl),
      (show (piInsertOrderIso β hjs y).2 = fun i : s => y ⟨i.1, mem_insert_of_mem i.2⟩ from rfl)]
      at hmu
    rw [hmu,
      ih (fun i => x ⟨i.1, mem_insert_of_mem i.2⟩)
        (fun i => y ⟨i.1, mem_insert_of_mem i.2⟩),
      prod_subtype_insert_eq hjs (fun i => mu R (x i) (y i))]

end IncidenceAlgebra