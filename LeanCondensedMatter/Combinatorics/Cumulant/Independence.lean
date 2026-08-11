import LeanCondensedMatter.Combinatorics.Cumulant.Inversion
import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# Cumulants vanish across independent finite-set regions

If a complex-valued moment function factors across a disjoint pair of finite sets, every cumulant
that straddles both regions vanishes.
-/

open IncidenceAlgebra

variable {α : Type*} [DecidableEq α]

namespace Finpartition

/-- `m` factors independently across the disjoint pair `(A, B)`. -/
def IsIndependentAcross (m : Finset α → ℂ) (A B : Finset α) : Prop :=
  Disjoint A B ∧ m ⊥ = 1 ∧ ∀ T ≤ A ⊔ B, m T = m (T ⊓ A) * m (T ⊓ B)

/-- A restricted partition product is the product of the corresponding intersections. -/
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
    ← Finset.prod_filter_mul_prod_filter_not π.parts (fun C => C ⊓ b ≠ ⊥)
      (fun C => m (C ⊓ b))]
  have h2 : (∏ C ∈ π.parts.filter (fun C => ¬C ⊓ b ≠ ⊥), m (C ⊓ b)) = 1 := by
    apply Finset.prod_eq_one
    intro C hC
    rw [Finset.mem_filter, not_not] at hC
    rw [hC.2, hm0]
  rw [h2, mul_one]

/-- Partition products factor across independent regions. -/
theorem partitionProduct_eq_mul_of_isIndependentAcross {m : Finset α → ℂ} {A B : Finset α}
    (hind : IsIndependentAcross m A B) (π : Finpartition (A ⊔ B)) :
    partitionProduct m π = partitionProduct m (π.restrict le_sup_left) *
      partitionProduct m (π.restrict le_sup_right) := by
  obtain ⟨-, hm0, hfact⟩ := hind
  rw [partitionProduct_restrict_eq_prod_inf π le_sup_left hm0,
    partitionProduct_restrict_eq_prod_inf π le_sup_right hm0, ← Finset.prod_mul_distrib,
    partitionProduct]
  exact Finset.prod_congr rfl fun C hC => hfact C (π.le hC)

/-- Candidate cumulant that vanishes on sets straddling both regions. -/
noncomputable def splitCumulant (m : Finset α → ℂ) (A B T : Finset α) : ℂ :=
  if T ≤ A ∨ T ≤ B then cumulantFromMoment m T else 0

theorem momentFromCumulant_splitCumulant_of_le_left {m : Finset α → ℂ} {A B T : Finset α}
    (hT : T ≠ ⊥) (hTA : T ≤ A) : momentFromCumulant (splitCumulant m A B) T = m T := by
  have heq : ∀ π : Finpartition T,
      partitionProduct (splitCumulant m A B) π = partitionProduct (cumulantFromMoment m) π :=
    fun π => Finset.prod_congr rfl fun C hC => by
      simp [splitCumulant, (π.le hC).trans hTA]
  rw [momentFromCumulant]
  simp_rw [heq]
  exact momentFromCumulant_cumulantFromMoment m hT

theorem momentFromCumulant_splitCumulant_of_le_right {m : Finset α → ℂ} {A B T : Finset α}
    (hT : T ≠ ⊥) (hTB : T ≤ B) : momentFromCumulant (splitCumulant m A B) T = m T := by
  have heq : ∀ π : Finpartition T,
      partitionProduct (splitCumulant m A B) π = partitionProduct (cumulantFromMoment m) π :=
    fun π => Finset.prod_congr rfl fun C hC => by
      simp [splitCumulant, (π.le hC).trans hTB]
  rw [momentFromCumulant]
  simp_rw [heq]
  exact momentFromCumulant_cumulantFromMoment m hT

theorem momentFromCumulant_splitCumulant_eq {m : Finset α → ℂ} {A B : Finset α}
    (hind : IsIndependentAcross m A B) :
    ∀ T ≤ A ⊔ B, momentFromCumulant (splitCumulant m A B) T = m T := by
  classical
  obtain ⟨hAB, hm0, hfact⟩ := hind
  have hbase : momentFromCumulant (splitCumulant m A B) (⊥ : Finset α) = m ⊥ := by
    have htop_empty : (⊤ : Finpartition (⊥ : Finset α)).parts = ∅ :=
      Finset.eq_empty_iff_forall_notMem.2 fun C hC =>
        (⊤ : Finpartition (⊥ : Finset α)).ne_bot hC
          (le_bot_iff.1 ((⊤ : Finpartition (⊥ : Finset α)).le hC))
    have hall : ∀ π : Finpartition (⊥ : Finset α), π = ⊤ := fun π => Finpartition.ext
      ((Finset.eq_empty_iff_forall_notMem.2 fun C hC =>
          π.ne_bot hC (le_bot_iff.1 (π.le hC))).trans htop_empty.symm)
    rw [momentFromCumulant,
      Finset.sum_eq_single (⊤ : Finpartition (⊥ : Finset α))
        (fun π _ hne => absurd (hall π) hne) (fun h => absurd (Finset.mem_univ _) h)]
    rw [partitionProduct, htop_empty, Finset.prod_empty]
    exact hm0.symm
  intro T hT
  by_cases hTA : T ≤ A
  · rcases eq_or_ne T ⊥ with rfl | hT0
    · exact hbase
    · exact momentFromCumulant_splitCumulant_of_le_left hT0 hTA
  by_cases hTB : T ≤ B
  · rcases eq_or_ne T ⊥ with rfl | hT0
    · exact hbase
    · exact momentFromCumulant_splitCumulant_of_le_right hT0 hTB
  obtain ⟨x, hxT, hxA⟩ := Finset.not_subset.1 hTA
  have hxB : x ∈ B := (Finset.mem_union.1 (hT hxT)).resolve_left hxA
  have hTB' : T ⊓ B ≠ ⊥ := Finset.ne_empty_of_mem (Finset.mem_inter.2 ⟨hxT, hxB⟩)
  obtain ⟨y, hyT, hyB⟩ := Finset.not_subset.1 hTB
  have hyA : y ∈ A := (Finset.mem_union.1 (hT hyT)).resolve_right hyB
  have hTA' : T ⊓ A ≠ ⊥ := Finset.ne_empty_of_mem (Finset.mem_inter.2 ⟨hyT, hyA⟩)
  have hdisj : Disjoint (T ⊓ A) (T ⊓ B) := hAB.mono inf_le_right inf_le_right
  have hunion : T ⊓ A ⊔ T ⊓ B = T := by
    rw [← inf_sup_left]
    exact inf_eq_left.2 hT
  set σ₀ : Finpartition T := (Finpartition.indiscrete hTA').extend hTB' hdisj hunion with hσ₀_def
  have hσ₀parts : σ₀.parts = insert (T ⊓ B) {T ⊓ A} := rfl
  have hzero : ∀ π : Finpartition T, ¬π ≤ σ₀ → partitionProduct (splitCumulant m A B) π = 0 := by
    intro π hπ
    have hπ' : ¬∀ ⦃b : Finset α⦄, b ∈ π.parts → ∃ c ∈ σ₀.parts, b ≤ c := hπ
    push Not at hπ'
    obtain ⟨C, hC, hCnot⟩ := hπ'
    have hmemA : T ⊓ A ∈ σ₀.parts := by rw [hσ₀parts]; simp
    have hmemB : T ⊓ B ∈ σ₀.parts := by rw [hσ₀parts]; simp
    have hCnotA : ¬C ≤ A := fun h => hCnot (T ⊓ A) hmemA (le_inf (π.le hC) h)
    have hCnotB : ¬C ≤ B := fun h => hCnot (T ⊓ B) hmemB (le_inf (π.le hC) h)
    exact Finset.prod_eq_zero hC (by simp [splitCumulant, hCnotA, hCnotB])
  have hsum : momentFromCumulant (splitCumulant m A B) T =
      ∑ π ∈ Finset.Iic σ₀, partitionProduct (splitCumulant m A B) π := by
    rw [momentFromCumulant, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ≤ σ₀)]
    have hz : (∑ π ∈ Finset.univ.filter (fun π => ¬π ≤ σ₀),
        partitionProduct (splitCumulant m A B) π) = 0 :=
      Finset.sum_eq_zero fun π hπ => hzero π (Finset.mem_filter.1 hπ).2
    rw [hz, add_zero]
    congr 1
    ext π
    simp [Finset.mem_Iic]
  have hne : T ⊓ B ∉ ({T ⊓ A} : Finset (Finset α)) := by
    simp only [Finset.mem_singleton]
    intro h
    exact hTA' (disjoint_self.1 (h ▸ hdisj.symm))
  rw [hsum, sum_Iic_partitionProduct_eq (splitCumulant m A B) σ₀, partitionProduct, hσ₀parts,
    Finset.prod_insert hne, Finset.prod_singleton,
    momentFromCumulant_splitCumulant_of_le_right hTB' (inf_le_right : T ⊓ B ≤ B),
    momentFromCumulant_splitCumulant_of_le_left hTA' (inf_le_right : T ⊓ A ≤ A), mul_comm]
  exact (hfact T hT).symm

/-- The true cumulant agrees with `splitCumulant` on every nonempty subset of the two regions. -/
theorem cumulantFromMoment_eq_splitCumulant_of_le {m : Finset α → ℂ} {A B : Finset α}
    (hind : IsIndependentAcross m A B) {T : Finset α} (hT : T ≤ A ⊔ B) (hT0 : T ≠ ⊥) :
    cumulantFromMoment m T = splitCumulant m A B T := by
  have hkey : cumulantFromMoment m T =
      cumulantFromMoment (momentFromCumulant (splitCumulant m A B)) T := by
    simp only [cumulantFromMoment, partitionProduct]
    refine Finset.sum_congr rfl fun π _ => ?_
    congr 1
    exact Finset.prod_congr rfl fun C hC =>
      (momentFromCumulant_splitCumulant_eq hind C ((π.le hC).trans hT)).symm
  rw [hkey, cumulantFromMoment_momentFromCumulant (splitCumulant m A B) hT0]

/-- Any set straddling both independent regions has vanishing cumulant. -/
theorem cumulantFromMoment_eq_zero_of_straddles {m : Finset α → ℂ} {A B : Finset α}
    (hind : IsIndependentAcross m A B) {T : Finset α} (hT : T ≤ A ⊔ B) (hTA : ¬T ≤ A)
    (hTB : ¬T ≤ B) : cumulantFromMoment m T = 0 := by
  have hT0 : T ≠ ⊥ := fun h => hTA (h ▸ bot_le)
  rw [cumulantFromMoment_eq_splitCumulant_of_le hind hT hT0, splitCumulant,
    if_neg (not_or.2 ⟨hTA, hTB⟩)]

/-- The cumulant of a union of two nonempty independent regions vanishes. -/
theorem cumulantFromMoment_eq_zero_of_isIndependentAcross {m : Finset α → ℂ} {A B : Finset α}
    (hind : IsIndependentAcross m A B) (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    cumulantFromMoment m (A ⊔ B) = 0 := by
  have hAB := hind.1
  refine cumulantFromMoment_eq_zero_of_straddles hind le_rfl ?_ ?_
  · intro h
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hB
    exact (Finset.disjoint_left.1 hAB) (h (Finset.mem_union.2 (Or.inr hx))) hx
  · intro h
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.2 hA
    exact (Finset.disjoint_left.1 hAB) hx (h (Finset.mem_union.2 (Or.inl hx)))

end Finpartition
