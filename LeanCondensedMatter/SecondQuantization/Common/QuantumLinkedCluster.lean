import LeanCondensedMatter.SecondQuantization.Fermionic.WeightedDiagonalFunctional
import LeanCondensedMatter.Combinatorics.CumulantFactorization
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Fermionic occupation moments and the linked-cluster bridge

Phase 8 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the first
bridge between Track D (weighted expectation functionals on `FockSpaceFermionic`) and Track B (the
abstract moment-cumulant duality on the partition lattice, `Combinatorics/MomentCumulant.lean`,
`Combinatorics/CumulantFactorization.lean`).

`occupationMoment w S := (Σₙ (if S ⊆ n then w n else 0)) / Z(w)` is the normalized weighted
diagonal functional for the simultaneous occupation of every mode in `S`, `⟨∏ᵢ∈S nᵢ⟩_w`, computed
directly as a weighted sum rather than via an operator product (the `numberOperator i`'s commute as
they're simultaneously diagonal, but `FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode` has no
`CommMonoid` structure under composition to state that with `Finset.prod`, so this file bypasses
the issue rather than solving it). It lands exactly in Track B's `Finset Mode → ℂ` moment-function
type, with
`occupationMoment w ⊥ = 1` matching `IsIndependentAcross`'s normalization hypothesis.

Despite this file's current `Common/` path, the implementation is fermionic-specific: it imports
`Fermionic.WeightedDiagonalFunctional` and uses `FermionOccupation` throughout. It should be moved under
`Fermionic/` or generalized before being presented as statistics-independent common infrastructure.

`occupationProjector S` supplies the operator-level witness `∏ᵢ∈S nᵢ` (diagonal in the
occupation-number basis, built via `Finsupp.lift` exactly as `create`/`annihilate` are), with
`normalizedWeightedDiagonal_occupationProjector` confirming it reproduces `occupationMoment` and
`occupationProjector_singleton` confirming it agrees with `numberOperator` at a single mode.
`occupationProjector_mul`/`_comm`/`_idempotent`/`_empty` establish it as a genuine commuting-
projector algebra under composition, making "`occupationProjector S` is the simultaneous product
of number operators" an operator-algebra theorem rather than only a physical reading.

`IsProductWeightAcross w A B` formalizes *physical* independence of a weight across a mode
bipartition (`Disjoint A B`, `A ∪ B = univ`, `w n = wA (n ∩ A) * wB (n ∩ B)`) — e.g. a Gibbs weight
for a Hamiltonian `H = HA + HB` with `[HA, HB] = 0` and no cross-region interaction. It is *not* a
general interacting Gibbs weight. `occupationMoment_isIndependentAcross` shows it implies
`Finpartition.IsIndependentAcross (occupationMoment w) A B`, and `occupationCumulant_eq_zero_of_
isProductWeightAcross` packages the resulting cumulant-vanishing fact without exposing
`Finpartition.IsIndependentAcross` to callers.

This is a necessary building block for the Linked Cluster Theorem, not the theorem itself: the LCT
needs the harder statement that disconnected contributions cancel in `log Z` even in the presence
of cross-region interaction — see `notes/roadmaps/second-quantization.md` for what remains.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The weighted occupation-correlator moment.** `occupationMoment w S` is the normalized weighted
occupation correlator under the weight `w` — the diagonal functional
`⟨∏ᵢ∈S nᵢ⟩_w` of the simultaneous occupation of `S`, computed directly as a weighted sum. For positive real weights (a
genuine Boltzmann weight) it is the probability that every mode in `S` is occupied; `w` here is an
arbitrary complex-valued weight, so no probabilistic interpretation is assumed in general. As with
the normalized weighted diagonal functional, division by `partitionFunction w` is only physically meaningful when
`partitionFunction w ≠ 0`. -/
noncomputable def occupationMoment (w : FermionOccupation Mode → ℂ) (S : Finset Mode) : ℂ :=
  (∑ n ∈ (Finset.univ : Finset (FermionOccupation Mode)).filter (S ⊆ ·), w n) /
    partitionFunction w

omit [LinearOrder Mode] in
/-- **`occupationMoment` at `⊥` is `1`** (given a nonzero partition function): every occupation
state vacuously contains the empty set of modes, so the numerator is exactly `Z(w)`. This matches
`Finpartition.IsIndependentAcross`'s `m ⊥ = 1` normalization hypothesis. -/
theorem occupationMoment_bot {w : FermionOccupation Mode → ℂ} (hZ : partitionFunction w ≠ 0) :
    occupationMoment w ⊥ = 1 := by
  have hfilter : (Finset.univ : Finset (FermionOccupation Mode)).filter ((⊥ : Finset Mode) ⊆ ·) =
      Finset.univ := by
    ext n; simp
  rw [occupationMoment, hfilter]
  exact div_self hZ

/-- **`occupationMoment` at a singleton `{i}` is the normalized weighted diagonal functional of
`numberOperator i`.**
Connects the weighted-sum definition back to Track D's operator-level normalized weighted
functional. -/
theorem occupationMoment_singleton (w : FermionOccupation Mode → ℂ) (i : Mode) :
    occupationMoment w {i} = normalizedWeightedDiagonal w (numberOperator i) := by
  rw [occupationMoment, normalizedWeightedDiagonal, weightedTrace_numberOperator]
  have hfilter : (Finset.univ : Finset (FermionOccupation Mode)).filter
      (({i} : Finset Mode) ⊆ ·) = (Finset.univ : Finset (FermionOccupation Mode)).filter
      (i ∈ ·) := by
    ext n; simp [Finset.subset_iff]
  rw [hfilter]

/-! ## The occupation projector: an operator-level witness for `occupationMoment` -/

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The occupation-projector operator, on a basis state.** `basisState n` if `n` occupies every
mode of `S`, `0` otherwise — the simultaneous-occupation observable `∏ᵢ∈S nᵢ` at the basis-state
level. -/
noncomputable def occupationProjectorBasis (S : Finset Mode) (n : FermionOccupation Mode) :
    FockSpaceFermionic Mode :=
  if S ⊆ n then basisState n else 0

omit [LinearOrder Mode] [Fintype Mode] in
/-- **The occupation-projector operator**, extended linearly from `occupationProjectorBasis`.
Diagonal in the occupation-number basis, so `occupationProjector S` and `occupationProjector T`
commute for any `S`, `T` (`occupationProjector_comm`), without needing a `CommMonoid` structure on
`FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode` under composition. -/
noncomputable def occupationProjector (S : Finset Mode) :
    FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode :=
  Finsupp.lift (FockSpaceFermionic Mode) ℂ (FermionOccupation Mode) (occupationProjectorBasis S)

omit [LinearOrder Mode] [Fintype Mode] in
theorem occupationProjector_basisState (S : Finset Mode) (n : FermionOccupation Mode) :
    occupationProjector S (basisState n) = if S ⊆ n then basisState n else 0 := by
  change Finsupp.lift _ ℂ _ (occupationProjectorBasis S) (Finsupp.single n 1) =
    occupationProjectorBasis S n
  simp [Finsupp.lift_apply, Finsupp.sum_single_index, occupationProjectorBasis]

omit [Fintype Mode] in
/-- **`occupationProjector` at the singleton `{i}` is exactly `numberOperator i`.** Confirms the
operator-level definition matches the physical "number operator" reading. -/
theorem occupationProjector_singleton (i : Mode) :
    occupationProjector ({i} : Finset Mode) = numberOperator i := by
  apply linearMap_ext_basisState
  intro n
  simp [occupationProjector_basisState, numberOperator_basisState, Finset.singleton_subset_iff]

omit [LinearOrder Mode] in
/-- **The normalized weighted functional of `occupationProjector S` is `occupationMoment w S`.** The operator-
level bridge promised by `occupationMoment`'s docstring: the simultaneous-occupation observable's
normalized weighted diagonal functional agrees with the direct weighted-sum definition. -/
theorem normalizedWeightedDiagonal_occupationProjector (w : FermionOccupation Mode → ℂ) (S : Finset Mode) :
    normalizedWeightedDiagonal w (occupationProjector S) = occupationMoment w S := by
  rw [normalizedWeightedDiagonal, occupationMoment]
  congr 1
  have h : ∀ n : FermionOccupation Mode,
      matrixCoeff (occupationProjector S) n n = if S ⊆ n then 1 else 0 := fun n => by
    by_cases hs : S ⊆ n
    · exact matrixCoeff_of_smul_basisState (by
        rw [occupationProjector_basisState, if_pos hs, if_pos hs, one_smul])
    · exact matrixCoeff_of_smul_basisState (by
        rw [occupationProjector_basisState, if_neg hs, if_neg hs, zero_smul])
  simp only [weightedTrace, h, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]

/-! ## Algebra of occupation projectors -/

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem occupationProjector_empty :
    occupationProjector (∅ : Finset Mode) = LinearMap.id := by
  apply linearMap_ext_basisState
  intro n
  simp [occupationProjector_basisState]

omit [LinearOrder Mode] [Fintype Mode] in
/-- **Occupation projectors compose by taking unions.** The operator-level confirmation that
`occupationProjector S` genuinely behaves as the "simultaneous occupation of `S`" observable: two
such observables combine into the observable for their union, without needing a general
`CommMonoid` structure on composition. -/
theorem occupationProjector_mul (S T : Finset Mode) :
    occupationProjector S * occupationProjector T = occupationProjector (S ∪ T) := by
  apply linearMap_ext_basisState
  intro n
  rw [Module.End.mul_apply, occupationProjector_basisState (S := T)]
  by_cases hT : T ⊆ n
  · rw [if_pos hT, occupationProjector_basisState, occupationProjector_basisState]
    simp [Finset.union_subset_iff, hT]
  · rw [if_neg hT, map_zero, occupationProjector_basisState]
    simp only [Finset.union_subset_iff, hT, and_false, if_false]

omit [LinearOrder Mode] [Fintype Mode] in
theorem occupationProjector_comm (S T : Finset Mode) :
    occupationProjector S * occupationProjector T =
      occupationProjector T * occupationProjector S := by
  rw [occupationProjector_mul, occupationProjector_mul, Finset.union_comm]

omit [LinearOrder Mode] [Fintype Mode] in
@[simp]
theorem occupationProjector_idempotent (S : Finset Mode) :
    occupationProjector S * occupationProjector S = occupationProjector S := by
  rw [occupationProjector_mul, Finset.union_self]

/-! ## Independence from a product weight -/

/-- **`w` is a product weight across the mode bipartition `(A, B)`.** `A`, `B` partition all of
`Mode` (`Disjoint A B`, `A ∪ B = univ`), and `w` factors as `wA` on the `A`-part of an occupation
state times `wB` on the `B`-part — the combinatorial content of "the weight treats modes in `A`
and modes in `B` as physically independent". -/
def IsProductWeightAcross (w : FermionOccupation Mode → ℂ) (A B : Finset Mode) : Prop :=
  Disjoint A B ∧ A ∪ B = Finset.univ ∧
    ∃ wA wB : Finset Mode → ℂ, ∀ n, w n = wA (n ∩ A) * wB (n ∩ B)

omit [LinearOrder Mode] in
/-- **Reindexing a sum over occupation states restricted to contain `C`, split across a product
weight's two independent sides.** The combinatorial core of this section: every occupation state
`n ⊇ C` corresponds bijectively to a pair `(n ∩ A, n ∩ B)` with `n ∩ A ⊇ C ∩ A` a subset of `A`
and `n ∩ B ⊇ C ∩ B` a subset of `B` (via `Disjoint A B`/`A ∪ B = univ`), so a sum of a product
`wA (n ∩ A) * wB (n ∩ B)` over such `n` splits into a product of two independent sums. -/
theorem sum_filter_subset_eq_mul {A B : Finset Mode} (hAB : Disjoint A B)
    (hU : A ∪ B = Finset.univ) (wA wB : Finset Mode → ℂ) (C : Finset Mode) :
    (∑ n ∈ (Finset.univ : Finset (FermionOccupation Mode)).filter (C ⊆ ·), wA (n ∩ A) * wB (n ∩ B))
      = (∑ S ∈ A.powerset.filter ((C ∩ A) ⊆ ·), wA S) *
        (∑ T ∈ B.powerset.filter ((C ∩ B) ⊆ ·), wB T) := by
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  apply Finset.sum_nbij' (fun n => (n ∩ A, n ∩ B)) (fun p => p.1 ∪ p.2)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨Finset.inter_subset_right, Finset.inter_subset_inter_right hn⟩,
      Finset.inter_subset_right, Finset.inter_subset_inter_right hn⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
    obtain ⟨⟨-, hCS⟩, -, hCT⟩ := hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    calc C = C ∩ A ∪ C ∩ B := by
          rw [← Finset.inter_union_distrib_left, hU, Finset.inter_univ]
      _ ⊆ p.1 ∪ p.2 := Finset.union_subset_union hCS hCT
  · intro n _
    ext x
    simp only [Finset.mem_union, Finset.mem_inter]
    refine ⟨fun h => h.elim And.left And.left, fun hx => ?_⟩
    rcases Finset.mem_union.1 (hU ▸ Finset.mem_univ x : x ∈ A ∪ B) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_powerset] at hp
    obtain ⟨⟨hSA, -⟩, hTB, -⟩ := hp
    have hTA : p.2 ∩ A = ∅ :=
      Finset.eq_empty_of_forall_notMem fun x hx =>
        Finset.disjoint_left.1 hAB (Finset.mem_inter.1 hx).2 (hTB (Finset.mem_inter.1 hx).1)
    have hSB : p.1 ∩ B = ∅ :=
      Finset.eq_empty_of_forall_notMem fun x hx =>
        Finset.disjoint_left.1 hAB (hSA (Finset.mem_inter.1 hx).1) (Finset.mem_inter.1 hx).2
    refine Prod.ext ?_ ?_
    · change (p.1 ∪ p.2) ∩ A = p.1
      rw [Finset.union_inter_distrib_right, hTA, Finset.union_empty,
        Finset.inter_eq_left.2 hSA]
    · change (p.1 ∪ p.2) ∩ B = p.2
      rw [Finset.union_inter_distrib_right, hSB, Finset.empty_union,
        Finset.inter_eq_left.2 hTB]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hn
    rfl

omit [LinearOrder Mode] in
/-- **`occupationMoment` under a product weight, in terms of the two independent sides.** -/
theorem occupationMoment_eq_of_product_factorization {w wA wB : FermionOccupation Mode → ℂ}
    {A B : Finset Mode} (hAB : Disjoint A B) (hU : A ∪ B = Finset.univ)
    (hw : ∀ n, w n = wA (n ∩ A) * wB (n ∩ B)) (T : Finset Mode) :
    occupationMoment w T = (∑ S ∈ A.powerset.filter ((T ∩ A) ⊆ ·), wA S) *
      (∑ T' ∈ B.powerset.filter ((T ∩ B) ⊆ ·), wB T') / partitionFunction w := by
  rw [occupationMoment, ← sum_filter_subset_eq_mul hAB hU wA wB T]
  congr 1
  exact Finset.sum_congr rfl fun n _ => hw n

omit [LinearOrder Mode] in
theorem partitionFunction_eq_mul_of_product_factorization {w wA wB : FermionOccupation Mode → ℂ}
    {A B : Finset Mode} (hAB : Disjoint A B) (hU : A ∪ B = Finset.univ)
    (hw : ∀ n, w n = wA (n ∩ A) * wB (n ∩ B)) :
    partitionFunction w = (∑ S ∈ A.powerset, wA S) * (∑ T ∈ B.powerset, wB T) := by
  have h := sum_filter_subset_eq_mul hAB hU wA wB (⊥ : Finset Mode)
  have e1 : (Finset.univ : Finset (FermionOccupation Mode)).filter ((⊥ : Finset Mode) ⊆ ·) =
      Finset.univ := Finset.filter_true_of_mem fun n _ => Finset.empty_subset n
  have e2 : A.powerset.filter (((⊥ : Finset Mode) ∩ A) ⊆ ·) = A.powerset := by
    have : (⊥ : Finset Mode) ∩ A = ⊥ := by ext x; simp
    rw [this]; exact Finset.filter_true_of_mem fun S _ => Finset.empty_subset S
  have e3 : B.powerset.filter (((⊥ : Finset Mode) ∩ B) ⊆ ·) = B.powerset := by
    have : (⊥ : Finset Mode) ∩ B = ⊥ := by ext x; simp
    rw [this]; exact Finset.filter_true_of_mem fun T _ => Finset.empty_subset T
  rw [e1, e2, e3] at h
  rw [partitionFunction]
  simp_rw [hw]
  exact h

omit [LinearOrder Mode] in
/-- **The main theorem: a product weight makes `occupationMoment` independent across its
bipartition.** Connects the *physical* independence hypothesis `IsProductWeightAcross` to the
abstract hypothesis `Finpartition.IsIndependentAcross` that Track B's cumulant-vanishing theorem
(`cumulantFromMoment_eq_zero_of_isIndependentAcross`) needs. -/
theorem occupationMoment_isIndependentAcross {w : FermionOccupation Mode → ℂ} {A B : Finset Mode}
    (hw : IsProductWeightAcross w A B) (hZ : partitionFunction w ≠ 0) :
    Finpartition.IsIndependentAcross (occupationMoment w) A B := by
  obtain ⟨hAB, hU, wA, wB, hfact⟩ := hw
  refine ⟨hAB, occupationMoment_bot hZ, fun T _ => ?_⟩
  rw [Finset.inf_eq_inter, Finset.inf_eq_inter]
  have hZeq := partitionFunction_eq_mul_of_product_factorization hAB hU hfact
  have hTAA : (T ∩ A) ∩ A = T ∩ A := by rw [Finset.inter_assoc, Finset.inter_self]
  have hTAB : (T ∩ A) ∩ B = ⊥ :=
    Finset.eq_empty_of_forall_notMem fun x hx =>
      Finset.disjoint_left.1 hAB (Finset.mem_inter.1 (Finset.mem_inter.1 hx).1).2
        (Finset.mem_inter.1 hx).2
  have hTBA : (T ∩ B) ∩ A = ⊥ :=
    Finset.eq_empty_of_forall_notMem fun x hx =>
      Finset.disjoint_left.1 hAB (Finset.mem_inter.1 hx).2
        (Finset.mem_inter.1 (Finset.mem_inter.1 hx).1).2
  have hTBB : (T ∩ B) ∩ B = T ∩ B := by rw [Finset.inter_assoc, Finset.inter_self]
  have eA : A.powerset.filter ((⊥ : Finset Mode) ⊆ ·) = A.powerset :=
    Finset.filter_true_of_mem fun S _ => Finset.empty_subset S
  have eB : B.powerset.filter ((⊥ : Finset Mode) ⊆ ·) = B.powerset :=
    Finset.filter_true_of_mem fun T _ => Finset.empty_subset T
  have hZAB : (∑ S ∈ A.powerset, wA S) * (∑ T ∈ B.powerset, wB T) ≠ 0 := hZeq ▸ hZ
  obtain ⟨hZA, hZB⟩ := mul_ne_zero_iff.1 hZAB
  rw [occupationMoment_eq_of_product_factorization hAB hU hfact T,
    occupationMoment_eq_of_product_factorization hAB hU hfact (T ∩ A),
    occupationMoment_eq_of_product_factorization hAB hU hfact (T ∩ B), hTAA, hTAB, hTBA, hTBB,
    eA, eB, hZeq]
  field_simp

/-- **The occupation-number cumulant** — Track B's `cumulantFromMoment` specialized to
`occupationMoment w`. Named so the physics-facing corollary below reads without exposing
`Finpartition.IsIndependentAcross`. -/
noncomputable def occupationCumulant (w : FermionOccupation Mode → ℂ) (S : Finset Mode) : ℂ :=
  Finpartition.cumulantFromMoment (occupationMoment w) S

omit [LinearOrder Mode] in
/-- **Occupation-number cumulants vanish across a product-weight bipartition.** The physics-facing
form of `occupationMoment_isIndependentAcross`: under a product weight (e.g. a Gibbs weight for a
Hamiltonian `H = HA + HB` with `[HA, HB] = 0` and no cross-region interaction), the connected
correlator of modes spanning both `A` and `B` vanishes. This packages Track B's
`cumulantFromMoment_eq_zero_of_isIndependentAcross` so callers never need to name
`Finpartition.IsIndependentAcross` themselves. -/
theorem occupationCumulant_eq_zero_of_isProductWeightAcross {w : FermionOccupation Mode → ℂ}
    {A B : Finset Mode} (hw : IsProductWeightAcross w A B) (hZ : partitionFunction w ≠ 0)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) : occupationCumulant w (A ⊔ B) = 0 :=
  Finpartition.cumulantFromMoment_eq_zero_of_isIndependentAcross
    (occupationMoment_isIndependentAcross hw hZ) hA hB

end SecondQuantization
