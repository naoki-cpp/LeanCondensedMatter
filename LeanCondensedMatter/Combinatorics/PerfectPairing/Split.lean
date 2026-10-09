import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import LeanCondensedMatter.Combinatorics.SumEquivPartition

set_option linter.style.header false

/-!
# Splitting a pairing along a decomposition of its positions

A *position splitting* presents the ambient positions of a pairing of `Fin (2 * n)` as two labelled
parts carrying `a` and `b` pairs. A pairing is *split* by it when no pair crosses between the parts;
such a pairing restricts to a pairing of each part through `PairingOn.restrictAlongEquiv`.

This is the decomposition a connected-component factorization uses: the pairs of a Wick diagram
never join two different connected components, so the diagram's pairing restricts to each component.

Only the left part needs to be assumed closed under `partner`. Closure of the right part is
automatic, because `partner` is an involution: a right position paired to a left one would make that
left position paired to a right one.

Restricting and assembling are mutually inverse, so the pairings split by a given splitting are
exactly the pairs of pairings of the parts (`Pairing.splitEquiv`).

Compare `Combinatorics.SideSplitting`, where the pairs all *do* cross between the two parts. The two
are the extreme cases of the same presentation of the positions.
-/

namespace Combinatorics

variable {a b n : ℕ}

/-- A presentation of the ambient positions of a pairing of `Fin (2 * n)` as two parts carrying `a`
and `b` pairs. -/
abbrev PositionSplitting (a b n : ℕ) := Fin (2 * a) ⊕ Fin (2 * b) ≃ Fin (2 * n)

/-- A pairing is *split* by a position splitting when the left part is closed under `partner`, so
that no pair joins the two parts. -/
def Pairing.IsSplit (e : PositionSplitting a b n) (P : Pairing n) : Prop :=
  ∀ i : Fin (2 * a), ∃ j : Fin (2 * a), P.partner (e (Sum.inl i)) = e (Sum.inl j)

/-- **The right part is closed automatically.** A right position paired to a left one would make
that left position paired to a right one, contradicting the left closure. -/
theorem Pairing.isSplit_inr (e : PositionSplitting a b n) {P : Pairing n} (h : P.IsSplit e)
    (i : Fin (2 * b)) : ∃ j : Fin (2 * b), P.partner (e (Sum.inr i)) = e (Sum.inr j) := by
  obtain ⟨y, hy⟩ := e.surjective (P.partner (e (Sum.inr i)))
  cases y with
  | inr j => exact ⟨j, hy.symm⟩
  | inl k =>
      obtain ⟨j, hj⟩ := h k
      have hback : P.partner (e (Sum.inl k)) = e (Sum.inr i) := by
        rw [hy, P.partner_partner]
      exact absurd (hback.symm.trans hj) (fun h => by simpa using e.injective h)

private theorem splitLeftInvariant (e : PositionSplitting a b n) {P : Pairing n}
    (h : P.IsSplit e) (i : Fin (2 * n)) :
    i ∈ SumEquiv.leftImage e ↔ P.partner i ∈ SumEquiv.leftImage e := by
  have hclosed : ∀ j, j ∈ SumEquiv.leftImage e →
      P.partner j ∈ SumEquiv.leftImage e := by
    intro j hj
    obtain ⟨k, rfl⟩ := (SumEquiv.mem_leftImage_iff e j).1 hj
    obtain ⟨l, hl⟩ := h k
    exact (SumEquiv.mem_leftImage_iff e _).2 ⟨l, hl.symm⟩
  constructor
  · exact hclosed i
  · intro hi
    simpa only [P.partner_partner] using hclosed (P.partner i) hi

private theorem splitRightInvariant (e : PositionSplitting a b n) {P : Pairing n}
    (h : P.IsSplit e) (i : Fin (2 * n)) :
    i ∈ SumEquiv.rightImage e ↔ P.partner i ∈ SumEquiv.rightImage e := by
  rw [SumEquiv.mem_rightImage_iff_not_mem_leftImage,
    SumEquiv.mem_rightImage_iff_not_mem_leftImage]
  exact not_congr (splitLeftInvariant e h i)

section Left

variable (e : PositionSplitting a b n) {P : Pairing n} (h : P.IsSplit e)

/-- The pairing induced on the left part by restricting to its invariant image. -/
noncomputable def Pairing.splitLeft : Pairing a :=
  P.restrictAlongEquiv (fun i => i ∈ SumEquiv.leftImage e) (splitLeftInvariant e h)
    (SumEquiv.leftSubtypeEquiv e).symm

/-- The induced left pairing is read off the ambient partner map. -/
@[simp]
theorem Pairing.partner_splitLeft (i : Fin (2 * a)) :
    P.partner (e (Sum.inl i)) = e (Sum.inl ((P.splitLeft e h).partner i)) := by
  have he : (SumEquiv.leftSubtypeEquiv e).symm.symm = SumEquiv.leftSubtypeEquiv e := rfl
  simpa only [Pairing.splitLeft, he, SumEquiv.leftSubtypeEquiv_val] using
    (P.restrictAlongEquiv_partner_symm_val (fun j => j ∈ SumEquiv.leftImage e)
      (splitLeftInvariant e h) (SumEquiv.leftSubtypeEquiv e).symm i).symm

end Left

section Right

variable (e : PositionSplitting a b n) {P : Pairing n} (h : P.IsSplit e)

/-- The pairing induced on the right part by restricting to its invariant image. -/
noncomputable def Pairing.splitRight : Pairing b :=
  P.restrictAlongEquiv (fun i => i ∈ SumEquiv.rightImage e) (splitRightInvariant e h)
    (SumEquiv.rightSubtypeEquiv e).symm

/-- The induced right pairing is read off the ambient partner map. -/
@[simp]
theorem Pairing.partner_splitRight (i : Fin (2 * b)) :
    P.partner (e (Sum.inr i)) = e (Sum.inr ((P.splitRight e h).partner i)) := by
  have he : (SumEquiv.rightSubtypeEquiv e).symm.symm = SumEquiv.rightSubtypeEquiv e := rfl
  simpa only [Pairing.splitRight, he, SumEquiv.rightSubtypeEquiv_val] using
    (P.restrictAlongEquiv_partner_symm_val (fun j => j ∈ SumEquiv.rightImage e)
      (splitRightInvariant e h) (SumEquiv.rightSubtypeEquiv e).symm i).symm

end Right

section Assemble

/-- **Assemble a pairing from a pairing on each part.** Inverse construction to `splitLeft` and
`splitRight`: no pair joins the two parts, so the two partner maps can simply be run side by side. -/
def Pairing.ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    Pairing n :=
  (P.sumCongr Q).transport e.symm

@[simp]
theorem Pairing.ofSplit_partner_inl (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (i : Fin (2 * a)) :
    (Pairing.ofSplit e P Q).partner (e (Sum.inl i)) = e (Sum.inl (P.partner i)) := by
  simp [Pairing.ofSplit]

@[simp]
theorem Pairing.ofSplit_partner_inr (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b)
    (i : Fin (2 * b)) :
    (Pairing.ofSplit e P Q).partner (e (Sum.inr i)) = e (Sum.inr (Q.partner i)) := by
  simp [Pairing.ofSplit]


/-- Normalized pairs of a pairing assembled from two independent parts are precisely
the normalized pairs of those parts, tagged by their side.

The position splitting is not required to preserve the ambient order: normalization may
reverse an individual transported pair. This equivalence is the reindexing input for
factorizing products of pair contractions over an arbitrary slot shuffle. -/
noncomputable def Pairing.ofSplitNormalizedPairEquiv
    (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    P.NormalizedPair ⊕ Q.NormalizedPair ≃ (Pairing.ofSplit e P Q).NormalizedPair := by
  classical
  let endpointEquiv :
      (P.NormalizedPair ⊕ Q.NormalizedPair) × Fin 2 ≃
        Fin (2 * a) ⊕ Fin (2 * b) :=
    (Equiv.sumProdDistrib P.NormalizedPair Q.NormalizedPair (Fin 2)).trans
      (Equiv.sumCongr P.pairEndpointEquiv Q.pairEndpointEquiv)
  refine (Pairing.ofSplit e P Q).normalizedPairEquivOfEndpointEquiv endpointEquiv e ?_
  intro pr
  cases pr with
  | inl x =>
      change (Pairing.ofSplit e P Q).partner
          (e (Sum.inl (P.pairEndpointEquiv (x, 0)))) =
        e (Sum.inl (P.pairEndpointEquiv (x, 1)))
      rw [Pairing.ofSplit_partner_inl]
      simp only [Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint_zero,
        Pairing.pairEndpoint_one]
      exact congrArg (fun j => e (Sum.inl j))
        ((P.mem_pairs_iff x.1.1 x.1.2).mp x.2).2
  | inr x =>
      change (Pairing.ofSplit e P Q).partner
          (e (Sum.inr (Q.pairEndpointEquiv (x, 0)))) =
        e (Sum.inr (Q.pairEndpointEquiv (x, 1)))
      rw [Pairing.ofSplit_partner_inr]
      simp only [Pairing.pairEndpointEquiv_apply, Pairing.pairEndpoint_zero,
        Pairing.pairEndpoint_one]
      exact congrArg (fun j => e (Sum.inr j))
        ((Q.mem_pairs_iff x.1.1 x.1.2).mp x.2).2


/-- An assembled pairing is split by the splitting it was assembled along. -/
theorem Pairing.isSplit_ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplit e P Q).IsSplit e := fun i =>
  ⟨P.partner i, Pairing.ofSplit_partner_inl e P Q i⟩

end Assemble

section Inverse

/-- Assembling and then restricting to the left part returns the left pairing. -/
@[simp]
theorem Pairing.splitLeft_ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplit e P Q).splitLeft e (Pairing.isSplit_ofSplit e P Q) = P := by
  refine PairingOn.ext (Equiv.ext fun i => ?_)
  have h := Pairing.partner_splitLeft e (Pairing.isSplit_ofSplit e P Q) i
  rw [Pairing.ofSplit_partner_inl] at h
  exact (Sum.inl.inj (e.injective h)).symm

/-- Assembling and then restricting to the right part returns the right pairing. -/
@[simp]
theorem Pairing.splitRight_ofSplit (e : PositionSplitting a b n) (P : Pairing a) (Q : Pairing b) :
    (Pairing.ofSplit e P Q).splitRight e (Pairing.isSplit_ofSplit e P Q) = Q := by
  refine PairingOn.ext (Equiv.ext fun i => ?_)
  have h := Pairing.partner_splitRight e (Pairing.isSplit_ofSplit e P Q) i
  rw [Pairing.ofSplit_partner_inr] at h
  exact (Sum.inr.inj (e.injective h)).symm

/-- **A split pairing is assembled from its two restrictions.** Nothing is lost by taking a split
pairing apart: every position lies in one of the parts, and its partner lies in the same part. -/
@[simp]
theorem Pairing.ofSplit_splitLeft_splitRight (e : PositionSplitting a b n) {P : Pairing n}
    (h : P.IsSplit e) :
    Pairing.ofSplit e (P.splitLeft e h) (P.splitRight e h) = P := by
  refine PairingOn.ext (Equiv.ext fun i => ?_)
  obtain ⟨x, rfl⟩ := e.surjective i
  cases x with
  | inl j => rw [Pairing.ofSplit_partner_inl, Pairing.partner_splitLeft e h]
  | inr j => rw [Pairing.ofSplit_partner_inr, Pairing.partner_splitRight e h]

/-- **The pairings split by a position splitting are exactly the pairs of part pairings.**

This is the combinatorial content of a binary diagram decomposition: choosing a pairing that
respects the splitting is the same as choosing one on each part independently. A reindexing of a sum
over diagrams as a sum over pairs of pieces goes through this equivalence. -/
noncomputable def Pairing.splitEquiv (e : PositionSplitting a b n) :
    {P : Pairing n // P.IsSplit e} ≃ Pairing a × Pairing b where
  toFun P := (P.1.splitLeft e P.2, P.1.splitRight e P.2)
  invFun PQ := ⟨Pairing.ofSplit e PQ.1 PQ.2, Pairing.isSplit_ofSplit e PQ.1 PQ.2⟩
  left_inv P := Subtype.ext (Pairing.ofSplit_splitLeft_splitRight e P.2)
  right_inv PQ := by
    obtain ⟨P, Q⟩ := PQ
    simp only [Prod.mk.injEq]
    exact ⟨Pairing.splitLeft_ofSplit e P Q, Pairing.splitRight_ofSplit e P Q⟩

end Inverse

end Combinatorics
