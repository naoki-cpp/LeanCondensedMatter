import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction

set_option linter.style.header false

/-!
# Splitting a pairing along a decomposition of its positions

A sum equivalence presents the ambient positions of a pairing as two labelled parts. A pairing is *split* by it when no pair crosses between the parts;
such a pairing restricts to a pairing of each part through `PairingOn.restrictAlongEquiv`.

This is the decomposition a connected-component factorization uses: the pairs of a Wick diagram
never join two different connected components, so the diagram's pairing restricts to each component.

Only the left part needs to be assumed closed under `partner`. Closure of the right part is
automatic, because `partner` is an involution: a right position paired to a left one would make that
left position paired to a right one.

Restricting and assembling are mutually inverse, so the pairings split by a given splitting are
exactly the pairs of pairings of the parts (`PairingOn.splitEquiv`).

Compare `Combinatorics.SideSplitting`, where the pairs all *do* cross between the two parts. The two
are the extreme cases of the same presentation of the positions.
-/

namespace Combinatorics

/-- A presentation of the ambient positions of a pairing of `Fin (2 * n)` as two parts carrying `a`
and `b` pairs. -/
abbrev PositionSplitting (a b n : ℕ) := Fin (2 * a) ⊕ Fin (2 * b) ≃ Fin (2 * n)

variable {α β γ : Type*}

/-- A pairing is split by a sum equivalence when the left part is closed under the partner map. -/
def PairingOn.IsSplit (e : α ⊕ β ≃ γ) (P : PairingOn γ) : Prop :=
  ∀ i : α, ∃ j : α, P.partner (e (Sum.inl i)) = e (Sum.inl j)

/-- The right part is closed automatically by involutivity and disjointness of the summands. -/
theorem PairingOn.isSplit_inr (e : α ⊕ β ≃ γ) {P : PairingOn γ} (h : P.IsSplit e)
    (i : β) : ∃ j : β, P.partner (e (Sum.inr i)) = e (Sum.inr j) := by
  obtain ⟨z, hz⟩ := e.surjective (P.partner (e (Sum.inr i)))
  rcases z with k | j
  · obtain ⟨l, hl⟩ := h k
    have he : e (Sum.inr i) = e (Sum.inl l) := by
      rw [← hl, hz, P.partner_partner]
    have he' := e.injective he
    cases he'
  · exact ⟨j, hz.symm⟩

section Left

variable (e : α ⊕ β ≃ γ) {P : PairingOn γ} (h : P.IsSplit e)

/-- The pairing induced on the left part by restricting to its invariant range. -/
noncomputable def PairingOn.splitLeft : PairingOn α :=
  P.restrictAlongInjection (fun i => e (Sum.inl i))
    (fun _ _ he => Sum.inl.inj (e.injective he)) h

/-- The induced left pairing is read off the ambient partner map. -/
@[simp]
theorem PairingOn.partner_splitLeft (i : α) :
    P.partner (e (Sum.inl i)) = e (Sum.inl ((P.splitLeft e h).partner i)) :=
  P.restrictAlongInjection_partner _ _ h i

end Left

section Right

variable (e : α ⊕ β ≃ γ) {P : PairingOn γ} (h : P.IsSplit e)

/-- The pairing induced on the right part by restricting to its invariant range. -/
noncomputable def PairingOn.splitRight : PairingOn β :=
  P.restrictAlongInjection (fun i => e (Sum.inr i))
    (fun _ _ he => Sum.inr.inj (e.injective he)) (PairingOn.isSplit_inr e h)

/-- The induced right pairing is read off the ambient partner map. -/
@[simp]
theorem PairingOn.partner_splitRight (i : β) :
    P.partner (e (Sum.inr i)) = e (Sum.inr ((P.splitRight e h).partner i)) :=
  P.restrictAlongInjection_partner _ _ (PairingOn.isSplit_inr e h) i

end Right

section Assemble

/-- **Assemble a pairing from a pairing on each part.** Inverse construction to `splitLeft` and
`splitRight`: no pair joins the two parts, so the two partner maps can simply be run side by side. -/
def PairingOn.ofSplit (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) :
    PairingOn γ :=
  (P.sumCongr Q).transport e.symm

@[simp]
theorem PairingOn.ofSplit_partner_inl (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β)
    (i : α) :
    (PairingOn.ofSplit e P Q).partner (e (Sum.inl i)) = e (Sum.inl (P.partner i)) := by
  simp [PairingOn.ofSplit]

@[simp]
theorem PairingOn.ofSplit_partner_inr (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β)
    (i : β) :
    (PairingOn.ofSplit e P Q).partner (e (Sum.inr i)) = e (Sum.inr (Q.partner i)) := by
  simp [PairingOn.ofSplit]

/-- Reindexing the two local pairings and the corresponding sides of the position
splitting leaves the assembled ambient pairing unchanged. Local equivalences need not
preserve either endpoint order. -/
theorem PairingOn.ofSplit_reindex
    (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β)
    {α' β' : Type*} (left : α' ≃ α) (right : β' ≃ β) :
    PairingOn.ofSplit ((Equiv.sumCongr left right).trans e)
        (P.transport left) (Q.transport right) =
      PairingOn.ofSplit e P Q := by
  apply PairingOn.ext
  apply Equiv.ext
  intro z
  obtain ⟨x, rfl⟩ := ((Equiv.sumCongr left right).trans e).surjective z
  cases x with
  | inl i =>
      rw [PairingOn.ofSplit_partner_inl]
      change e (Sum.inl (left ((P.transport left).partner i))) =
        (PairingOn.ofSplit e P Q).partner (e (Sum.inl (left i)))
      rw [PairingOn.ofSplit_partner_inl, PairingOn.transport_partner, Equiv.apply_symm_apply]
  | inr j =>
      rw [PairingOn.ofSplit_partner_inr]
      change e (Sum.inr (right ((Q.transport right).partner j))) =
        (PairingOn.ofSplit e P Q).partner (e (Sum.inr (right j)))
      rw [PairingOn.ofSplit_partner_inr, PairingOn.transport_partner, Equiv.apply_symm_apply]

/-- An assembled pairing is split by the splitting it was assembled along. -/
theorem PairingOn.isSplit_ofSplit (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) :
    (PairingOn.ofSplit e P Q).IsSplit e := fun i =>
  ⟨P.partner i, PairingOn.ofSplit_partner_inl e P Q i⟩

end Assemble

section Inverse

/-- Assembling and then restricting to the left part returns the left pairing. -/
@[simp]
theorem PairingOn.splitLeft_ofSplit (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) :
    (PairingOn.ofSplit e P Q).splitLeft e (PairingOn.isSplit_ofSplit e P Q) = P := by
  exact (PairingOn.ofSplit e P Q).restrictAlongInjection_eq _ _ _ P
    (PairingOn.ofSplit_partner_inl e P Q)

/-- Assembling and then restricting to the right part returns the right pairing. -/
@[simp]
theorem PairingOn.splitRight_ofSplit (e : α ⊕ β ≃ γ) (P : PairingOn α) (Q : PairingOn β) :
    (PairingOn.ofSplit e P Q).splitRight e (PairingOn.isSplit_ofSplit e P Q) = Q := by
  exact (PairingOn.ofSplit e P Q).restrictAlongInjection_eq _ _ _ Q
    (PairingOn.ofSplit_partner_inr e P Q)

/-- **A split pairing is assembled from its two restrictions.** Nothing is lost by taking a split
pairing apart: every position lies in one of the parts, and its partner lies in the same part. -/
@[simp]
theorem PairingOn.ofSplit_splitLeft_splitRight (e : α ⊕ β ≃ γ) {P : PairingOn γ}
    (h : P.IsSplit e) :
    PairingOn.ofSplit e (P.splitLeft e h) (P.splitRight e h) = P := by
  refine PairingOn.ext (Equiv.ext fun i => ?_)
  obtain ⟨x, rfl⟩ := e.surjective i
  cases x with
  | inl j => rw [PairingOn.ofSplit_partner_inl, PairingOn.partner_splitLeft e h]
  | inr j => rw [PairingOn.ofSplit_partner_inr, PairingOn.partner_splitRight e h]

/-- **The pairings split by a position splitting are exactly the pairs of part pairings.**

This is the combinatorial content of a binary diagram decomposition: choosing a pairing that
respects the splitting is the same as choosing one on each part independently. A reindexing of a sum
over diagrams as a sum over pairs of pieces goes through this equivalence. -/
noncomputable def PairingOn.splitEquiv (e : α ⊕ β ≃ γ) :
    {P : PairingOn γ // P.IsSplit e} ≃ PairingOn α × PairingOn β where
  toFun P := (P.1.splitLeft e P.2, P.1.splitRight e P.2)
  invFun PQ := ⟨PairingOn.ofSplit e PQ.1 PQ.2, PairingOn.isSplit_ofSplit e PQ.1 PQ.2⟩
  left_inv P := Subtype.ext (PairingOn.ofSplit_splitLeft_splitRight e P.2)
  right_inv PQ := by
    obtain ⟨P, Q⟩ := PQ
    simp only [Prod.mk.injEq]
    exact ⟨PairingOn.splitLeft_ofSplit e P Q, PairingOn.splitRight_ofSplit e P Q⟩

end Inverse

end Combinatorics
