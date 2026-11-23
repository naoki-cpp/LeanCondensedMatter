import Mathlib.Combinatorics.SimpleGraph.Matching
import LeanCondensedMatter.Combinatorics.PerfectPairing.Restriction
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Equiv.Prod

set_option linter.style.header false

/-!
# Fixed-point-free involutions have even orbit counts

A fixed-point-free involution pairs a finite type up, so the type has even cardinality. For a perfect
pairing this says any set of positions closed under `partner` has even size — which is what lets such
a set index half as many pairs, and so present the positions as a two-part splitting.
-/

namespace Combinatorics

/-- A fixed-point-free involution forces even cardinality. -/
theorem even_card_of_fixedPointFreeInvolution {α : Type*} [Fintype α]
    (p : Equiv.Perm α) (hp : Function.Involutive p) (hne : ∀ x, p x ≠ x) :
    Even (Fintype.card α) := by
  let adj : α → α → Prop := fun x y => p x = y
  have hadjSymm : Std.Symm adj := ⟨by
    intro x y h
    change p y = x
    calc
      p y = p (p x) := congrArg p h.symm
      _ = x := hp x⟩
  have hadjIrrefl : Std.Irrefl adj := ⟨fun x h => hne x h⟩
  let G : SimpleGraph α := ⟨adj, hadjSymm, hadjIrrefl⟩
  have hM : (⊤ : G.Subgraph).IsPerfectMatching := by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro x
    refine ⟨p x, rfl, fun y hy => ?_⟩
    change p x = y at hy
    exact hy.symm
  exact hM.even_card

/-- A finite type carrying a perfect pairing has even cardinality. -/
theorem PairingOn.even_card {α : Type*} [Fintype α] (P : PairingOn α) :
    Even (Fintype.card α) :=
  even_card_of_fixedPointFreeInvolution P.partner P.partner_involutive P.partner_ne

/-- **A set of positions closed under `partner` has even size.** Its elements come in pairs, so it
carries half as many pairs — the hypothesis a two-part splitting of the positions needs. -/
theorem Pairing.even_card_of_partner_mem {n : ℕ} (P : Pairing n) {A : Finset (Fin (2 * n))}
    (hA : ∀ x ∈ A, P.partner x ∈ A) : Even A.card := by
  classical
  have hinvariant (x : Fin (2 * n)) : x ∈ A ↔ P.partner x ∈ A := by
    refine ⟨hA x, fun hx => ?_⟩
    simpa only [P.partner_partner] using hA (P.partner x) hx
  have hcard := (P.restrict (fun x => x ∈ A) hinvariant).even_card
  rwa [Fintype.card_coe] at hcard

/-- For a partner-invariant family of legs, an equivalence separating one-legged external data
from interaction vertices with an even number of local legs forces an even external count.

This is a combinatorial property of perfect pairings, independent of vertex graphs or diagrams. -/
theorem PairingOn.even_card_left_of_invariant_subtype
    {Leg ExternalData InteractionData LocalData : Type*}
    [Finite Leg] [Fintype ExternalData] [Finite InteractionData] [Fintype LocalData]
    (pairing : PairingOn Leg) (p : Leg → Prop)
    (hPartner : ∀ leg, p leg ↔ p (pairing.partner leg))
    (legEquiv : {leg : Leg // p leg} ≃ ExternalData ⊕ (InteractionData × LocalData))
    (hLocal : Even (Fintype.card LocalData)) :
    Even (Fintype.card ExternalData) := by
  classical
  letI := Fintype.ofFinite Leg
  letI := Fintype.ofFinite InteractionData
  have hcard :
      Fintype.card {leg : Leg // p leg} =
        Fintype.card ExternalData + Fintype.card InteractionData * Fintype.card LocalData := by
    rw [Fintype.card_congr legEquiv, Fintype.card_sum, Fintype.card_prod]
  have hEven := (pairing.restrict p hPartner).even_card
  rw [hcard, Nat.even_add] at hEven
  exact hEven.mpr (Nat.even_mul.mpr (Or.inr hLocal))

end Combinatorics
