import Mathlib.Combinatorics.SimpleGraph.Matching
import LeanCondensedMatter.Combinatorics.PerfectPairing.Core

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
  let M : G.Subgraph :=
    { verts := Set.univ
      Adj := adj
      adj_sub := fun h => h
      edge_vert := fun _ => Set.mem_univ _
      symm := hadjSymm }
  have hM : M.IsPerfectMatching := by
    rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
    intro x
    refine ⟨p x, rfl, fun y hy => ?_⟩
    change p x = y at hy
    exact hy.symm
  exact hM.even_card

/-- **A set of positions closed under `partner` has even size.** Its elements come in pairs, so it
carries half as many pairs — the hypothesis a two-part splitting of the positions needs. -/
theorem Pairing.even_card_of_partner_mem {n : ℕ} (P : Pairing n) {A : Finset (Fin (2 * n))}
    (hA : ∀ x ∈ A, P.partner x ∈ A) : Even A.card := by
  classical
  have hinv : Function.Involutive (fun x : ↥A => (⟨P.partner x, hA x x.2⟩ : ↥A)) := by
    intro x
    exact Subtype.ext (P.partner_partner (x : Fin (2 * n)))
  have hne : ∀ x : ↥A, (Function.Involutive.toPerm _ hinv) x ≠ x := by
    intro x hx
    exact P.partner_ne (x : Fin (2 * n)) (congrArg Subtype.val hx)
  have hcard := even_card_of_fixedPointFreeInvolution
    (Function.Involutive.toPerm _ hinv) hinv hne
  rwa [Fintype.card_coe] at hcard

end Combinatorics
