import LeanCondensedMatter.Combinatorics.Cumulant.Inversion

set_option linter.style.header false

/-!
# Connected decompositions and multiplicative weights

A combinatorial object family may decompose uniquely into a partition of its vertex set and one
connected object on every block. Weight data are layered separately, so the same decomposition can
be reused with different coefficient rings and physical amplitudes.
-/

namespace Combinatorics

/-- A family of finite objects with a unique connected-component decomposition. -/
structure ConnectedDecomposition (α : Type*) [DecidableEq α] where
  Object : Finset α → Type*
  ConnectedObject : Finset α → Type*
  fintypeObject : ∀ S, Fintype (Object S)
  fintypeConnectedObject : ∀ S, Fintype (ConnectedObject S)
  decompose : ∀ S : Finset α,
    Object S ≃ Σ π : Finpartition S, ∀ B : π.parts, ConnectedObject (B : Finset α)

/-- A multiplicative weight on a connected decomposition. -/
structure MultiplicativeWeight {α : Type*} [DecidableEq α]
    (D : ConnectedDecomposition α) (R : Type*) [CommSemiring R] where
  objectWeight : ∀ {S : Finset α}, D.Object S → R
  connectedWeight : ∀ {S : Finset α}, D.ConnectedObject S → R
  weight_decompose : ∀ {S : Finset α} (d : D.Object S),
    objectWeight d =
      ∏ B : (D.decompose S d).1.parts, connectedWeight ((D.decompose S d).2 B)

namespace MultiplicativeWeight

variable {α R : Type*} [DecidableEq α] [CommRing R]
variable {D : ConnectedDecomposition α} (W : MultiplicativeWeight D R)

attribute [local instance] ConnectedDecomposition.fintypeObject
  ConnectedDecomposition.fintypeConnectedObject

/-- Total weight of all objects on a finite vertex set. -/
noncomputable def objectMoment (S : Finset α) : R :=
  ∑ d : D.Object S, W.objectWeight d

/-- Total weight of all connected objects on a finite vertex set. -/
noncomputable def connectedContribution (S : Finset α) : R :=
  ∑ d : D.ConnectedObject S, W.connectedWeight d

/-- Object weights form the moment transform of connected-object weights. -/
theorem objectMoment_eq_momentFromCumulant (S : Finset α) :
    W.objectMoment S = Finpartition.momentFromCumulant W.connectedContribution S := by
  classical
  have hreindex : W.objectMoment S =
      ∑ x : Σ π : Finpartition S, ∀ B : π.parts, D.ConnectedObject (B : Finset α),
        ∏ B : x.1.parts, W.connectedWeight (x.2 B) := by
    rw [objectMoment, ← Equiv.sum_comp (D.decompose S)
      (fun x : Σ π : Finpartition S, ∀ B : π.parts, D.ConnectedObject (B : Finset α) =>
        ∏ B : x.1.parts, W.connectedWeight (x.2 B))]
    exact Finset.sum_congr rfl fun d _ => W.weight_decompose d
  rw [hreindex, Fintype.sum_sigma, Finpartition.momentFromCumulant]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finpartition.partitionProduct,
    ← Finset.prod_coe_sort π.parts W.connectedContribution]
  have hdist := Finset.prod_univ_sum
    (fun B : π.parts => (Finset.univ : Finset (D.ConnectedObject (B : Finset α))))
    (fun B c => W.connectedWeight c)
  rw [Fintype.piFinset_univ] at hdist
  exact hdist.symm

/-- The cumulant of the total object weight is the connected-object contribution. -/
theorem cumulantFromMoment_objectMoment {S : Finset α} (hS : S ≠ ∅) :
    Finpartition.cumulantFromMoment W.objectMoment S = W.connectedContribution S := by
  have h := Finpartition.cumulantFromMoment_momentFromCumulant W.connectedContribution
    (S := S) hS
  have hfun : Finpartition.momentFromCumulant W.connectedContribution = W.objectMoment :=
    funext fun T => (W.objectMoment_eq_momentFromCumulant T).symm
  rwa [hfun] at h

end MultiplicativeWeight
end Combinatorics
