import LeanCondensedMatter.Combinatorics.Cumulant.Moment
import LeanCondensedMatter.Combinatorics.Cumulant.NormalizedCore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false

/-!
# Connected decompositions and multiplicative weights

A combinatorial object family may decompose uniquely into a partition of its vertex set and one
connected object on every block. Weight data are layered separately, so the same decomposition can
be reused with different coefficient rings and physical amplitudes.

The finite-sum factorization retains an arbitrary partition-dependent coefficient. Multiplicative
weights specialize that coefficient to one, giving the ordinary moment identity.

This module stops at the moment transform and therefore only requires a commutative semiring.
Möbius-inversion consequences live in `ConnectedDecompositionInversion.lean`.
-/

namespace Combinatorics

universe u v

/-- A family of finite objects with a unique connected-component decomposition. -/
structure ConnectedDecomposition (α : Type u) [DecidableEq α] where
  /-- Objects supported on a finite vertex set. -/
  Object : Finset α → Type v
  /-- Connected objects supported on a finite vertex set. -/
  ConnectedObject : Finset α → Type v
  /-- Finiteness of the object family on each finite vertex set. -/
  fintypeObject : ∀ S, Fintype (Object S)
  /-- Finiteness of the connected-object family on each finite vertex set. -/
  fintypeConnectedObject : ∀ S, Fintype (ConnectedObject S)
  /-- Equivalence between an object and its partition-indexed connected components. -/
  decompose : ∀ S : Finset α,
    Object S ≃ Σ π : Finpartition S, ∀ B : π.parts, ConnectedObject (B : Finset α)

/-- A multiplicative weight on a connected decomposition. -/
structure MultiplicativeWeight {α : Type*} [DecidableEq α]
    (D : ConnectedDecomposition α) (R : Type*) [CommSemiring R] where
  /-- Weight assigned to a full object. -/
  objectWeight : ∀ {S : Finset α}, D.Object S → R
  /-- Weight assigned to a connected object. -/
  connectedWeight : ∀ {S : Finset α}, D.ConnectedObject S → R
  weight_decompose : ∀ {S : Finset α} (d : D.Object S),
    objectWeight d =
      ∏ B : (D.decompose S d).1.parts, connectedWeight ((D.decompose S d).2 B)

namespace ConnectedDecomposition

attribute [local instance] ConnectedDecomposition.fintypeObject
  ConnectedDecomposition.fintypeConnectedObject

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

/-- A connected decomposition transports object weights to a partition-weighted moment.
The partition coefficient is arbitrary; no normalization or Möbius inversion is assumed. -/
theorem sum_objectWeight_eq_weightedMomentFromCumulant
    (D : ConnectedDecomposition α)
    (partitionWeight : ∀ S : Finset α, Finpartition S → R)
    (objectWeight : ∀ {S : Finset α}, D.Object S → R)
    (connectedWeight : ∀ {S : Finset α}, D.ConnectedObject S → R)
    (hweight : ∀ {S : Finset α} (d : D.Object S),
      objectWeight d =
        partitionWeight S (D.decompose S d).1 *
          ∏ B : (D.decompose S d).1.parts,
            connectedWeight ((D.decompose S d).2 B))
    (S : Finset α) :
    (∑ d : D.Object S, objectWeight d) =
      Finpartition.weightedMomentFromCumulant partitionWeight
        (fun T => ∑ d : D.ConnectedObject T, connectedWeight d) S := by
  classical
  have hreindex :
      (∑ d : D.Object S, objectWeight d) =
        ∑ x : Σ π : Finpartition S,
          ∀ B : π.parts, D.ConnectedObject (B : Finset α),
          partitionWeight S x.1 * ∏ B : x.1.parts, connectedWeight (x.2 B) := by
    rw [← Equiv.sum_comp (D.decompose S)
      (fun x : Σ π : Finpartition S,
        ∀ B : π.parts, D.ConnectedObject (B : Finset α) =>
          partitionWeight S x.1 * ∏ B : x.1.parts, connectedWeight (x.2 B))]
    exact Finset.sum_congr rfl fun d _ => hweight d
  rw [hreindex, Fintype.sum_sigma, Finpartition.weightedMomentFromCumulant]
  apply Finset.sum_congr rfl
  intro π _
  change (∑ y : ∀ B : π.parts, D.ConnectedObject (B : Finset α),
      partitionWeight S π * ∏ B : π.parts, connectedWeight (y B)) =
    partitionWeight S π * Finpartition.partitionProduct
      (fun T => ∑ d : D.ConnectedObject T, connectedWeight d) π
  rw [← Finset.mul_sum]
  apply congrArg (fun z : R => partitionWeight S π * z)
  rw [Finpartition.partitionProduct,
    ← Finset.prod_coe_sort π.parts
      (fun T => ∑ d : D.ConnectedObject T, connectedWeight d)]
  have hdist := Finset.prod_univ_sum
    (fun B : π.parts => (Finset.univ : Finset (D.ConnectedObject (B : Finset α))))
    (fun B d => connectedWeight d)
  rw [Fintype.piFinset_univ] at hdist
  exact hdist.symm


end ConnectedDecomposition

namespace MultiplicativeWeight

attribute [local instance] ConnectedDecomposition.fintypeObject
  ConnectedDecomposition.fintypeConnectedObject

variable {α R : Type*} [DecidableEq α] [CommSemiring R]
variable {D : ConnectedDecomposition α} (W : MultiplicativeWeight D R)

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
  simpa only [objectMoment, connectedContribution,
    Finpartition.weightedMomentFromCumulant_one] using
    (D.sum_objectWeight_eq_weightedMomentFromCumulant (fun _ _ => (1 : R))
      W.objectWeight W.connectedWeight
      (fun {S} d => by simpa only [one_mul] using W.weight_decompose d) S)

/-- The total object moment, bundled with its canonical empty-set normalization.
This construction uses only the forward connected-decomposition moment theorem. -/
noncomputable def normalizedObjectMoment : NormalizedSetFunction α R where
  toFun := W.objectMoment
  map_empty := by
    rw [W.objectMoment_eq_momentFromCumulant]
    exact Finpartition.momentFromCumulant_empty W.connectedContribution

@[simp]
theorem normalizedObjectMoment_apply (S : Finset α) :
    W.normalizedObjectMoment S = W.objectMoment S :=
  rfl

end MultiplicativeWeight
end Combinatorics
