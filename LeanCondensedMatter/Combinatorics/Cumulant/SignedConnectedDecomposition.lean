import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecomposition

set_option linter.style.header false

/-!
# Signed finite-set connected-decomposition moments

For fermionic sources, grouping external fields by connected blocks can carry
a permutation sign. Such a sign cannot be removed from the ordinary
`Finpartition.momentFromCumulant` formula. Here it is explicit as a weight on
each partition and the standard connected-decomposition equivalence yields
the corresponding signed moment formula.

The theorem is semiring-generic and does not assume any arbitrary partition
weight admits ordinary Möbius inversion. Applications must prove that their
physical diagram weights obey the required signed factorization.
-/

namespace Finpartition

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

/-- A moment formed from connected-block weights with one additional
partition-dependent (e.g. fermionic shuffle) factor. -/
noncomputable def signedMomentFromCumulant
    (sign : ∀ S : Finset α, Finpartition S → R)
    (κ : Finset α → R) (S : Finset α) : R :=
  ∑ π : Finpartition S, sign S π * partitionProduct κ π

/-- With unit partition signs, the signed moment reduces to the ordinary
partition moment. -/
theorem signedMomentFromCumulant_one
    (κ : Finset α → R) (S : Finset α) :
    signedMomentFromCumulant (fun _ _ => 1) κ S =
      momentFromCumulant κ S := by
  classical
  simp [signedMomentFromCumulant, momentFromCumulant]

end Finpartition

namespace Combinatorics
namespace ConnectedDecomposition

attribute [local instance] ConnectedDecomposition.fintypeObject
  ConnectedDecomposition.fintypeConnectedObject

variable {α R : Type*} [DecidableEq α] [CommSemiring R]

/-- Finite connected decomposition yields a signed partition-moment identity,
provided the full-object weight factors into the sign of the external-block
partition and the product of its connected-object weights.

Unlike the unsigned `MultiplicativeWeight` theorem, this retains the sign
rather than assuming it equals one. It is an exact finite combinatorial
identity; no source or analytic Dyson-series identification is asserted. -/
theorem sum_objectWeight_eq_signedMomentFromCumulant
    (D : ConnectedDecomposition α)
    (sign : ∀ S : Finset α, Finpartition S → R)
    (objectWeight : ∀ {S : Finset α}, D.Object S → R)
    (connectedWeight : ∀ {S : Finset α}, D.ConnectedObject S → R)
    (hweight : ∀ {S : Finset α} (d : D.Object S),
      objectWeight d =
        sign S (D.decompose S d).1 *
          ∏ B : (D.decompose S d).1.parts,
            connectedWeight ((D.decompose S d).2 B))
    (S : Finset α) :
    (∑ d : D.Object S, objectWeight d) =
      Finpartition.signedMomentFromCumulant sign
        (fun T => ∑ d : D.ConnectedObject T, connectedWeight d) S := by
  classical
  have hreindex :
      (∑ d : D.Object S, objectWeight d) =
        ∑ x : Σ π : Finpartition S,
          ∀ B : π.parts, D.ConnectedObject (B : Finset α),
          sign S x.1 * ∏ B : x.1.parts, connectedWeight (x.2 B) := by
    rw [← Equiv.sum_comp (D.decompose S)
      (fun x : Σ π : Finpartition S,
        ∀ B : π.parts, D.ConnectedObject (B : Finset α) =>
          sign S x.1 * ∏ B : x.1.parts, connectedWeight (x.2 B))]
    exact Finset.sum_congr rfl fun d _ => hweight d
  rw [hreindex, Fintype.sum_sigma, Finpartition.signedMomentFromCumulant]
  apply Finset.sum_congr rfl
  intro π _
  change (∑ y : ∀ B : π.parts, D.ConnectedObject (B : Finset α),
      sign S π * ∏ B : π.parts, connectedWeight (y B)) =
    sign S π * Finpartition.partitionProduct
      (fun T => ∑ d : D.ConnectedObject T, connectedWeight d) π
  rw [← Finset.mul_sum]
  apply congrArg (fun z : R => sign S π * z)
  rw [Finpartition.partitionProduct,
    ← Finset.prod_coe_sort π.parts
      (fun T => ∑ d : D.ConnectedObject T, connectedWeight d)]
  have hdist := Finset.prod_univ_sum
    (fun B : π.parts => (Finset.univ : Finset (D.ConnectedObject (B : Finset α))))
    (fun B d => connectedWeight d)
  rw [Fintype.piFinset_univ] at hdist
  exact hdist.symm

end ConnectedDecomposition
end Combinatorics
