import LeanCondensedMatter.Analysis.Operator.TraceClass.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Diagonal operators from summable Hilbert-basis weights

This module constructs the bounded operator

`∑' i, a i • |b i⟩⟨b i|`

from a Hilbert basis `b` and an absolutely summable scalar family `a`. This is the operator-level
foundation needed to build genuine infinite-dimensional Gibbs states from a discrete energy basis,
without representing the generally unbounded Hamiltonian itself as a bounded continuous linear map.
-/

noncomputable section

namespace HilbertBasis

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The `i`th rank-one term of a diagonal operator in the Hilbert basis `b`. -/
def diagonalTerm (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (i : ι) : H →L[ℂ] H :=
  a i • InnerProductSpace.rankOne ℂ (b i) (b i)

/-- Absolute summability of the coefficients implies summability of the diagonal rank-one
operator series in operator norm. -/
theorem summable_diagonalTerm (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : Summable (diagonalTerm b a) := by
  refine Summable.of_norm_bounded ha fun i => ?_
  simp [diagonalTerm, norm_smul, b.orthonormal.1 i]

/-- The totalized diagonal operator series with coefficients `a` in the Hilbert basis `b`.
Analytic results about its action and compactness state absolute summability explicitly. -/
def diagonalOp (b : HilbertBasis ι ℂ H) (a : ι → ℂ) : H →L[ℂ] H :=
  ∑' i, diagonalTerm b a i

/-- The defining diagonal rank-one series converges to `diagonalOp`. -/
theorem hasSum_diagonalTerm (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : HasSum (diagonalTerm b a) (diagonalOp b a) :=
  (summable_diagonalTerm b a ha).hasSum

/-- The diagonal operator acts on each basis vector by its corresponding coefficient. -/
theorem diagonalOp_apply_basis (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) (j : ι) :
    diagonalOp b a (b j) = a j • b j := by
  classical
  have hmap := (hasSum_diagonalTerm b a ha).mapL
    (ContinuousLinearMap.apply ℂ H (b j))
  have htsum : (∑' i, diagonalTerm b a i (b j)) = a j • b j := by
    rw [tsum_eq_single j]
    · simp [diagonalTerm, InnerProductSpace.rankOne_apply,
        inner_self_eq_norm_sq_to_K, b.orthonormal.1 j]
    · intro i hij
      simp [diagonalTerm, InnerProductSpace.rankOne_apply, b.orthonormal.2 hij]
  calc
    diagonalOp b a (b j) = ∑' i, diagonalTerm b a i (b j) := hmap.tsum_eq.symm
    _ = a j • b j := htsum

omit [CompleteSpace H] in
/-- Every term of the diagonal operator series is compact. -/
theorem diagonalTerm_isCompact (b : HilbertBasis ι ℂ H) (a : ι → ℂ) (i : ι) :
    IsCompactOperator (diagonalTerm b a i) := by
  change IsCompactOperator
    (fun x : H => a i • InnerProductSpace.rankOne ℂ (b i) (b i) x)
  exact (ContinuousLinearMap.isCompactOperator_rankOne (b i) (b i)).smul (a i)

/-- A diagonal operator with absolutely summable coefficients is compact. -/
theorem diagonalOp_isCompact (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : IsCompactOperator (diagonalOp b a) := by
  classical
  have hfinite (s : Finset ι) :
      IsCompactOperator ⇑(∑ i ∈ s, diagonalTerm b a i : H →L[ℂ] H) := by
    refine Finset.sum_induction (fun i => diagonalTerm b a i)
      (fun A : H →L[ℂ] H => IsCompactOperator ⇑A) ?_ ?_ ?_
    · intro A B hA hB
      simpa only [ContinuousLinearMap.add_apply] using hA.add hB
    · change IsCompactOperator (fun _ : H => (0 : H))
      exact isCompactOperator_zero
    · intro i _
      exact diagonalTerm_isCompact b a i
  refine isCompactOperator_of_tendsto
    (l := Filter.atTop)
    (F := fun s : Finset ι => ∑ i ∈ s, diagonalTerm b a i)
    (f := diagonalOp b a) ?_ ?_
  · exact hasSum_diagonalTerm b a ha
  · exact Filter.Eventually.of_forall hfinite

end HilbertBasis
