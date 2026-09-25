import LeanCondensedMatter.Analysis.Operator.Compact
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Hilbert-basis diagonal operators

This module constructs the bounded operator

`∑' i, a i • |b i⟩⟨b i|`

from a Hilbert basis `b` and an absolutely summable scalar family `a`. This neutral operator layer
is reused by Fredholm, density-state, and Gibbs constructions. It also records positivity for
summable nonnegative real coefficients, while spectral trace-class membership remains downstream.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace HilbertBasis

/-- Positivity is closed under convergence in the continuous-linear-map topology. -/
private theorem isPositive_of_tendsto
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {α : Type*} {l : Filter α} [NeBot l]
    {F : α → H →L[ℂ] H} {T : H →L[ℂ] H}
    (hF : Tendsto F l (𝓝 T)) (hpos : ∀ᶠ i in l, (F i).IsPositive) : T.IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff]
  constructor
  · intro x y
    have happly_x : Tendsto (fun i => F i x) l (𝓝 (T x)) :=
      ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto T).comp hF
    have happly_y : Tendsto (fun i => F i y) l (𝓝 (T y)) :=
      ((ContinuousLinearMap.apply ℂ H y).continuous.tendsto T).comp hF
    have hleft : Tendsto (fun i => inner ℂ (F i x) y) l (𝓝 (inner ℂ (T x) y)) :=
      happly_x.inner tendsto_const_nhds
    have hright : Tendsto (fun i => inner ℂ x (F i y)) l (𝓝 (inner ℂ x (T y))) :=
      tendsto_const_nhds.inner happly_y
    have heq : ∀ᶠ i in l, inner ℂ (F i x) y = inner ℂ x (F i y) :=
      hpos.mono fun i hi => hi.isSymmetric x y
    have hright' : Tendsto (fun i => inner ℂ (F i x) y) l (𝓝 (inner ℂ x (T y))) :=
      (tendsto_congr' heq).mpr hright
    exact tendsto_nhds_unique hleft hright'
  · intro x
    have happly : Tendsto (fun i => F i x) l (𝓝 (T x)) :=
      ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto T).comp hF
    have hinner : Tendsto (fun i => inner ℂ (F i x) x) l (𝓝 (inner ℂ (T x) x)) :=
      happly.inner tendsto_const_nhds
    exact isClosed_Ici.mem_of_tendsto hinner
      (hpos.mono fun i hi => hi.inner_nonneg_left x)

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
  change IsCompactOperator (a i • InnerProductSpace.rankOne ℂ (b i) (b i))
  exact (ContinuousLinearMap.isCompactOperator_rankOne (b i) (b i)).smul (a i)

/-- A diagonal operator with absolutely summable coefficients is compact. -/
theorem diagonalOp_isCompact (b : HilbertBasis ι ℂ H) (a : ι → ℂ)
    (ha : Summable fun i => ‖a i‖) : IsCompactOperator (diagonalOp b a) := by
  classical
  have hfinite (s : Finset ι) :
      IsCompactOperator ⇑(∑ i ∈ s, diagonalTerm b a i : H →L[ℂ] H) := by
    induction s using Finset.induction_on with
    | empty =>
        change IsCompactOperator (fun _ : H => (0 : H))
        exact isCompactOperator_zero
    | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        change IsCompactOperator (fun x : H =>
          diagonalTerm b a i x + (∑ j ∈ s, diagonalTerm b a j) x)
        exact (diagonalTerm_isCompact b a i).add ih
  refine isCompactOperator_of_tendsto
    (l := Filter.atTop)
    (F := fun s : Finset ι => ∑ i ∈ s, diagonalTerm b a i)
    (f := diagonalOp b a) ?_ ?_
  · exact hasSum_diagonalTerm b a ha
  · exact Filter.Eventually.of_forall hfinite

/-- A diagonal operator with summable real nonnegative/ coefficients is positive. -/
theorem diagonalOp_isPositive (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    (diagonalOp b (fun i => (a i : ℂ))).IsPositive := by
  classical
  let hac : Summable fun i => ‖(a i : ℂ)‖ := by simpa using ha
  let F : Finset ι → H →L[ℂ] H := fun s =>
    ∑ i ∈ s, diagonalTerm b (fun i => (a i : ℂ)) i
  have hFpos (s : Finset ι) : (F s).IsPositive := by
    unfold F
    apply ContinuousLinearMap.isPositive_sum
    intro i hi
    have hcoeff : 0 ≤ (a i : ℂ) :=
      (RCLike.ofReal_nonneg (K := ℂ)).mpr (ha_nonneg i)
    simpa [diagonalTerm] using
      (InnerProductSpace.isPositive_rankOne_self (𝕜 := ℂ) (b i)).smul_of_nonneg hcoeff
  apply isPositive_of_tendsto
    (l := Filter.atTop)
    (F := F) (T := diagonalOp b (fun i => (a i : ℂ)))
  · exact hasSum_diagonalTerm b (fun i => (a i : ℂ)) hac
  · exact Filter.Eventually.of_forall hFpos

end HilbertBasis
