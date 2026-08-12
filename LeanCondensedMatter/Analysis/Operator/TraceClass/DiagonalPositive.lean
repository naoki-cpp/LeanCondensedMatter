import LeanCondensedMatter.Analysis.Operator.TraceClass.Diagonal
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Positive diagonal operators

This module proves that operator-norm limits of positive continuous linear maps remain positive,
and applies that closure result to diagonal operators with real nonnegative coefficients.
-/

noncomputable section

open Filter Topology
open scoped ComplexOrder

namespace ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Positivity is closed under convergence in the continuous-linear-map topology. -/
theorem isPositive_of_tendsto {α : Type*} {l : Filter α} [NeBot l]
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

end ContinuousLinearMap

namespace HilbertBasis

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A diagonal operator with summable real nonnegative coefficients is positive. -/
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
  apply ContinuousLinearMap.isPositive_of_tendsto
    (l := Filter.atTop)
    (F := F) (T := diagonalOp b (fun i => (a i : ℂ)))
  · exact hasSum_diagonalTerm b (fun i => (a i : ℂ)) hac
  · exact Filter.Eventually.of_forall hFpos

/-- A diagonal operator with summable real nonnegative coefficients is self-adjoint. -/
theorem diagonalOp_isSelfAdjoint (b : HilbertBasis ι ℂ H) (a : ι → ℝ)
    (ha : Summable fun i => ‖a i‖) (ha_nonneg : ∀ i, 0 ≤ a i) :
    IsSelfAdjoint (diagonalOp b (fun i => (a i : ℂ))) :=
  (diagonalOp_isPositive b a ha ha_nonneg).isSelfAdjoint

end HilbertBasis
