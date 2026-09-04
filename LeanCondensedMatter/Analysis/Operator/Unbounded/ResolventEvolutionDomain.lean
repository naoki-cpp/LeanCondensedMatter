import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolutionStrongContinuity
import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventCommutation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Domain invariance of the limiting Stone evolution

The bounded self-adjoint resolvent approximants commute with every nonreal resolvent of the original
self-adjoint operator.  Their exponential evolutions therefore commute with those resolvents as
well.  Passing this identity through the vectorwise strong limit shows that the limiting unitary
evolution commutes with every nonreal resolvent.

Using a fixed nonreal parameter, every vector in the original operator domain can be represented as
a resolvent value.  Resolvent commutation then implies that the limiting evolution preserves the
original domain and intertwines the unbounded generator there.
-/

namespace LinearPMap

noncomputable section

open Complex Filter
open scoped InnerProductSpace Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem imaginaryParameter_im_ne_zero {r : ℝ} (hr : 0 < r) :
    (((r : ℂ) * I).im) ≠ 0 := by
  simpa using ne_of_gt hr

private theorem star_imaginaryParameter_im_ne_zero {r : ℝ} (hr : 0 < r) :
    ((star ((r : ℂ) * I)).im) ≠ 0 := by
  simpa using neg_ne_zero.mpr (ne_of_gt hr)

private theorem I_im_ne_zero : (I : ℂ).im ≠ 0 := by
  norm_num

/-- Every bounded self-adjoint resolvent approximant commutes with every nonreal resolvent of the
original self-adjoint operator. -/
theorem boundedSelfAdjointApproximation_nonrealResolvent_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : z.im ≠ 0) :
    Commute (boundedSelfAdjointApproximation A hA r hr)
      (nonrealResolvent A hA z hz) := by
  unfold boundedSelfAdjointApproximation
  apply Commute.smul_left
  apply Commute.add_left
  · exact nonrealResolvent_commute A hA ((r : ℂ) * I) z
      (imaginaryParameter_im_ne_zero hr) hz
  · exact nonrealResolvent_commute A hA (star ((r : ℂ) * I)) z
      (star_imaginaryParameter_im_ne_zero hr) hz

/-- Exponentiating a bounded resolvent approximant preserves its commutation with every nonreal
resolvent. -/
theorem resolventApproximationEvolution_nonrealResolvent_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r : ℝ) (hr : 0 < r) (t : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    Commute (resolventApproximationEvolution A hA r hr t)
      (nonrealResolvent A hA z hz) := by
  unfold resolventApproximationEvolution boundedUnitaryEvolution
  exact
    ((boundedSelfAdjointApproximation_nonrealResolvent_commute A hA r hr z hz).smul_left _).exp_left

/-- The totalized positive-scale bounded evolution commutes with every nonreal resolvent. -/
theorem resolventApproximationEvolutionAtScale_nonrealResolvent_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r t : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    Commute (resolventApproximationEvolutionAtScale A hA r t)
      (nonrealResolvent A hA z hz) := by
  unfold resolventApproximationEvolutionAtScale
  exact resolventApproximationEvolution_nonrealResolvent_commute A hA _ _ t z hz

/-- Nonreal resolvent commutation passes through the vectorwise strong limit. -/
theorem resolventEvolutionStrongLimitOperator_nonrealResolvent_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (t : ℝ) (z : ℂ) (hz : z.im ≠ 0) (y : H) :
    resolventEvolutionStrongLimitOperator A hA t (nonrealResolvent A hA z hz y) =
      nonrealResolvent A hA z hz (resolventEvolutionStrongLimitOperator A hA t y) := by
  have hleft :=
    tendsto_resolventApproximationEvolutionAtScale_apply A hA t
      (nonrealResolvent A hA z hz y)
  have hright :
      Tendsto
        (fun r : ℝ =>
          nonrealResolvent A hA z hz
            (resolventApproximationEvolutionAtScale A hA r t y))
        atTop
        (𝓝 (nonrealResolvent A hA z hz
          (resolventEvolutionStrongLimitOperator A hA t y))) := by
    exact ((nonrealResolvent A hA z hz).continuous.tendsto _).comp
      (tendsto_resolventApproximationEvolutionAtScale_apply A hA t y)
  exact tendsto_nhds_unique
    (hleft.congr' (Eventually.of_forall fun r => by
      have happ := congrArg (fun T : H →L[ℂ] H => T y)
        (resolventApproximationEvolutionAtScale_nonrealResolvent_commute A hA r t z hz).eq
      simpa using happ))
    hright

/-- Operator form of nonreal resolvent commutation for the limiting Stone evolution. -/
theorem resolventEvolutionStrongLimitOperator_nonrealResolvent_mul_comm
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (t : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    resolventEvolutionStrongLimitOperator A hA t * nonrealResolvent A hA z hz =
      nonrealResolvent A hA z hz * resolventEvolutionStrongLimitOperator A hA t := by
  ext y
  simpa using resolventEvolutionStrongLimitOperator_nonrealResolvent_apply A hA t z hz y

/-- `Commute`-packaged form of resolvent commutation for the limiting Stone evolution. -/
theorem resolventEvolutionStrongLimitOperator_nonrealResolvent_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (t : ℝ) (z : ℂ) (hz : z.im ≠ 0) :
    Commute (resolventEvolutionStrongLimitOperator A hA t)
      (nonrealResolvent A hA z hz) := by
  exact resolventEvolutionStrongLimitOperator_nonrealResolvent_mul_comm A hA t z hz

/-- The limiting Stone evolution preserves the original self-adjoint operator domain. -/
theorem resolventEvolutionStrongLimitOperator_mem_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    resolventEvolutionStrongLimitOperator A hA t (x : H) ∈ A.domain := by
  let z : ℂ := I
  have hz : z.im ≠ 0 := by
    simpa [z] using I_im_ne_zero
  let y : H := A x - z • (x : H)
  have hxrepr : nonrealResolvent A hA z hz y = (x : H) := by
    dsimp [y]
    rw [(nonrealResolvent A hA z hz).map_sub,
      (nonrealResolvent A hA z hz).map_smul,
      nonrealResolvent_apply_operator A hA z hz x]
    module
  have hcomm :=
    resolventEvolutionStrongLimitOperator_nonrealResolvent_apply A hA t z hz y
  have hrepr :
      resolventEvolutionStrongLimitOperator A hA t (x : H) =
        nonrealResolvent A hA z hz
          (resolventEvolutionStrongLimitOperator A hA t y) := by
    calc
      resolventEvolutionStrongLimitOperator A hA t (x : H) =
          resolventEvolutionStrongLimitOperator A hA t
            (nonrealResolvent A hA z hz y) := by rw [hxrepr]
      _ = nonrealResolvent A hA z hz
            (resolventEvolutionStrongLimitOperator A hA t y) := hcomm
  rw [hrepr]
  exact nonrealResolvent_mem_domain A hA z hz _

/-- On its original domain, the unbounded self-adjoint generator intertwines with the limiting
Stone evolution. -/
theorem resolventEvolutionStrongLimitOperator_apply_domain
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (t : ℝ) (x : A.domain) :
    A ⟨resolventEvolutionStrongLimitOperator A hA t (x : H),
        resolventEvolutionStrongLimitOperator_mem_domain A hA t x⟩ =
      resolventEvolutionStrongLimitOperator A hA t (A x) := by
  let U : H →L[ℂ] H := resolventEvolutionStrongLimitOperator A hA t
  let z : ℂ := I
  have hz : z.im ≠ 0 := by
    simpa [z] using I_im_ne_zero
  let R : H →L[ℂ] H := nonrealResolvent A hA z hz
  let y : H := A x - z • (x : H)
  have hxrepr : R y = (x : H) := by
    dsimp [R, y]
    rw [(nonrealResolvent A hA z hz).map_sub,
      (nonrealResolvent A hA z hz).map_smul,
      nonrealResolvent_apply_operator A hA z hz x]
    module
  have hcomm : U (R y) = R (U y) := by
    exact resolventEvolutionStrongLimitOperator_nonrealResolvent_apply A hA t z hz y
  have hUrepr : U (x : H) = R (U y) := by
    calc
      U (x : H) = U (R y) := by rw [hxrepr]
      _ = R (U y) := hcomm
  let ux : A.domain :=
    ⟨U (x : H), resolventEvolutionStrongLimitOperator_mem_domain A hA t x⟩
  let rx : A.domain :=
    ⟨R (U y), nonrealResolvent_mem_domain A hA z hz (U y)⟩
  have huxrx : ux = rx := by
    apply Subtype.ext
    exact hUrepr
  change A ux = U (A x)
  rw [huxrx]
  have hshift : A rx - z • R (U y) = U y := by
    simpa [rx, R] using apply_nonrealResolvent_sub_smul A hA z hz (U y)
  have hAeq : A rx = U y + z • R (U y) :=
    (sub_eq_iff_eq_add).mp hshift
  have hUy : U y = U (A x) - z • U (x : H) := by
    dsimp [y]
    rw [U.map_sub, U.map_smul]
  calc
    A rx = U y + z • R (U y) := hAeq
    _ = (U (A x) - z • U (x : H)) + z • U (x : H) := by
      rw [← hUrepr, hUy]
    _ = U (A x) := by module

end

end LinearPMap
