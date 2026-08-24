import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventApproximation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Resolvent identities and commutation

For a self-adjoint partial operator, the bounded resolvents at two nonreal spectral parameters
satisfy the usual resolvent identity and therefore commute pairwise. The bounded self-adjoint
resolvent approximants used in the Stone construction are symmetric linear combinations of these
resolvents, so approximants at different positive regularization scales commute as well.
-/

namespace LinearPMap

noncomputable section

open Complex
open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Pointwise resolvent identity for the convention `R(z) = (A-z)⁻¹`. -/
theorem nonrealResolvent_sub_nonrealResolvent_apply
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) (y : H) :
    nonrealResolvent A hA z hz y - nonrealResolvent A hA w hw y =
      (z - w) • nonrealResolvent A hA z hz (nonrealResolvent A hA w hw y) := by
  let x : A.domain :=
    ⟨nonrealResolvent A hA w hw y, nonrealResolvent_mem_domain A hA w hw y⟩
  have hy : A x - w • (x : H) = y := by
    simpa [x] using apply_nonrealResolvent_sub_smul A hA w hw y
  calc
    nonrealResolvent A hA z hz y - nonrealResolvent A hA w hw y =
        nonrealResolvent A hA z hz (A x - w • (x : H)) - (x : H) := by
      rw [hy]
    _ = (nonrealResolvent A hA z hz (A x) -
          w • nonrealResolvent A hA z hz (x : H)) - (x : H) := by
      rw [(nonrealResolvent A hA z hz).map_sub,
        (nonrealResolvent A hA z hz).map_smul]
    _ = ((x : H) + z • nonrealResolvent A hA z hz (x : H) -
          w • nonrealResolvent A hA z hz (x : H)) - (x : H) := by
      rw [nonrealResolvent_apply_operator A hA z hz x]
    _ = (z - w) • nonrealResolvent A hA z hz (nonrealResolvent A hA w hw y) := by
      change ((x : H) + z • nonrealResolvent A hA z hz (x : H) -
          w • nonrealResolvent A hA z hz (x : H)) - (x : H) =
        (z - w) • nonrealResolvent A hA z hz (x : H)
      module

/-- Bounded nonreal resolvents of one self-adjoint operator commute pairwise. -/
theorem nonrealResolvent_mul_comm
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    nonrealResolvent A hA z hz * nonrealResolvent A hA w hw =
      nonrealResolvent A hA w hw * nonrealResolvent A hA z hz := by
  ext y
  by_cases hzw : z = w
  · subst w
    rfl
  · have h₁ := nonrealResolvent_sub_nonrealResolvent_apply A hA z w hz hw y
    have h₂ := nonrealResolvent_sub_nonrealResolvent_apply A hA w z hw hz y
    have hscaled :
        (z - w) • nonrealResolvent A hA z hz (nonrealResolvent A hA w hw y) =
          (z - w) • nonrealResolvent A hA w hw (nonrealResolvent A hA z hz y) := by
      calc
        (z - w) • nonrealResolvent A hA z hz (nonrealResolvent A hA w hw y) =
            nonrealResolvent A hA z hz y - nonrealResolvent A hA w hw y := h₁.symm
        _ = -(nonrealResolvent A hA w hw y - nonrealResolvent A hA z hz y) := by
          module
        _ = -((w - z) • nonrealResolvent A hA w hw
              (nonrealResolvent A hA z hz y)) := by rw [h₂]
        _ = (z - w) • nonrealResolvent A hA w hw
              (nonrealResolvent A hA z hz y) := by
          module
    have hne : z - w ≠ 0 := sub_ne_zero.mpr hzw
    have hcancel := congrArg (fun v : H => (z - w)⁻¹ • v) hscaled
    simpa [smul_smul, hne] using hcancel

/-- `Commute`-packaged form of pairwise nonreal resolvent commutation. -/
theorem nonrealResolvent_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (z w : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    Commute (nonrealResolvent A hA z hz) (nonrealResolvent A hA w hw) := by
  exact nonrealResolvent_mul_comm A hA z w hz hw

/-- Bounded self-adjoint resolvent approximants at two positive scales commute. -/
theorem boundedSelfAdjointApproximation_commute
    (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    Commute (boundedSelfAdjointApproximation A hA r hr)
      (boundedSelfAdjointApproximation A hA s hs) := by
  unfold boundedSelfAdjointApproximation
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.add_left
  · apply Commute.add_right
    · apply nonrealResolvent_commute
    · apply nonrealResolvent_commute
  · apply Commute.add_right
    · apply nonrealResolvent_commute
    · apply nonrealResolvent_commute

end

end LinearPMap
