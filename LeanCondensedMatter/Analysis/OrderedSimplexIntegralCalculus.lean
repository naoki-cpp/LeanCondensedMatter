import LeanCondensedMatter.Analysis.OrderedSimplexIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option linter.style.header false

/-!
# Calculus for ordered-simplex integrals

This module supplies the endpoint-calculus facts needed for the ordered-simplex shuffle identity.
For a continuous integrand, an `(n + 1)`-dimensional ordered-simplex integral is differentiable in
its upper bound; its derivative is the `n`-dimensional boundary integral obtained by fixing the
outermost time at that bound. Applying the product rule and the fundamental theorem of calculus
then splits a product of two positive-dimensional ordered-simplex integrals according to whether
its largest time belongs to the left or the right factor.
-/

namespace intervalIntegral

/-- An ordered-simplex integral of a fixed continuous integrand is continuous in its upper bound. -/
theorem continuous_orderedSimplexIntegral_bound (n : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : Continuous f) :
    Continuous (fun β : ℝ => orderedSimplexIntegral n β f) := by
  simpa using continuous_orderedSimplexIntegral_of_continuous n id
    (fun _ : ℝ => f) continuous_id (hf.comp continuous_snd)

/-- Fixing the outermost coordinate of a continuous integrand at the varying upper bound and
integrating over all remaining ordered coordinates gives a continuous function of that bound. -/
theorem continuous_orderedSimplexIntegral_boundary (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℂ) (hf : Continuous f) :
    Continuous (fun β : ℝ =>
      orderedSimplexIntegral n β (fun rest => f (Fin.cons β rest))) := by
  have hcons : Continuous
      (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2)) :=
    hf.comp (Continuous.finCons continuous_fst continuous_snd)
  exact continuous_orderedSimplexIntegral_of_continuous n id
    (fun β rest => f (Fin.cons β rest)) continuous_id hcons

/-- Every positive-dimensional ordered-simplex integral vanishes when its upper bound is zero. -/
@[simp]
theorem orderedSimplexIntegral_succ_zero_bound (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℂ) :
    orderedSimplexIntegral (n + 1) 0 f = 0 := by
  simp [orderedSimplexIntegral_succ]

-- Use the normed-space structure supplied by the real normed algebra on `ℂ` throughout the
-- derivative statements below. This keeps the fundamental theorem and the product rule on the
-- same instance.
local instance : NormedSpace ℝ ℂ := NormedAlgebra.toNormedSpace ℂ

/-- Fundamental theorem of calculus for an ordered-simplex integral: differentiating in the upper
bound fixes the outermost time coordinate at that bound. -/
theorem hasDerivAt_orderedSimplexIntegral_succ (n : ℕ)
    (f : (Fin (n + 1) → ℝ) → ℂ) (hf : Continuous f) (β : ℝ) :
    HasDerivAt (fun t : ℝ => orderedSimplexIntegral (n + 1) t f)
      (orderedSimplexIntegral n β (fun rest => f (Fin.cons β rest))) β := by
  have hboundary := continuous_orderedSimplexIntegral_boundary n f hf
  simpa only [orderedSimplexIntegral_succ] using
    (hboundary.integral_hasStrictDerivAt 0 β).hasDerivAt

/-- Split a product of two positive-dimensional ordered-simplex integrals by the component that
contains the largest time. This is the analytic recurrence underlying the binary shuffle identity:
the first summand fixes the left outermost time, while the second fixes the right outermost time. -/
theorem orderedSimplexIntegral_succ_mul_succ (m n : ℕ) (β : ℝ)
    (f : (Fin (m + 1) → ℝ) → ℂ) (g : (Fin (n + 1) → ℝ) → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    orderedSimplexIntegral (m + 1) β f * orderedSimplexIntegral (n + 1) β g =
      ∫ t in (0 : ℝ)..β,
        orderedSimplexIntegral m t (fun rest => f (Fin.cons t rest)) *
            orderedSimplexIntegral (n + 1) t g +
          orderedSimplexIntegral (m + 1) t f *
            orderedSimplexIntegral n t (fun rest => g (Fin.cons t rest)) := by
  let F : ℝ → ℂ := fun t =>
    orderedSimplexIntegral (m + 1) t f * orderedSimplexIntegral (n + 1) t g
  let F' : ℝ → ℂ := fun t =>
    orderedSimplexIntegral m t (fun rest => f (Fin.cons t rest)) *
        orderedSimplexIntegral (n + 1) t g +
      orderedSimplexIntegral (m + 1) t f *
        orderedSimplexIntegral n t (fun rest => g (Fin.cons t rest))
  have hderiv : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    simpa [F, F'] using
      (hasDerivAt_orderedSimplexIntegral_succ m f hf t).mul
        (hasDerivAt_orderedSimplexIntegral_succ n g hg t)
  have hF' : Continuous F' := by
    dsimp [F']
    exact ((continuous_orderedSimplexIntegral_boundary m f hf).mul
      (continuous_orderedSimplexIntegral_bound (n + 1) g hg)).add
      ((continuous_orderedSimplexIntegral_bound (m + 1) f hf).mul
        (continuous_orderedSimplexIntegral_boundary n g hg))
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := β) (f := F) (f' := F')
    (fun t _ => hderiv t) (hF'.intervalIntegrable 0 β)
  simpa [F, F'] using hfund.symm

end intervalIntegral
