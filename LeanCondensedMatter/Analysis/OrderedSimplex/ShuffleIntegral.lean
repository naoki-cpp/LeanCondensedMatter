import LeanCondensedMatter.Analysis.OrderedSimplex.Calculus
import LeanCondensedMatter.Analysis.OrderedSimplex.MeasurableProductSplit

set_option linter.style.header false

/-!
# Binary ordered-simplex shuffle integrals

The product of two ordered-simplex integrals is a sum over all order-preserving interleavings of
their time coordinates. This module packages that sum recursively, splitting the interleavings by
whether their outermost (largest) time comes from the left or right factor.

The recursive definition deliberately precedes an explicit finite shuffle type. It isolates the
analytic identity from the later combinatorial task of identifying this recursion with a concrete
sum over order-preserving shuffle equivalences and, ultimately, diagram component shuffles.
-/

namespace intervalIntegral

/-- The recursively accumulated integral over every binary order-preserving shuffle.

When either side has dimension zero there is only one shuffle. In positive dimensions, shuffles are
partitioned by whether the outermost time belongs to the left or right factor. -/
noncomputable def orderedSimplexShuffleIntegral :
    ∀ (m n : ℕ), ℝ → ((Fin m → ℝ) → ℂ) → ((Fin n → ℝ) → ℂ) → ℂ
  | 0, n, β, f, g => f Fin.elim0 * orderedSimplexIntegral n β g
  | m + 1, 0, β, f, g => orderedSimplexIntegral (m + 1) β f * g Fin.elim0
  | m + 1, n + 1, β, f, g =>
      ∫ t in (0 : ℝ)..β,
        orderedSimplexShuffleIntegral m (n + 1) t
            (fun rest => f (Fin.cons t rest)) g +
          orderedSimplexShuffleIntegral (m + 1) n t f
            (fun rest => g (Fin.cons t rest))
termination_by m n => m + n

@[simp]
theorem orderedSimplexShuffleIntegral_zero_left (n : ℕ) (β : ℝ)
    (f : (Fin 0 → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ) :
    orderedSimplexShuffleIntegral 0 n β f g =
      f Fin.elim0 * orderedSimplexIntegral n β g := by
  rw [orderedSimplexShuffleIntegral]

@[simp]
theorem orderedSimplexShuffleIntegral_zero_right (m : ℕ) (β : ℝ)
    (f : (Fin (m + 1) → ℝ) → ℂ) (g : (Fin 0 → ℝ) → ℂ) :
    orderedSimplexShuffleIntegral (m + 1) 0 β f g =
      orderedSimplexIntegral (m + 1) β f * g Fin.elim0 := by
  rw [orderedSimplexShuffleIntegral]

/-- Binary shuffle identity for measurable locally bounded integrands. -/
theorem orderedSimplexShuffleIntegral_eq_mul_of_measurableLocallyBounded :
    ∀ (m n : ℕ) (β : ℝ) (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ),
      MeasurableLocallyBounded f → MeasurableLocallyBounded g →
      orderedSimplexShuffleIntegral m n β f g =
        orderedSimplexIntegral m β f * orderedSimplexIntegral n β g
  | 0, n, β, f, g, _hf, _hg => by
      simp
  | m + 1, 0, β, f, g, _hf, _hg => by
      simp
  | m + 1, n + 1, β, f, g, hf, hg => by
      rw [orderedSimplexShuffleIntegral]
      have hleft : ∀ t : ℝ,
          orderedSimplexShuffleIntegral m (n + 1) t
              (fun rest => f (Fin.cons t rest)) g =
            orderedSimplexIntegral m t (fun rest => f (Fin.cons t rest)) *
              orderedSimplexIntegral (n + 1) t g := by
        intro t
        exact orderedSimplexShuffleIntegral_eq_mul_of_measurableLocallyBounded
          m (n + 1) t (fun rest => f (Fin.cons t rest)) g (hf.finCons t) hg
      have hright : ∀ t : ℝ,
          orderedSimplexShuffleIntegral (m + 1) n t f
              (fun rest => g (Fin.cons t rest)) =
            orderedSimplexIntegral (m + 1) t f *
              orderedSimplexIntegral n t (fun rest => g (Fin.cons t rest)) := by
        intro t
        exact orderedSimplexShuffleIntegral_eq_mul_of_measurableLocallyBounded
          (m + 1) n t f (fun rest => g (Fin.cons t rest)) hf (hg.finCons t)
      simp_rw [hleft, hright]
      exact
        (orderedSimplexIntegral_succ_mul_succ_of_measurableLocallyBounded
          m n β f g hf hg).symm
termination_by m n => m + n

/-- Binary shuffle identity: the recursively accumulated contribution of all order-preserving
interleavings equals the product of the two component ordered-simplex integrals. -/
theorem orderedSimplexShuffleIntegral_eq_mul
    (m n : ℕ) (β : ℝ)
    (f : (Fin m → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    orderedSimplexShuffleIntegral m n β f g =
      orderedSimplexIntegral m β f * orderedSimplexIntegral n β g :=
  orderedSimplexShuffleIntegral_eq_mul_of_measurableLocallyBounded
    m n β f g (intervalIntegral.Continuous.measurableLocallyBounded hf)
      (intervalIntegral.Continuous.measurableLocallyBounded hg)

end intervalIntegral
