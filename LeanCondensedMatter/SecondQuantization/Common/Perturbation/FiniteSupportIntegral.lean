import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ReachableSupport
import Mathlib.Data.Finsupp.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Coefficientwise integration on a finite algebraic-Fock support

A family of algebraic-Fock vectors whose values are all supported in one fixed finite set can be
integrated coordinatewise and reconstructed inside the same algebraic-Fock space.  The ambient
configuration type may be infinite: only the supplied finite support is enumerated.

This is an algebraic reconstruction boundary.  It does not assert Bochner integrability in a
completed Fock space, boundedness of the underlying operators, or convergence of an infinite Dyson
series.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- Coordinatewise interval integration reconstructed over a prescribed finite output support. -/
noncomputable def finiteSupportIntervalIntegral (S : Finset Config)
    (f : ℝ → AlgebraicFock Config) (a b : ℝ) : AlgebraicFock Config :=
  Finsupp.indicator S fun m _ => ∫ τ in a..b, f τ m

/-- Coordinatewise reconstruction cannot create support outside the supplied finite set. -/
theorem support_finiteSupportIntervalIntegral_subset (S : Finset Config)
    (f : ℝ → AlgebraicFock Config) (a b : ℝ) :
    (finiteSupportIntervalIntegral S f a b).support ⊆ S := by
  change (Finsupp.indicator S (fun m (_ : m ∈ S) => ∫ τ in a..b, f τ m)).support ⊆ S
  exact Finsupp.support_indicator_subset S (fun m (_ : m ∈ S) => ∫ τ in a..b, f τ m)

/-- If every vector in the family is supported in `S`, the finite reconstruction agrees with the
coordinatewise interval integral at every configuration. -/
theorem finiteSupportIntervalIntegral_apply (S : Finset Config)
    (f : ℝ → AlgebraicFock Config) (a b : ℝ)
    (hf : ∀ τ, (f τ).support ⊆ S) (m : Config) :
    finiteSupportIntervalIntegral S f a b m = ∫ τ in a..b, f τ m := by
  by_cases hm : m ∈ S
  · rw [finiteSupportIntervalIntegral, Finsupp.indicator_of_mem hm]
  · rw [finiteSupportIntervalIntegral, Finsupp.indicator_of_notMem hm]
    have hzero : (fun τ : ℝ => f τ m) = (0 : ℝ → ℂ) := by
      funext τ
      by_contra hne
      exact hm (hf τ (Finsupp.mem_support_iff.mpr hne))
    rw [hzero]
    exact intervalIntegral.integral_zero.symm

end Common
end SecondQuantization
