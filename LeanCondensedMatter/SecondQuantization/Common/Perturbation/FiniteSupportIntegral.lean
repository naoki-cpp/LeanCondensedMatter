import LeanCondensedMatter.SecondQuantization.Common.Perturbation.ReachableSupport
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
  ∑ m ∈ S, (∫ τ in a..b, f τ m) • basisState m

/-- A reconstructed coordinate inside the prescribed support is its scalar interval integral. -/
theorem finiteSupportIntervalIntegral_apply_of_mem (S : Finset Config)
    (f : ℝ → AlgebraicFock Config) (a b : ℝ) {m : Config} (hm : m ∈ S) :
    finiteSupportIntervalIntegral S f a b m = ∫ τ in a..b, f τ m := by
  classical
  rw [finiteSupportIntervalIntegral, Finsupp.finsetSum_apply]
  calc
    ∑ i ∈ S, ((∫ τ in a..b, f τ i) • basisState i) m =
        ((∫ τ in a..b, f τ m) • basisState m) m := by
      apply Finset.sum_eq_single m
      · intro k hk hkm
        simp [basisState, hkm]
      · intro hnot
        exact (hnot hm).elim
    _ = ∫ τ in a..b, f τ m := by simp [basisState]

/-- A reconstructed coordinate outside the prescribed support vanishes. -/
theorem finiteSupportIntervalIntegral_apply_of_not_mem (S : Finset Config)
    (f : ℝ → AlgebraicFock Config) (a b : ℝ) {m : Config} (hm : m ∉ S) :
    finiteSupportIntervalIntegral S f a b m = 0 := by
  classical
  rw [finiteSupportIntervalIntegral, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro k hk
  have hkm : k ≠ m := by
    intro h
    subst k
    exact hm hk
  simp [basisState, hkm]

/-- Coordinatewise reconstruction cannot create support outside the supplied finite set. -/
theorem support_finiteSupportIntervalIntegral_subset (S : Finset Config)
    (f : ℝ → AlgebraicFock Config) (a b : ℝ) :
    (finiteSupportIntervalIntegral S f a b).support ⊆ S := by
  intro m hm
  by_contra hnot
  exact (Finsupp.mem_support_iff.mp hm)
    (finiteSupportIntervalIntegral_apply_of_not_mem S f a b hnot)

/-- If every vector in the family is supported in `S`, the finite reconstruction agrees with the
coordinatewise interval integral at every configuration. -/
theorem finiteSupportIntervalIntegral_apply (S : Finset Config)
    (f : ℝ → AlgebraicFock Config) (a b : ℝ)
    (hf : ∀ τ, (f τ).support ⊆ S) (m : Config) :
    finiteSupportIntervalIntegral S f a b m = ∫ τ in a..b, f τ m := by
  classical
  by_cases hm : m ∈ S
  · exact finiteSupportIntervalIntegral_apply_of_mem S f a b hm
  · rw [finiteSupportIntervalIntegral_apply_of_not_mem S f a b hm]
    have hzero : (fun τ : ℝ => f τ m) = (0 : ℝ → ℂ) := by
      funext τ
      by_contra hne
      exact hm (hf τ (Finsupp.mem_support_iff.mpr hne))
    rw [hzero]
    exact intervalIntegral.integral_zero.symm

end Common
end SecondQuantization
