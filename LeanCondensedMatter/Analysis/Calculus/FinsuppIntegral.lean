import Mathlib.Data.Finsupp.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option linter.style.header false

/-!
# Coordinatewise interval integration on a fixed finite support

Finite-support functions with values in a real normed space can be integrated coordinatewise
over a prescribed finite set. This is a reconstruction of the scalar-coordinate integrals,
not a claim of Bochner integrability in a topology on the space of finitely supported functions.
-/

namespace Finsupp

variable {ι V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Coordinatewise interval integration reconstructed over a prescribed finite output support. -/
noncomputable def finiteSupportIntervalIntegral (S : Finset ι)
    (f : ℝ → (ι →₀ V)) (a b : ℝ) : (ι →₀ V) :=
  Finsupp.indicator S fun m _ => ∫ τ in a..b, f τ m

/-- Coordinatewise reconstruction cannot create support outside the supplied finite set. -/
theorem support_finiteSupportIntervalIntegral_subset (S : Finset ι)
    (f : ℝ → (ι →₀ V)) (a b : ℝ) :
    (finiteSupportIntervalIntegral S f a b).support ⊆ S := by
  change (Finsupp.indicator S (fun m (_ : m ∈ S) => ∫ τ in a..b, f τ m)).support ⊆ S
  exact Finsupp.support_indicator_subset S (fun m (_ : m ∈ S) => ∫ τ in a..b, f τ m)

/-- If every vector in the family is supported in `S`, the finite reconstruction agrees with the
coordinatewise interval integral at every index. -/
theorem finiteSupportIntervalIntegral_apply (S : Finset ι)
    (f : ℝ → (ι →₀ V)) (a b : ℝ)
    (hf : ∀ τ, (f τ).support ⊆ S) (m : ι) :
    finiteSupportIntervalIntegral S f a b m = ∫ τ in a..b, f τ m := by
  by_cases hm : m ∈ S
  · rw [finiteSupportIntervalIntegral, Finsupp.indicator_of_mem hm]
  · rw [finiteSupportIntervalIntegral, Finsupp.indicator_of_notMem hm]
    have hzero : (fun τ : ℝ => f τ m) = (0 : ℝ → V) := by
      funext τ
      by_contra hne
      exact hm (hf τ (Finsupp.mem_support_iff.mpr hne))
    rw [hzero]
    exact intervalIntegral.integral_zero.symm

end Finsupp
