import LeanCondensedMatter.Analysis.Dyson.Bounds
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option linter.style.header false

/-!
# First-variation bounds for generic Dyson evolution

This module isolates the quantitative estimate needed to differentiate the bounded Dyson evolution
with respect to its scalar coupling. After removing the zeroth and first weighted coefficients, the
remaining series starts at order two and is controlled termwise by the shifted factorial majorant.

The theorem remains in the state-independent `Analysis.Dyson` layer. Physical coupling conventions,
Planck's constant, and interaction-picture observables belong to downstream `QuantumTheory`
specializations.
-/

namespace Dyson

open Set

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The part of the bounded Dyson evolution beyond first order is controlled by the corresponding
shifted factorial-majorant series. -/
theorem norm_evolution_sub_one_add_term_one_le_of_bound
    (V : ℝ → A) {β M : ℝ}
    (hOne : ‖(1 : A)‖ ≤ 1) (hM : 0 ≤ M)
    (hV : ∀ σ ∈ Icc (0 : ℝ) β, ‖V σ‖ ≤ M)
    (lam : ℂ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) β) :
    ‖evolution V lam τ - (1 + term V lam τ 1)‖ ≤
      ∑' n : ℕ, majorant (‖lam‖ * M) τ (n + 2) := by
  have htail :
      HasSum (fun n : ℕ => term V lam τ (n + 2))
        (evolution V lam τ - ∑ n ∈ Finset.range 2, term V lam τ n) :=
    (hasSum_nat_add_iff' 2).2
      (hasSum_evolution_of_bound V hOne hM hV lam hτ)
  have hmajorant :
      Summable (fun n : ℕ => majorant (‖lam‖ * M) τ (n + 2)) :=
    (summable_nat_add_iff 2).2 (summable_majorant (‖lam‖ * M) τ)
  have hbound := htail.norm_le_of_bounded hmajorant.hasSum fun n =>
    norm_term_le_of_bound V hOne hM hV lam (n + 2) hτ
  simpa [Finset.sum_range_succ] using hbound

end
end Dyson
