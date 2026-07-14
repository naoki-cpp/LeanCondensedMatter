import LeanCondensedMatter.QuantumTheory.DensityOperatorTraceClass

/-!
# Energy expectation value via trace-class operators (infinite dimensions)

Extends the energy expectation value `Tr[ρĤ]` (`QuantumTheory.energyExpValue` in
`QuantumTheory/Entropy.lean`) beyond finite-dimensional `H`.

**This file is additive, not a replacement**: the finite-dimensional `QuantumTheory.energyExpValue`
and everything built on it are untouched.

**Why not `ContinuousLinearMap.trace (ρ.op ∘L Hop.1)` directly.** The finite-dimensional
definition is `(LinearMap.trace ℂ H (ρ.1 ∘L Hop.1)).re`. The naive infinite-dimensional analogue
would use `ContinuousLinearMap.trace` (`Analysis/CompactSelfAdjoint.lean`) on `ρ.op ∘L Hop.1`, but
that trace is only meaningful for *compact self-adjoint* operators, and a composition of two
self-adjoint operators is self-adjoint only when they commute — exactly the same obstacle already
documented for the Born-rule `prob` in `DensityOperatorTraceClass.lean` (`E_m ∘ ρ need not be
self-adjoint even when E_m, ρ both are`). So, as with `prob`, `energyExpValue` below is instead
defined directly from `ρ`'s own eigendecomposition `ρ = Σᵢ λᵢ |eᵢ⟩⟨eᵢ|`
(`ContinuousLinearMap.eigenvectorFamily`), which never needs `Hop.1` itself to be trace-class or
compact: `Σᵢ λᵢ ⟪eᵢ, Ĥ eᵢ⟫`. This is the same quantity as the finite-dimensional
`Tr[ρĤ] = Σₘ p_m ⟨e_m|Ĥ|e_m⟩` (matching `QuantumTheory.energyExpValue_eq_sum`, specialized to a
single eigenbasis — the one for `ρ` — instead of a double sum over both `ρ`'s and `Hop`'s
eigenbases), so no new hypothesis on `Hop` is required beyond it being a general `Observable H`.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Convergence of the series defining `energyExpValue`, via comparison against `‖Hop.1‖ * |λᵢ|`
— the same bound used for `summable_prob_term` (`Hop.1` plays the role of a single POVM effect
`P.E m`). -/
theorem summable_energyExpValue_term (ρ : DensityOperator H) (Hop : Observable H) :
    Summable (fun a : EigenvectorIndex ρ.op => (a.1.1 : ℂ) *
      (inner ℂ (eigenvectorFamily ρ.compact a) (Hop.1 (eigenvectorFamily ρ.compact a)) : ℂ)) := by
  have hnorm := eigenvectorFamily_norm_eq_one ρ
  refine Summable.of_norm_bounded (ρ.traceClass.mul_right ‖Hop.1‖) fun a => ?_
  have hle : ‖(inner ℂ (eigenvectorFamily ρ.compact a) (Hop.1 (eigenvectorFamily ρ.compact a)) :
      ℂ)‖ ≤ ‖Hop.1‖ :=
    calc ‖(inner ℂ (eigenvectorFamily ρ.compact a) (Hop.1 (eigenvectorFamily ρ.compact a)) : ℂ)‖
        ≤ ‖eigenvectorFamily ρ.compact a‖ * ‖Hop.1 (eigenvectorFamily ρ.compact a)‖ :=
          norm_inner_le_norm _ _
      _ ≤ ‖eigenvectorFamily ρ.compact a‖ * (‖Hop.1‖ * ‖eigenvectorFamily ρ.compact a‖) := by
          gcongr; exact Hop.1.le_opNorm _
      _ = ‖Hop.1‖ := by rw [hnorm a]; ring
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)

/-- **The expectation value `Tr[ρĤ]` of the Hamiltonian `Hop` in the state `ρ`
(infinite-dimensional).** Computed from `ρ`'s own eigendecomposition (see the module docstring
for why, unlike the finite-dimensional `QuantumTheory.energyExpValue`, this does not go through
`ContinuousLinearMap.trace (ρ.op ∘L Hop.1)`). -/
noncomputable def energyExpValue (ρ : DensityOperator H) (Hop : Observable H) : ℝ :=
  (∑' a : EigenvectorIndex ρ.op, (a.1.1 : ℂ) *
    (inner ℂ (eigenvectorFamily ρ.compact a) (Hop.1 (eigenvectorFamily ρ.compact a)) : ℂ)).re

end QuantumTheory.TraceClass
