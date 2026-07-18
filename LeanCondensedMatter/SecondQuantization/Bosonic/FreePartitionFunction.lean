import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTimeEvolution
import Mathlib.Analysis.SpecificLimits.Normed

set_option linter.style.header false

/-!
# The free bosonic partition function: the one-mode geometric series

Phase B3a of Track D's bosonic line (`notes/roadmaps/second-quantization.md`): the single-mode
building block for the genuine (uncutoff) bosonic partition function `Z(β) = Σ_n e^{-βE(n)}`,
summed over *all* occupation states rather than a finite occupation-number cutoff.

For a single mode with dispersion `ε` at inverse temperature `β`, the occupation number `k` ranges
over all of `ℕ` — no Pauli exclusion caps it — so the sum over that one mode's contribution to `Z`
is the geometric series `Σ_{k=0}^∞ e^{-βkε} = (1 - e^{-βε})⁻¹`, converging exactly when `0 < βε`
(equivalently `e^{-βε} < 1`). This is the concrete bosonic convergence condition anticipated
throughout the roadmap's Phase B3 notes.

**What remains** (B3b/B3c, not yet started): the multi-mode product formula
`Z(β) = ∏ᵢ (1 - e^{-βεᵢ})⁻¹` for `[Fintype Mode]`, decomposing `freeEigenvalue`'s sum over modes
into a `tsum` over `Occupation Mode` that factors as a product of one-mode geometric series (one
per mode, via the identity proved here). Carrying that out by induction on `Mode` (`Mode = Empty`,
then `Mode = Option Mode'`) uses Mathlib's `Finsupp.optionEquiv : (Option α →₀ M) ≃ M × (α →₀ M)`
to identify `Occupation (Option Mode) ≃ ℕ × Occupation Mode`; the remaining work is the
`tsum`-over-a-product decomposition and the `Fintype.induction_empty_option` bookkeeping around
it, deferred to its own file rather than folded into this one.
-/

namespace SecondQuantization
namespace Bosonic

/-- **The one-mode bosonic Boltzmann weight**, `e^{-βkε}`, for occupation number `k` in a single
mode with dispersion `ε` at inverse temperature `β`. -/
noncomputable def oneModeBoltzmannWeight (β ε : ℝ) (k : ℕ) : ℝ :=
  Real.exp ((k : ℝ) * (-β * ε))

/-- **The one-mode partition function's defining geometric series.** Converges (`HasSum`) to
`(1 - e^{-βε})⁻¹` exactly when `0 < βε`; only the sign of the *product* `βε` matters, not the
sign of `β` or `ε` individually. -/
theorem hasSum_oneModeBoltzmannWeight {β ε : ℝ} (h : 0 < β * ε) :
    HasSum (oneModeBoltzmannWeight β ε) (1 - Real.exp (-β * ε))⁻¹ := by
  have hnorm : ‖Real.exp (-β * ε)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), Real.exp_lt_one_iff]
    linarith
  have hgeo := hasSum_geometric_of_norm_lt_one hnorm
  unfold oneModeBoltzmannWeight
  simpa only [Real.exp_nat_mul] using hgeo

theorem summable_oneModeBoltzmannWeight {β ε : ℝ} (h : 0 < β * ε) :
    Summable (oneModeBoltzmannWeight β ε) :=
  (hasSum_oneModeBoltzmannWeight h).summable

/-- **Convergence is not just sufficient but necessary**: `0 < βε` exactly characterizes
summability, matching the `HasSum`/docstring claims above word for word rather than only their
`0 < βε →` direction. -/
theorem summable_oneModeBoltzmannWeight_iff {β ε : ℝ} :
    Summable (oneModeBoltzmannWeight β ε) ↔ 0 < β * ε := by
  unfold oneModeBoltzmannWeight
  rw [show (fun k : ℕ => Real.exp ((k : ℝ) * (-β * ε))) =
        fun k : ℕ => Real.exp (-β * ε) ^ k from funext fun k => Real.exp_nat_mul _ k,
    summable_geometric_iff_norm_lt_one, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
    Real.exp_lt_one_iff]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The one-mode bosonic partition function**, `Σ_{k=0}^∞ e^{-βkε} = (1 - e^{-βε})⁻¹`. -/
theorem tsum_oneModeBoltzmannWeight {β ε : ℝ} (h : 0 < β * ε) :
    ∑' k, oneModeBoltzmannWeight β ε k = (1 - Real.exp (-β * ε))⁻¹ :=
  (hasSum_oneModeBoltzmannWeight h).tsum_eq

/-!
**Not yet done**: the one-mode bosonic occupation-number expectation `⟨n⟩ = e^{-βε}/(1 - e^{-βε})
= 1/(e^{βε} - 1)` (the Bose–Einstein distribution) — needs
`tsum_coe_mul_geometric_of_norm_lt_one` composed with `hasSum_oneModeBoltzmannWeight`'s
telescoping, analogous to `tsum_oneModeBoltzmannWeight`. Left as a future addition once the
multi-mode `normalizedWeightedDiagonal` API (B3d onward) is in place to state it against.
-/

end Bosonic
end SecondQuantization
