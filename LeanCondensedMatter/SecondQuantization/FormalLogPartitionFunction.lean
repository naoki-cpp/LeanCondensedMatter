import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Data.Complex.Basic

set_option linter.style.header false

/-!
# The formal logarithm of a partition function (power-series groundwork)

Phase 8 of Track D's fermionic primary line (`notes/roadmaps/second-quantization.md`): the first
piece of the *genuine* Linked Cluster Theorem — "disconnected contributions cancel in `log Z`" —
as opposed to the `IsProductWeightAcross` special case already done
(`QuantumLinkedCluster.lean`), which only covers a Hamiltonian that splits cleanly across a mode
bipartition.

This file is deliberately abstract and physics-free: it sets up `log Z` as a formal power series
in a perturbation-strength parameter `λ`, for an *arbitrary* partition-function series
`Z : PowerSeries ℂ` with `Z(0) = 1` (i.e. `Z` normalized by its zeroth-order value), using
Mathlib's `PowerSeries.log` (`log(1+X) = X - X²/2 + X³/3 - ⋯`, defined via substitution rather
than an analytic limit, so it needs no convergence hypothesis). Connecting this formal `log Z` to
an actual perturbative expansion of `traceFock (formalExpTruncation (H₀ + λ • V) N)` — where `H₀`,
`V` are genuinely non-commuting operators, so `(H₀ + λV)ⁿ` expands into a non-trivial sum over
orderings — and to Track B's connected-cluster combinatorics, is separate, harder, not-yet-started
future work. See `notes/roadmaps/second-quantization.md` for what remains.
-/

namespace SecondQuantization

open PowerSeries

/-- **The formal logarithm of a normalized partition-function series.** For `Z : PowerSeries ℂ`
with constant term `1` (i.e. `Z` already normalized by its zeroth-order value `Z(0)`), `log Z` is
the power series `log(1 + (Z - 1))`, obtained by substituting `Z - 1` into Mathlib's universal
`log(1+X)` series (`PowerSeries.log`). Well-defined purely formally: no convergence or topology is
needed, since `PowerSeries.subst` only ever inspects finitely many coefficients of `Z - 1` to
compute each coefficient of the result. -/
noncomputable def formalLogPartitionFunction (Z : PowerSeries ℂ) : PowerSeries ℂ :=
  (PowerSeries.log ℂ).subst (Z - 1)

theorem hasSubst_sub_one_of_constantCoeff_eq_one {Z : PowerSeries ℂ}
    (hZ : constantCoeff Z = 1) : HasSubst (Z - 1) :=
  HasSubst.of_constantCoeff_zero' (by simp [hZ])

/-- **`formalLogPartitionFunction` has vanishing constant term**, matching the physical picture
that `log Z(0) = log 1 = 0` once `Z` is normalized by its own zeroth-order value. -/
theorem constantCoeff_formalLogPartitionFunction {Z : PowerSeries ℂ}
    (hZ : constantCoeff Z = 1) : constantCoeff (formalLogPartitionFunction Z) = 0 := by
  rw [formalLogPartitionFunction, ← PowerSeries.coeff_zero_eq_constantCoeff,
    coeff_subst' (hasSubst_sub_one_of_constantCoeff_eq_one hZ)]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have hZ1 : constantCoeff (Z - 1) = 0 := by simp [hZ]
    have : PowerSeries.coeff 0 ((Z - 1) ^ d) = 0 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hZ1, zero_pow hd.ne']
    simp [this]

end SecondQuantization
