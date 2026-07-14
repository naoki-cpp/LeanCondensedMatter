import LeanCondensedMatter.QuantumTheory.EnergyExpValueTraceClass
import LeanCondensedMatter.QuantumTheory.GibbsStateTraceClass
import LeanCondensedMatter.QuantumTheory.EntropyTraceClass
import LeanCondensedMatter.Analysis.PeierlsBogoliubov

/-!
# The Gibbs–Klein / Helmholtz free-energy inequality (infinite dimensions)

Extends `QuantumTheory.helmholtzFreeEnergy_ge` (`QuantumTheory/Entropy.lean`) beyond
finite-dimensional `H`: for any density operator `ρ`, Hamiltonian `Hop`, and inverse temperature
`β > 0`, the Helmholtz free energy `F[ρ] = Tr[ρĤ] - (1/β)·S[ρ]` is bounded below by
`-(1/β)·ln Z(β)`, the free energy of the (unnormalized) Gibbs operator `e^{-βH}`'s own state.

**This file is additive, not a replacement.**

See the file docstring of `LeanCondensedMatter/Analysis/PeierlsBogoliubov.lean` and the roadmap
notes (`notes/roadmaps/quantum-theory-foundations.md`, `notes/roadmaps/operator-algebra.md`) for
the full derivation this file implements.
-/

namespace QuantumTheory.TraceClass

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Gibbs' scalar inequality.** For `x ≥ 0` and `y > 0`,
`-x ln x + x - y ≤ -x ln y`. The key elementary convexity fact (of `t ↦ t ln t - t`) driving the
Gibbs–Klein argument, reduced here to `Real.log_le_sub_one_of_pos` applied to `y / x`. -/
theorem gibbs_scalar_ineq (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    Real.negMulLog x + x - y ≤ -x * Real.log y := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · simp only [Real.negMulLog, ← hx0]
    nlinarith
  · have hxy : 0 < y / x := div_pos hy hx0
    have hlog := Real.log_le_sub_one_of_pos hxy
    rw [Real.log_div hy.ne' hx0.ne'] at hlog
    have hcancel : x * (y / x) = y := by field_simp
    have hmul := mul_le_mul_of_nonneg_left hlog hx0.le
    simp only [Real.negMulLog]
    nlinarith [hmul, hcancel]

/-- **A density operator's eigenvalues are at most `1`.** From `Σᵢ pᵢ = 1` and `pᵢ ≥ 0`, each
`pᵢ` is at most the total. Needed for `Real.negMulLog_nonneg`. -/
theorem eigenvalue_le_one (ρ : DensityOperator H) (a : EigenvectorIndex ρ.op) : a.1.1 ≤ 1 := by
  have hsum : Summable (fun b : EigenvectorIndex ρ.op => b.1.1) :=
    ρ.traceClass.congr (fun b => abs_of_nonneg (eigenvalue_nonneg ρ b))
  have hle := hsum.le_tsum a (fun j _ => eigenvalue_nonneg ρ j)
  have heq : ∑' b : EigenvectorIndex ρ.op, b.1.1 = 1 := ρ.trace_eq_one
  rwa [heq] at hle

end QuantumTheory.TraceClass
