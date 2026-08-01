import LeanCondensedMatter.SecondQuantization.Common.Perturbation.AnalyticDysonTrace
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.ContinuousDyson
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries

set_option linter.style.header false

/-!
# The analytic finite-dimensional fermionic partition function

For finitely many fermionic modes, the interacting Gibbs operator is a Banach-algebra exponential
in the continuous finite-dimensional operator realization. Its trace is the genuine analytic
partition function. The convergent interaction-picture Dyson sum is identified coefficientwise
with the existing formal `dysonPartitionCoeff` API.
-/

namespace SecondQuantization

noncomputable section

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- The genuine finite-dimensional interacting partition function
`Tr exp(-β (H₀ + λV))`. -/
noncomputable def analyticDysonPartitionFunction (ε : Mode → ℝ) (β : ℝ)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (lam : ℂ) : ℂ :=
  Common.finiteOperatorTrace
    (NormedSpace.exp ((-β) • continuousInteractingHamiltonian ε V lam))

omit [LinearOrder Mode] in
/-- The analytic partition function is the thermal trace of the interaction-picture Dyson
operator. -/
theorem analyticDysonPartitionFunction_eq_trace_analyticDysonEvolution
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (lam : ℂ) :
    analyticDysonPartitionFunction ε β V lam =
      Common.finiteOperatorTrace
        ((continuousImaginaryTimeEvolveFree ε (-β)).comp
          (analyticDysonEvolution ε V β lam)) := by
  rw [analyticDysonPartitionFunction,
    continuousImaginaryTimeEvolveFree_neg_mul_analyticDysonEvolution_eq_exp ε V hβ lam]

omit [LinearOrder Mode] in
/-- The existing fermionic Dyson partition coefficients sum to the genuine interacting partition
function. -/
theorem hasSum_dysonPartitionCoeff_eq_analyticDysonPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (lam : ℂ) :
    HasSum (fun n : ℕ => lam ^ n * dysonPartitionCoeff ε β V n)
      (analyticDysonPartitionFunction ε β V lam) := by
  have h := Common.hasSum_dysonTraceCoeff_eq_trace_analyticDysonEvolution
    (fermionEnergy ε) hβ V lam
  have hterms :
      (fun n : ℕ => lam ^ n * Common.dysonTraceCoeff (fermionEnergy ε) β V n) =
      (fun n : ℕ => lam ^ n * dysonPartitionCoeff ε β V n) := by
    funext n
    rw [dysonPartitionCoeff_eq_dysonTraceCoeff]
  rw [hterms]
  rw [analyticDysonPartitionFunction_eq_trace_analyticDysonEvolution ε hβ V lam]
  exact h

omit [LinearOrder Mode] in
/-- `dysonPartitionSeries` evaluates by a genuine convergent `tsum` to the analytic partition
function. -/
theorem tsum_dysonPartitionCoeff_eq_analyticDysonPartitionFunction
    (ε : Mode → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    (V : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) (lam : ℂ) :
    (∑' n : ℕ, lam ^ n * dysonPartitionCoeff ε β V n) =
      analyticDysonPartitionFunction ε β V lam :=
  (hasSum_dysonPartitionCoeff_eq_analyticDysonPartitionFunction ε hβ V lam).tsum_eq

end
end SecondQuantization
