import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.NormalizedPeelTrace

set_option linter.style.header false

/-!
# Normalized summable two-point trace identity

The normalized diagonal trace is the ratio of the operator's Gibbs numerator to the partition
trace. Configuration types are arbitrary; summability and both nonzero denominators are explicit.
Finite fermionic and infinite bosonic occupation realizations supply these analytic conditions.
-/

namespace SecondQuantization.Common

variable {Config : Type*}

/-- Divide the summable two-point trace identity by the partition trace and exchange denominator.
The rotated double series supplies the trace interchange; no countability assumption is needed. -/
theorem normalizedTsumTrace_comp_eq_div_of_zetaCommutator
    (energy : Config → ℝ) (β q : ℝ) (ζ c : ℂ)
    (C₁ C₂ : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC₁ : heisenbergEvolve energy (-β) C₁ =
      Complex.exp ((q * (-β) : ℝ) : ℂ) • C₁)
    (hcomm : ScalarExchange.zetaCommutator ζ C₁ C₂ =
      c • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hpartition : Summable (fun n =>
      matrixCoeff (diagonalEvolution energy (-β)) n n))
    (hrotate : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp C₂) n k * matrixCoeff C₁ k n)))
    (hZ : tsumTrace (diagonalEvolution energy (-β)) ≠ 0)
    (hden : (1 : ℂ) - ζ * Complex.exp ((q * β : ℝ) : ℂ) ≠ 0) :
    tsumTrace ((diagonalEvolution energy (-β)).comp (C₁.comp C₂)) /
        tsumTrace (diagonalEvolution energy (-β)) =
      c / (1 - ζ * Complex.exp ((q * β : ℝ) : ℂ)) := by
  have hpeel := hpartition.mul_left c
  have h := normalizedTsumTrace_comp_peel energy β q ζ C₁ [(C₂, c)] hC₁
    (by simpa using hcomm)
    (by simpa only [ScalarExchange.peelSumWithCoefficients, List.map_nil, List.prod_nil,
      mul_zero, smul_zero, add_zero, Module.End.one_eq_id, LinearMap.comp_smul,
      LinearMap.comp_id, ← matrixCoeffLinear_apply, map_smul, smul_eq_mul] using hpeel)
    (by simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      using hrotate) hZ hden
  simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil,
    ScalarExchange.peelSumWithCoefficients, mul_zero, smul_zero, add_zero,
    Module.End.one_eq_id, LinearMap.comp_smul, LinearMap.comp_id, tsumTrace_smul] at h
  have hcancel :
      c * tsumTrace (diagonalEvolution energy (-β)) /
          tsumTrace (diagonalEvolution energy (-β)) = c := by
    apply (div_eq_iff hZ).2
    ring
  simpa only [hcancel] using h

end SecondQuantization.Common
