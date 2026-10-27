import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace

set_option linter.style.header false

/-!
# Normalized summable Bloch–de Dominicis peel

The configuration-general trace peel identity can be divided by the nonzero partition
trace and exchange denominator. This isolates the normalization step from the finite Gibbs
implementation. Summability of the peeled diagonal and of the double series used for KMS
rotation remains explicit; no `Fintype` assumption on the configuration type is needed.
-/

namespace SecondQuantization.Common

variable {Config : Type*}

/-- Normalize the summable trace peel by a nonzero partition trace. The finite Gibbs
peel is a specialization of this identity, with summability automatic on finite
configuration types. -/
theorem normalizedTsumTrace_comp_peel
    (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, ScalarExchange.zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hPeel : Summable (fun n =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp
        (ScalarExchange.peelSumWithCoefficients ζ l)) n n))
    (hRotate : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp (List.prod (l.map Prod.fst))) n k *
        matrixCoeff C1 k n)))
    (hZ : tsumTrace (diagonalEvolution energy (-β)) ≠ 0)
    (hne : (1 : ℂ) - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ) ≠ 0) :
    tsumTrace ((diagonalEvolution energy (-β)).comp
        (C1.comp (List.prod (l.map Prod.fst)))) /
        tsumTrace (diagonalEvolution energy (-β)) =
      (tsumTrace ((diagonalEvolution energy (-β)).comp
        (ScalarExchange.peelSumWithCoefficients ζ l)) /
        tsumTrace (diagonalEvolution energy (-β))) /
        (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) := by
  have h := tsumTrace_diagonalEvolution_comp_peel
    energy β q1 ζ C1 l hC1 hcomm hPeel hRotate
  apply (div_eq_div_iff hZ hne).2
  rw [div_mul_cancel₀ _ hZ]
  simpa only [mul_comm] using h

end SecondQuantization.Common
