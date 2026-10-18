import LeanCondensedMatter.Analysis.ScalarExchange.Peel
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.KMSRotation

set_option linter.style.header false

/-!
# Trace-level peel-first identity from KMS cyclicity

Combining the generic scalar-exchange product identity with KMS cyclicity for an arbitrary-length
remaining product gives a self-referential trace equation. Moving `C₁` from the end of the product back to
the front contributes `w₁ = exp(q₁ β)`, while the exchange algebra contributes
`ζ ^ l.length`, yielding

`(1 - ζ^{l.length} w₁) Tr[e^{-βH₀}(C₁ B₁⋯Bₖ)]
  = Tr[e^{-βH₀} ScalarExchange.peelSumWithCoefficients ζ [(B₁,c₁),…,(Bₖ,cₖ)]]`.

The identity is expressed through `tsumTrace` with explicit summability hypotheses, independently
of configuration cardinality. Finite Gibbs expectations specialize it through automatic summability
and the finite trace-coordinate bridge; infinite bosonic occupation spaces provide convergence proofs.
Summability of the rotated diagonal tail follows from the corresponding double-series hypothesis.

`ScalarExchange.peelSumWithCoefficients_eq_sum` supplies the position-indexed form used to
match individual exchange terms with perfect-pairing recursion.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- The configuration-general trace-level peel-first identity. It requires the scalar-exchange
relations and the imaginary-time eigenvalue-shift equation, together with explicit summability
of the peeled diagonal (`hPeel`) and the rotated double series (`hRotate`). Summability of the
rotated tail's diagonal is derived from `hRotate` by
`summable_matrixCoeff_diag_comp_of_summable_uncurry`. -/
theorem tsumTrace_diagonalEvolution_comp_peel
    (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, ScalarExchange.zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hPeel : Summable (fun n =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp (ScalarExchange.peelSumWithCoefficients ζ l)) n n))
    (hRotate : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp (List.prod (l.map Prod.fst))) n k *
        matrixCoeff C1 k n))) :
    (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        tsumTrace ((diagonalEvolution energy (-β)).comp
          (C1.comp (List.prod (l.map Prod.fst)))) =
      tsumTrace ((diagonalEvolution energy (-β)).comp (ScalarExchange.peelSumWithCoefficients ζ l)) := by
  have hExchange : ∀ p ∈ l,
      C1 * p.1 = p.2 • (1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) +
        ζ • (p.1 * C1) := by
    intro p hp
    have hcomm' : C1 * p.1 - ζ • (p.1 * C1) =
        p.2 • (1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
      simpa only [ScalarExchange.zetaCommutator, Module.End.mul_eq_comp,
        Module.End.one_eq_id] using hcomm p hp
    exact (sub_eq_iff_eq_add).mp hcomm'
  have hopeq : C1.comp ((l.map Prod.fst).prod) =
      ScalarExchange.peelSumWithCoefficients ζ l +
        ζ ^ l.length • ((l.map Prod.fst).prod.comp C1) := by
    simpa only [Module.End.mul_eq_comp, Module.End.one_eq_id] using
      ScalarExchange.mul_prod_eq_peelSumWithCoefficients ζ C1 l hExchange
  have hrot := tsumTrace_diagonalEvolution_comp_rotate energy β q1
    (List.prod (l.map Prod.fst)) C1 hC1 hRotate
  have hSummDCjC1 : Summable (fun n => matrixCoeff
      ((diagonalEvolution energy (-β)).comp ((List.prod (l.map Prod.fst)).comp C1)) n n) := by
    have := summable_matrixCoeff_diag_comp_of_summable_uncurry
      ((diagonalEvolution energy (-β)).comp (List.prod (l.map Prod.fst))) C1 hRotate
    rwa [LinearMap.comp_assoc] at this
  have hscaled : Summable (fun n =>
      matrixCoeff (ζ ^ l.length • ((diagonalEvolution energy (-β)).comp
        ((List.prod (l.map Prod.fst)).comp C1))) n n) := by
    simpa only [← matrixCoeffLinear_apply, map_smul, smul_eq_mul] using
      hSummDCjC1.mul_left (ζ ^ l.length)
  have hstep : tsumTrace ((diagonalEvolution energy (-β)).comp
      (C1.comp (List.prod (l.map Prod.fst)))) =
      tsumTrace ((diagonalEvolution energy (-β)).comp (ScalarExchange.peelSumWithCoefficients ζ l)) +
        ζ ^ l.length * tsumTrace ((diagonalEvolution energy (-β)).comp
          ((List.prod (l.map Prod.fst)).comp C1)) := by
    rw [hopeq, LinearMap.comp_add, LinearMap.comp_smul,
      tsumTrace_add hPeel hscaled, tsumTrace_smul]
  rw [hrot, smul_eq_mul] at hstep
  linear_combination hstep

end Common
end SecondQuantization
