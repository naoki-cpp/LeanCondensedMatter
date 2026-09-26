import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirst
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.KMSRotation

set_option linter.style.header false

/-!
# Trace-level peel-first identity from KMS cyclicity

Combining the operator-algebra peel identity with KMS cyclicity for an arbitrary-length remaining
product gives a self-referential trace equation. Moving `C₁` from the end of the product back to
the front contributes `w₁ = exp(q₁ β)`, while the exchange algebra contributes
`ζ ^ l.length`, yielding

`(1 - ζ^{l.length} w₁) Tr[e^{-βH₀}(C₁ B₁⋯Bₖ)]
  = Tr[e^{-βH₀} peelSum ζ [(B₁,c₁),…,(Bₖ,cₖ)]]`.

The module proves both a finite-configuration trace form and a `tsum` form guarded by explicit
summability hypotheses. The latter applies to bosonic occupation spaces, which remain infinite even
for finitely many modes. Summability of the rotated diagonal tail follows from the corresponding
double-series hypothesis.

`PeelTermsIndexed` supplies the position-indexed form of `peelSum` used to match individual
terms with perfect-pairing recursion.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **The trace-level peel-first identity**: `Common.traceFock_diagonalEvolution_comp_rotate`
applied to the whole remaining product `B₁⋯Bₖ` (rotating `C₁` from the end back to the front)
combined with `comp_prod_eq_of_zetaCommutator`'s operator identity, solving the resulting
self-referential equation for `Tr[e^{-βH₀}(C₁B₁⋯Bₖ)]`. -/
theorem traceFock_diagonalEvolution_comp_peel [Fintype Config]
    (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, ScalarExchange.zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        traceFock ((diagonalEvolution energy (-β)).comp
          (C1.comp (List.prod (l.map Prod.fst)))) =
      traceFock ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) := by
  have hopeq := comp_prod_eq_of_zetaCommutator ζ C1 l hcomm
  have hrot := traceFock_diagonalEvolution_comp_rotate energy β q1
    (List.prod (l.map Prod.fst)) C1 hC1
  have hstep : traceFock ((diagonalEvolution energy (-β)).comp
      (C1.comp (List.prod (l.map Prod.fst)))) =
      traceFock ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) +
        ζ ^ l.length * traceFock ((diagonalEvolution energy (-β)).comp
          ((List.prod (l.map Prod.fst)).comp C1)) := by
    conv_lhs => rw [hopeq]
    simp only [LinearMap.comp_add, LinearMap.comp_smul, map_add, map_smul, smul_eq_mul]
  rw [hrot, smul_eq_mul] at hstep
  linear_combination hstep

/-- **The `tsum` trace-level peel-first identity**: the `[Fintype Config]`-free analogue of
`traceFock_diagonalEvolution_comp_peel`, given the same `ζ`-commutator and KMS eigenvalue-shift
hypotheses plus explicit summability of `peelSum`'s own diagonal series (`hPeel`) and of the
rotation's double series (`hRotate`). Summability of the rotated tail's diagonal series (`n ↦
(e^{-βH₀}(B₁⋯Bₖ)C₁)ₙₙ`) is *not* a separate hypothesis — it follows from `hRotate` alone via
`summable_matrixCoeff_diag_comp_of_summable_uncurry`, mirroring `TwoPoint.lean`'s own `tsum`
theorem. -/
theorem tsumTrace_diagonalEvolution_comp_peel
    (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, ScalarExchange.zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hPeel : Summable (fun n =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) n n))
    (hRotate : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp (List.prod (l.map Prod.fst))) n k *
        matrixCoeff C1 k n))) :
    (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        tsumTrace ((diagonalEvolution energy (-β)).comp
          (C1.comp (List.prod (l.map Prod.fst)))) =
      tsumTrace ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) := by
  have hopeq := comp_prod_eq_of_zetaCommutator ζ C1 l hcomm
  have hrot := tsumTrace_diagonalEvolution_comp_rotate energy β q1
    (List.prod (l.map Prod.fst)) C1 hC1 hRotate
  have hSummDCjC1 : Summable (fun n => matrixCoeff
      ((diagonalEvolution energy (-β)).comp ((List.prod (l.map Prod.fst)).comp C1)) n n) := by
    have := summable_matrixCoeff_diag_comp_of_summable_uncurry
      ((diagonalEvolution energy (-β)).comp (List.prod (l.map Prod.fst))) C1 hRotate
    rwa [LinearMap.comp_assoc] at this
  have hDcomm : (diagonalEvolution energy (-β)).comp (C1.comp (List.prod (l.map Prod.fst))) =
      (diagonalEvolution energy (-β)).comp (peelSum ζ l) +
        ζ ^ l.length • ((diagonalEvolution energy (-β)).comp
          ((List.prod (l.map Prod.fst)).comp C1)) := by
    rw [hopeq, LinearMap.comp_add, LinearMap.comp_smul]
  have hpoint : (fun n => matrixCoeff ((diagonalEvolution energy (-β)).comp
      (C1.comp (List.prod (l.map Prod.fst)))) n n) =
      fun n => matrixCoeff ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) n n +
        ζ ^ l.length * matrixCoeff ((diagonalEvolution energy (-β)).comp
          ((List.prod (l.map Prod.fst)).comp C1)) n n := by
    funext n
    rw [hDcomm]
    simpa only [← matrixCoeffLinear_apply, map_add, map_smul, smul_eq_mul]
  have hstep : tsumTrace ((diagonalEvolution energy (-β)).comp
      (C1.comp (List.prod (l.map Prod.fst)))) =
      tsumTrace ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) +
        ζ ^ l.length * tsumTrace ((diagonalEvolution energy (-β)).comp
          ((List.prod (l.map Prod.fst)).comp C1)) := by
    rw [tsumTrace, tsumTrace, tsumTrace, hpoint,
      (hPeel.hasSum.add ((hSummDCjC1.mul_left (ζ ^ l.length)).hasSum)).tsum_eq, tsum_mul_left]
  rw [hrot, smul_eq_mul] at hstep
  linear_combination hstep

end Common
end SecondQuantization
