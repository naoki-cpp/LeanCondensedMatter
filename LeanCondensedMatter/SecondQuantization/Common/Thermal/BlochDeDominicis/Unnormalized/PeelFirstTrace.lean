import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirst
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.KMSRotation

set_option linter.style.header false

/-!
# The trace-level peel-first identity: `PeelFirst.lean` + KMS cyclicity

Wraps `Common/Thermal/BlochDeDominicis/Unnormalized/PeelFirst.lean`'s pure operator-algebra peel identity
(`comp_prodComp_eq_of_zetaCommutator`) in the trace-level KMS cyclicity step
(`Common.traceFock_diagonalEvolution_comp_rotate`), the way
`Common/Thermal/BlochDeDominicis/Unnormalized/FourPointReduction.lean` does for the hand-unrolled
3-operator case — this is that same strategy, but for an arbitrary-length remaining product, so
`FourPointReduction.lean`'s theorem is now a special case (`l := [(C2, c12), (C3, c13), (C4,
c14)]`, not yet stated as such here).

Solving the resulting self-referential trace equation (rotating `C₁` from the end of the product
back to the front, picking up `w₁ := e^{q₁β}`, and matching the `ζ^{l.length}` power the peel
identity produces) gives

`(1 - ζ^{l.length}w₁) Tr[e^{-βH₀}(C₁·B₁⋯Bₖ)] = Tr[e^{-βH₀}·peelSum ζ [(B₁,c₁),…,(Bₖ,cₖ)]]`

Both a `[Fintype Config]` (`traceFock_diagonalEvolution_comp_peel`) and a `tsum`,
summability-hypothesis-gated (`tsumTrace_diagonalEvolution_comp_peel`) form are proved — the
bosonic line's `Occupation Mode := Mode →₀ ℕ` is genuinely infinite even for a finite mode set, so
only the `tsum` form applies there, mirroring `TwoPoint.lean`'s own finite/`tsum` pair. The
rotated tail's diagonal-series summability isn't a separate hypothesis — it follows from the
double-series hypothesis alone via `summable_matrixCoeff_diag_comp_of_summable_uncurry`, the same
way `TwoPoint.lean`'s `tsum` theorem derives it.

**Left un-reduced on the right** — *unlike* `FourPointReduction.lean`, which does expand its
right side down to a sum of `traceFock`-of-remaining-*pairs* terms (`c₁₂Tr[D(C₃C₄)] +
ζc₁₃Tr[D(C₂C₄)] + ζ²c₁₄Tr[D(C₂C₃)]`). Here `peelSum`'s value is *not* further decomposed at
all — even one level short of `FourPointReduction`'s own reduction — since `peelSum` is defined
recursively rather than as a closed sum, and unfolding it against `traceFock_add`/`_smul`
recursively for an arbitrary-length list is deferred to whenever the general induction needs that
form to match term-by-term against `Common.BlochDeDominicis.Pairing`.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **The trace-level peel-first identity**: `Common.traceFock_diagonalEvolution_comp_rotate`
applied to the whole remaining product `B₁⋯Bₖ` (rotating `C₁` from the end back to the front)
combined with `comp_prodComp_eq_of_zetaCommutator`'s operator identity, solving the resulting
self-referential equation for `Tr[e^{-βH₀}(C₁B₁⋯Bₖ)]`. -/
theorem traceFock_diagonalEvolution_comp_peel [Fintype Config]
    (energy : Config → ℝ) (β q1 : ℝ) (ζ : ℂ)
    (C1 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (l : List ((AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) × ℂ))
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : ∀ p ∈ l, zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        traceFock ((diagonalEvolution energy (-β)).comp
          (C1.comp (prodComp (l.map Prod.fst)))) =
      traceFock ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) := by
  have hopeq := comp_prodComp_eq_of_zetaCommutator ζ C1 l hcomm
  have hrot := traceFock_diagonalEvolution_comp_rotate energy β q1
    (prodComp (l.map Prod.fst)) C1 hC1
  have hstep : traceFock ((diagonalEvolution energy (-β)).comp
      (C1.comp (prodComp (l.map Prod.fst)))) =
      traceFock ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) +
        ζ ^ l.length * traceFock ((diagonalEvolution energy (-β)).comp
          ((prodComp (l.map Prod.fst)).comp C1)) := by
    conv_lhs => rw [hopeq]
    simp only [LinearMap.comp_add, LinearMap.comp_smul, traceFock_add, traceFock_smul]
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
    (hcomm : ∀ p ∈ l, zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hPeel : Summable (fun n =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) n n))
    (hRotate : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp (prodComp (l.map Prod.fst))) n k *
        matrixCoeff C1 k n))) :
    (1 - ζ ^ l.length * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        tsumTrace ((diagonalEvolution energy (-β)).comp
          (C1.comp (prodComp (l.map Prod.fst)))) =
      tsumTrace ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) := by
  have hopeq := comp_prodComp_eq_of_zetaCommutator ζ C1 l hcomm
  have hrot := tsumTrace_diagonalEvolution_comp_rotate energy β q1
    (prodComp (l.map Prod.fst)) C1 hC1 hRotate
  have hSummDCjC1 : Summable (fun n => matrixCoeff
      ((diagonalEvolution energy (-β)).comp ((prodComp (l.map Prod.fst)).comp C1)) n n) := by
    have := summable_matrixCoeff_diag_comp_of_summable_uncurry
      ((diagonalEvolution energy (-β)).comp (prodComp (l.map Prod.fst))) C1 hRotate
    rwa [LinearMap.comp_assoc] at this
  have hDcomm : (diagonalEvolution energy (-β)).comp (C1.comp (prodComp (l.map Prod.fst))) =
      (diagonalEvolution energy (-β)).comp (peelSum ζ l) +
        ζ ^ l.length • ((diagonalEvolution energy (-β)).comp
          ((prodComp (l.map Prod.fst)).comp C1)) := by
    rw [hopeq, LinearMap.comp_add, LinearMap.comp_smul]
  have hpoint : (fun n => matrixCoeff ((diagonalEvolution energy (-β)).comp
      (C1.comp (prodComp (l.map Prod.fst)))) n n) =
      fun n => matrixCoeff ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) n n +
        ζ ^ l.length * matrixCoeff ((diagonalEvolution energy (-β)).comp
          ((prodComp (l.map Prod.fst)).comp C1)) n n := by
    funext n
    rw [hDcomm, matrixCoeff_add, matrixCoeff_smul]
  have hstep : tsumTrace ((diagonalEvolution energy (-β)).comp
      (C1.comp (prodComp (l.map Prod.fst)))) =
      tsumTrace ((diagonalEvolution energy (-β)).comp (peelSum ζ l)) +
        ζ ^ l.length * tsumTrace ((diagonalEvolution energy (-β)).comp
          ((prodComp (l.map Prod.fst)).comp C1)) := by
    rw [tsumTrace, tsumTrace, tsumTrace, hpoint,
      (hPeel.hasSum.add ((hSummDCjC1.mul_left (ζ ^ l.length)).hasSum)).tsum_eq, tsum_mul_left]
  rw [hrot, smul_eq_mul] at hstep
  linear_combination hstep

end Common
end SecondQuantization
