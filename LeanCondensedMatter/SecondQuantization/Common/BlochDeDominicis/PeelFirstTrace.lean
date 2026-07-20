import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.PeelFirst
import LeanCondensedMatter.SecondQuantization.Common.KMSRotation

set_option linter.style.header false

/-!
# The trace-level peel-first identity: `PeelFirst.lean` + KMS cyclicity

Wraps `Common/BlochDeDominicis/PeelFirst.lean`'s pure operator-algebra peel identity
(`comp_prodComp_eq_of_zetaCommutator`) in the trace-level KMS cyclicity step
(`Common.traceFock_diagonalEvolution_comp_rotate`), the way
`Common/BlochDeDominicis/FourPointReduction.lean` does for the hand-unrolled 3-operator case —
this is that same strategy, but for an arbitrary-length remaining product, so
`FourPointReduction.lean`'s theorem is now a special case (`l := [(C2, c12), (C3, c13), (C4,
c14)]`, not yet stated as such here).

Solving the resulting self-referential trace equation (rotating `C₁` from the end of the product
back to the front, picking up `w₁ := e^{q₁β}`, and matching the `ζ^{l.length}` power the peel
identity produces) gives

`(1 - ζ^{l.length}w₁) Tr[e^{-βH₀}(C₁·B₁⋯Bₖ)] = Tr[e^{-βH₀}·peelSum ζ [(B₁,c₁),…,(Bₖ,cₖ)]]`

**Left un-reduced on the right**, matching `TwoPoint.lean`/`FourPointReduction.lean`'s own choice:
`peelSum`'s value is *not* further decomposed into a closed sum of `traceFock`-of-remaining-pairs
terms here (that needs unfolding `peelSum`'s recursion against `traceFock_add`/`_smul`/
`LinearMap.comp_add`/`_smul` recursively — straightforward but deferred, since the immediately
useful form is this single self-referential equation, solved once).
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

end Common
end SecondQuantization
