import LeanCondensedMatter.SecondQuantization.Common.KMSRotation

set_option linter.style.header false

/-!
# The 2-point Bloch–de Dominicis base case

Phase 9, step 4 of Track D's finite-mode fermionic primary line
(`notes/roadmaps/second-quantization.md`): the `n = 1` base case of the general finite-temperature
Bloch–de Dominicis induction (`quantum-statistical-mechanics.tex`), packaging
`Common/KMSRotation.lean`'s rotation identity together with the c-number exchange commutator into
the closed self-referential 2-point equation

`(1 - ζw₁) Tr[e^{-βH₀}(C₁Cⱼ)] = c₁ⱼ Tr[e^{-βH₀}]`

Unlike the rotation identity itself (reusable well beyond Bloch–de Dominicis), this equation is
specifically the Bloch–de Dominicis base case, hence its own file. Both a `[Fintype Config]`
version (`traceFock_diagonalEvolution_comp_two_point`) and a `tsum`, summability-hypothesis-gated
version usable on an infinite `Config` (`tsumTrace_diagonalEvolution_comp_two_point`) are proved
below.
-/

namespace SecondQuantization
namespace Common

variable {Config : Type*}

/-- **The 2-point Bloch–de Dominicis base case**: `(1 - ζw₁) Tr[e^{-βH₀}(C₁Cⱼ)] = c₁ⱼ
Tr[e^{-βH₀}]`, where `c₁ⱼ` is the (assumed scalar) `ζ`-commutator `[C₁, Cⱼ]_ζ := C₁Cⱼ - ζCⱼC₁`,
and `w₁ := e^{q₁β}` is `C₁`'s thermal factor (`q₁` its eigenvalue shift). This is the
un-normalized, un-divided form of the physics reference notes' `⟨Ĉ₁Ĉⱼ⟩ = C_{1,j}/(1 - ζw₁)`
(`quantum-statistical-mechanics.tex`, the `n = 1` base case inside the general Bloch–de Dominicis
induction): derived from the assumed c-number commutator (rewriting `C₁Cⱼ` as `c₁ⱼ • id + ζ•(CⱼC₁)`)
and `traceFock_diagonalEvolution_comp_rotate` (rotating `CⱼC₁` back to `w₁•(C₁Cⱼ)`), then solving
the resulting self-referential equation for the trace — left un-divided (rather than requiring
`1 - ζw₁ ≠ 0` as a further hypothesis) so the caller decides how to use it. -/
theorem traceFock_diagonalEvolution_comp_two_point [Fintype Config]
    (energy : Config → ℝ) (β q1 : ℝ) (ζ c1j : ℂ)
    (C1 Cj : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : C1.comp Cj - ζ • (Cj.comp C1) =
      c1j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    (1 - ζ * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        traceFock ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) =
      c1j * traceFock (diagonalEvolution energy (-β)) := by
  rw [sub_eq_iff_eq_add] at hcomm
  have hrot := traceFock_diagonalEvolution_comp_rotate energy β q1 Cj C1 hC1
  have hstep : traceFock ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) =
      c1j * traceFock (diagonalEvolution energy (-β)) +
        ζ * traceFock ((diagonalEvolution energy (-β)).comp (Cj.comp C1)) := by
    conv_lhs => rw [hcomm]
    rw [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.comp_smul, LinearMap.comp_id,
      traceFock_add, traceFock_smul, traceFock_smul]
  rw [hrot, smul_eq_mul] at hstep
  linear_combination hstep

/-- **The `tsum` 2-point Bloch–de Dominicis base case**: the `[Fintype Config]`-free analogue of
`traceFock_diagonalEvolution_comp_two_point`, given the same c-number-commutator and KMS-weight
hypotheses plus explicit summability of the partition-function diagonal series
(`n ↦ (e^{-βH₀})ₙₙ`, `hSummD`) and of the rotation's double series (`h`). Summability of the
rotated two-point diagonal series (`n ↦ (e^{-βH₀}CⱼC₁)ₙₙ`) is *not* a separate hypothesis — it
follows from `h` alone via `summable_matrixCoeff_diag_comp_of_summable_uncurry`, so only two
summability witnesses are needed rather than three. This is the theorem a genuine bosonic
free Boltzmann weight would need to instantiate (supplying those two summability witnesses from
`Bosonic/BoltzmannWeightSummable.lean`-style convergence facts, not done here) to get a real
bosonic 2-point function out of this framework. -/
theorem tsumTrace_diagonalEvolution_comp_two_point
    (energy : Config → ℝ) (β q1 : ℝ) (ζ c1j : ℂ)
    (C1 Cj : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm : C1.comp Cj - ζ • (Cj.comp C1) =
      c1j • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hSummD : Summable (fun n => matrixCoeff (diagonalEvolution energy (-β)) n n))
    (h : Summable (Function.uncurry (fun n k =>
      matrixCoeff ((diagonalEvolution energy (-β)).comp Cj) n k * matrixCoeff C1 k n))) :
    (1 - ζ * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        tsumTrace ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) =
      c1j * tsumTrace (diagonalEvolution energy (-β)) := by
  rw [sub_eq_iff_eq_add] at hcomm
  have hrot := tsumTrace_diagonalEvolution_comp_rotate energy β q1 Cj C1 hC1 h
  have hSummDCjC1 : Summable
      (fun n => matrixCoeff ((diagonalEvolution energy (-β)).comp (Cj.comp C1)) n n) := by
    have := summable_matrixCoeff_diag_comp_of_summable_uncurry
      ((diagonalEvolution energy (-β)).comp Cj) C1 h
    rwa [LinearMap.comp_assoc] at this
  have hpoint : (fun n => matrixCoeff ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) n n) =
      fun n => c1j * matrixCoeff (diagonalEvolution energy (-β)) n n +
        ζ * matrixCoeff ((diagonalEvolution energy (-β)).comp (Cj.comp C1)) n n := by
    funext n
    conv_lhs => rw [hcomm]
    rw [LinearMap.comp_add, LinearMap.comp_smul, LinearMap.comp_smul, LinearMap.comp_id,
      matrixCoeff_add, matrixCoeff_smul, matrixCoeff_smul]
  have hstep : tsumTrace ((diagonalEvolution energy (-β)).comp (C1.comp Cj)) =
      c1j * tsumTrace (diagonalEvolution energy (-β)) +
        ζ * tsumTrace ((diagonalEvolution energy (-β)).comp (Cj.comp C1)) := by
    rw [tsumTrace, tsumTrace, tsumTrace, hpoint,
      (((hSummD.mul_left c1j).hasSum).add ((hSummDCjC1.mul_left ζ)).hasSum).tsum_eq,
      tsum_mul_left, tsum_mul_left]
  rw [hrot, smul_eq_mul] at hstep
  linear_combination hstep

end Common
end SecondQuantization
