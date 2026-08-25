import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.PeelFirstTrace

set_option linter.style.header false

/-!
# The 4-point Bloch–de Dominicis first-operator reduction

The `n = 2` (4-operator) case of the finite-temperature Bloch–de Dominicis induction applies the
same commutator-substitution and KMS-rotation pattern as the 2-point base case: commute `C₁`
through the three remaining factors via the c-number exchange commutator, then use
`Common.traceFock_diagonalEvolution_comp_rotate` to close the resulting self-referential trace
equation. The general induction is provided by
`Common/Thermal/BlochDeDominicis/Induction.lean`; this file exposes the concrete hand-unrolled
`n = 2` first-operator reduction.

**Not the fully reduced 4-point Bloch–de Dominicis expansion.** The normalized identity
`⟨C₁C₂C₃C₄⟩_β = ⟨C₁C₂⟩_β⟨C₃C₄⟩_β + ζ⟨C₁C₃⟩_β⟨C₂C₄⟩_β + ⟨C₁C₄⟩_β⟨C₂C₃⟩_β` is a product of
normalized 2-point numbers. Here the right-hand side is instead a sum of un-normalized
`traceFock` terms for the remaining operator pairs. Reducing those terms further requires each
remaining pair's own imaginary-time eigenoperator shift and c-number commutator hypotheses, plus
a nonzero partition function for normalization. The general theorem in `Induction.lean` packages
the corresponding pairing-weighted reduction; at `n = 2` it matches
`GibbsExpectation/FourPoint.lean`'s `finiteGibbsExpectation_four_point`.
-/

namespace SecondQuantization
namespace Common


variable {Config : Type*}

/-- **The pure operator-algebra identity behind the 4-point reduction**, a specialization of
`PeelFirst.lean`'s general `comp_prodComp_eq_of_zetaCommutator` at `l := [(C2,c12), (C3,c13),
(C4,c14)]` — repeatedly rewriting `C₁Cⱼ` as `c₁ⱼ • id + ζ•(CⱼC₁)` (for `j = 2, 3, 4`) and pushing
the resulting `C₁` rightward through `C₂`, then `C₃`, picks up one factor of `ζ` per operator it
passes, landing `C₁` at the very end. Pure `LinearMap` composition algebra — no
`traceFock`/`Config`-finiteness involved. -/
theorem comp_comp_comp_eq_of_zetaCommutator
    (ζ c12 c13 c14 : ℂ) (C1 C2 C3 C4 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hcomm12 : C1.comp C2 - ζ • (C2.comp C1) =
      c12 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm13 : C1.comp C3 - ζ • (C3.comp C1) =
      c13 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm14 : C1.comp C4 - ζ • (C4.comp C1) =
      c14 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    C1.comp (C2.comp (C3.comp C4)) =
      c12 • (C3.comp C4) + (ζ * c13) • (C2.comp C4) + (ζ ^ 2 * c14) • (C2.comp C3) +
        ζ ^ 3 • (C2.comp (C3.comp (C4.comp C1))) := by
  have hmem : ∀ p ∈ [(C2, c12), (C3, c13), (C4, c14)], zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
    intro p hp
    fin_cases hp
    · exact hcomm12
    · exact hcomm13
    · exact hcomm14
  have h := comp_prodComp_eq_of_zetaCommutator ζ C1 [(C2, c12), (C3, c13), (C4, c14)] hmem
  simp only [prodComp, peelSum, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    LinearMap.comp_id, LinearMap.comp_zero, LinearMap.comp_add, LinearMap.comp_smul, smul_add,
    smul_smul, smul_zero, add_zero] at h
  linear_combination (norm := module) h

/-- **The 4-point Bloch–de Dominicis first-operator reduction**, a specialization of
`PeelFirstTrace.lean`'s general `traceFock_diagonalEvolution_comp_peel` at `l := [(C2,c12),
(C3,c13), (C4,c14)]`: `(1 - ζ³w₁) Tr[e^{-βH₀}(C₁C₂C₃C₄)] = c₁₂ Tr[e^{-βH₀}(C₃C₄)] + ζc₁₃
Tr[e^{-βH₀}(C₂C₄)] + ζ²c₁₄ Tr[e^{-βH₀}(C₂C₃)]`. See the module docstring for why this is left
un-normalized rather than reduced to a pairing-weighted sum of normalized numbers. -/
theorem traceFock_diagonalEvolution_comp_four_point_reduction [Fintype Config]
    (energy : Config → ℝ) (β q1 : ℝ) (ζ c12 c13 c14 : ℂ)
    (C1 C2 C3 C4 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)
    (hC1 : heisenbergEvolve energy (-β) C1 = Complex.exp ((q1 * (-β) : ℝ) : ℂ) • C1)
    (hcomm12 : C1.comp C2 - ζ • (C2.comp C1) =
      c12 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm13 : C1.comp C3 - ζ • (C3.comp C1) =
      c13 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config))
    (hcomm14 : C1.comp C4 - ζ • (C4.comp C1) =
      c14 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config)) :
    (1 - ζ ^ 3 * Complex.exp ((q1 * β : ℝ) : ℂ)) *
        traceFock ((diagonalEvolution energy (-β)).comp
          (C1.comp (C2.comp (C3.comp C4)))) =
      c12 * traceFock ((diagonalEvolution energy (-β)).comp (C3.comp C4)) +
        ζ * c13 * traceFock ((diagonalEvolution energy (-β)).comp (C2.comp C4)) +
        ζ ^ 2 * c14 * traceFock ((diagonalEvolution energy (-β)).comp (C2.comp C3)) := by
  have hmem : ∀ p ∈ [(C2, c12), (C3, c13), (C4, c14)], zetaCommutator ζ C1 p.1 =
      p.2 • (LinearMap.id : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) := by
    intro p hp
    fin_cases hp
    · exact hcomm12
    · exact hcomm13
    · exact hcomm14
  have hz : traceFock (0 : AlgebraicFock Config →ₗ[ℂ] AlgebraicFock Config) = 0 := by
    simp [traceFock, matrixCoeff]
  have h := traceFock_diagonalEvolution_comp_peel energy β q1 ζ C1
    [(C2, c12), (C3, c13), (C4, c14)] hC1 hmem
  simp only [prodComp, peelSum, List.map_cons, List.map_nil, List.length_cons, List.length_nil,
    LinearMap.comp_id, LinearMap.comp_zero, LinearMap.comp_add, LinearMap.comp_smul,
    traceFock_add, traceFock_smul, hz, mul_zero] at h
  linear_combination h

end Common
end SecondQuantization
