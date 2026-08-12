import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Common.Thermal.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.Unnormalized.TwoPoint

set_option linter.style.header false

/-!
# Finite-mode fermionic Bloch–de Dominicis two-point identity

This module instantiates the Common unnormalized Bloch–de Dominicis two-point theorem for finite
free fermions. The imaginary-time evolution supplies the eigenvalue shift
`c_i(τ) = e^{-τε_i} c_i`, while CAR supplies the exchange relation
`{c_i, c_j†} = δ_{ij}`.

The resulting trace identity reproduces the same Fermi–Dirac mixed contraction evaluated directly
in `Fermionic/Thermal/FreeGibbsGreenFunction.lean`. The proof uses the general KMS/reordering
infrastructure and does not inspect occupation configurations mode by mode.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- **The finite-mode fermionic two-point identity**:
`(1 + e^{-εᵢβ}) Tr[e^{-βH₀}(cᵢcⱼ†)] = δᵢⱼ Tr[e^{-βH₀}]`.

This is the fermionic specialization of `Common.traceFock_diagonalEvolution_comp_two_point`, with
`q₁ := -εᵢ`, exchange sign `ζ := -1`, and c-number exchange term `δᵢⱼ`. At `i = j` it gives
`⟨cᵢcᵢ†⟩ = 1 - ⟨Nᵢ⟩`, matching the closed form in
`Fermionic/Thermal/FreeGibbsGreenFunction.lean`. -/
theorem traceFock_imaginaryTimeEvolveFree_comp_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (1 + Complex.exp ((-(ε i) * β : ℝ) : ℂ)) *
        Common.traceFock
          ((imaginaryTimeEvolveFree ε (-β)).comp ((annihilate i).comp (create j))) =
      (if i = j then (1 : ℂ) else 0) * Common.traceFock (imaginaryTimeEvolveFree ε (-β)) := by
  have hC1 : Common.heisenbergEvolve (fermionEnergy ε) (-β) (annihilate i) =
      Complex.exp ((-(ε i) * (-β) : ℝ) : ℂ) • annihilate i := by
    have h := imaginaryTimeEvolve_annihilate ε (-β) i
    rwa [show ((-(ε i) * (-β) : ℝ) : ℂ) = -((-β : ℝ) : ℂ) * (ε i : ℂ) by push_cast; ring]
  have hcomm : (annihilate i).comp (create j) -
      (Common.Statistics.zetaInt Common.Statistics.fermion : ℂ) • ((create j).comp (annihilate i)) =
        (if i = j then (1 : ℂ) else 0) •
          (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
    rw [Common.Statistics.zetaInt_fermion]
    have h := anticomm_annihilate_create i j
    rw [anticomm] at h
    push_cast
    rw [neg_one_smul, sub_neg_eq_add, h]
    split_ifs <;> simp
  have h := Common.traceFock_diagonalEvolution_comp_two_point (fermionEnergy ε) β (-(ε i))
    (Common.Statistics.zetaInt Common.Statistics.fermion : ℂ) (if i = j then (1 : ℂ) else 0)
    (annihilate i) (create j) hC1 hcomm
  rw [Common.Statistics.zetaInt_fermion] at h
  rwa [show (1 - ((-1 : ℤ) : ℂ) * Complex.exp ((-(ε i) * β : ℝ) : ℂ)) =
      1 + Complex.exp ((-(ε i) * β : ℝ) : ℂ) by push_cast; ring] at h

end Fermionic
end SecondQuantization
