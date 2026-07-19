import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Fermionic.CanonicalAnticommutationRelations
import LeanCondensedMatter.SecondQuantization.Fermionic.WeightedDiagonalFunctional
import LeanCondensedMatter.SecondQuantization.Common.BlochDeDominicis.TwoPoint

set_option linter.style.header false

/-!
# The finite-mode fermionic 2-point function, from the general Bloch–de Dominicis base case

Phase 9, step 4 of Track D's finite-mode fermionic primary line
(`notes/roadmaps/second-quantization.md`): the first concrete instantiation of
`Common.traceFock_diagonalEvolution_comp_two_point` (from `Common/BlochDeDominicis/TwoPoint.lean`,
itself built from `Common/WeightedDiagonalFunctional.lean`'s trace cyclicity and
`Common/DiagonalEvolution.lean`'s KMS-type relation) against real fermionic `annihilate`/`create`
operators — validating the whole general `Common/` Bloch–de Dominicis chain (PRs building trace
cyclicity, the KMS relation, and their combination) by cross-checking it reproduces the already
independently-established closed-form fermionic 2-point function
(`Fermionic/FreeTwoPointFunction.lean`'s `freeGibbsGreenFunction_of_gt_self`/Fermi–Dirac
occupation number).

The instantiation uses only: `imaginaryTimeEvolve_annihilate`'s eigenvalue-shift fact (`c_i(τ) =
e^{-τεᵢ}c_i`, giving the KMS relation's `q := -εᵢ`) and CAR's `anticomm_annihilate_create` (the
c-number exchange commutator, `ζ := -1`) — no case analysis on `FermionOccupation Mode`, unlike
the earlier `Fermionic/BlochDeDominicisSingleMode.lean` (single-mode, hand-derived from CAR
directly rather than through the general `Common/` framework).
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The finite-mode fermionic 2-point identity**: `(1 + e^{-εᵢβ}) Tr[e^{-βH₀}(cᵢcⱼ†)] = δᵢⱼ
Tr[e^{-βH₀}]`, a direct instantiation of `Common.traceFock_diagonalEvolution_comp_two_point` with
`C₁ := annihilate i`, `Cⱼ := create j`, `q₁ := -εᵢ` (from `imaginaryTimeEvolve_annihilate`), and
`ζ := -1`, `c₁ⱼ := δᵢⱼ` (from `anticomm_annihilate_create`, CAR's mixed exchange relation). At
`i = j` this recovers `⟨cᵢcᵢ†⟩ = 1/(1 + e^{-εᵢβ}) = e^{εᵢβ}/(e^{εᵢβ}+1) = 1 - ⟨Nᵢ⟩`, matching the
Fermi–Dirac distribution already established independently in
`Fermionic/FreeTwoPointFunction.lean`. -/
theorem traceFock_imaginaryTimeEvolveFree_comp_annihilate_comp_create
    (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    (1 + Complex.exp ((-(ε i) * β : ℝ) : ℂ)) *
        traceFock ((imaginaryTimeEvolveFree ε (-β)).comp ((annihilate i).comp (create j))) =
      (if i = j then (1 : ℂ) else 0) * traceFock (imaginaryTimeEvolveFree ε (-β)) := by
  have hC1 : Common.heisenbergEvolve (fermionEnergy ε) (-β) (annihilate i) =
      Complex.exp ((-(ε i) * (-β) : ℝ) : ℂ) • annihilate i := by
    have h := imaginaryTimeEvolve_annihilate ε (-β) i
    rwa [show ((-(ε i) * (-β) : ℝ) : ℂ) = -((-β : ℝ) : ℂ) * (ε i : ℂ) by push_cast; ring]
  have hcomm : (annihilate i).comp (create j) -
      (Statistics.zetaInt Statistics.fermion : ℂ) • ((create j).comp (annihilate i)) =
        (if i = j then (1 : ℂ) else 0) •
          (LinearMap.id : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) := by
    rw [Statistics.zetaInt_fermion]
    have h := anticomm_annihilate_create i j
    rw [anticomm] at h
    push_cast
    rw [neg_one_smul, sub_neg_eq_add, h]
    split_ifs <;> simp
  have h := Common.traceFock_diagonalEvolution_comp_two_point (fermionEnergy ε) β (-(ε i))
    (Statistics.zetaInt Statistics.fermion : ℂ) (if i = j then (1 : ℂ) else 0)
    (annihilate i) (create j) hC1 hcomm
  rw [Statistics.zetaInt_fermion] at h
  rwa [show (1 - ((-1 : ℤ) : ℂ) * Complex.exp ((-(ε i) * β : ℝ) : ℂ)) =
      1 + Complex.exp ((-(ε i) * β : ℝ) : ℂ) by push_cast; ring] at h

end SecondQuantization
