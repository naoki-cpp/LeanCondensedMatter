import LeanCondensedMatter.SecondQuantization.ThermalTimeOrdering
import LeanCondensedMatter.SecondQuantization.ThermalExpectationFermionic

set_option linter.style.header false

/-!
# The finite-temperature (imaginary-time) two-point Green function

Phase 9, step 3 (`notes/roadmaps/second-quantization.md`): the fermionic two-point Green function
`G_{ij}(τ, τ') := -⟨T_τ c_i(τ) c_j†(τ')⟩_w`, assembled from the previous two steps —
`ImaginaryTimeEvolution.lean`'s `imaginaryTimeEvolve` (still only defined for evolution under the
*free* Hamiltonian `H₀ = freeHamiltonian ε`) and `ThermalTimeOrdering.lean`'s `timeOrderedProduct`
— applied to `annihilate i`/`create j` and averaged with `ThermalExpectationFermionic.lean`'s
`thermalExpectation w`.

As with `thermalExpectation`/`partitionFunction`, `w` is an arbitrary complex weight here, not
necessarily a genuine Boltzmann weight; `thermalGreenFunction` is only the physical
finite-temperature Green function once `w` is so specialized. And since `imaginaryTimeEvolve` is
currently only defined for the free Hamiltonian, this file's Green function is the *free* one,
`G₀`, not yet the interacting `G` a genuine Dyson expansion needs.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-- **The fermionic two-point (imaginary-)time-ordered Green function**,
`G_{ij}(τ, τ') := -⟨T_τ c_i(τ) c_j†(τ')⟩_w`, for the free Hamiltonian's imaginary-time evolution
`c_i(τ) := imaginaryTimeEvolve ε τ (annihilate i)`, `c_j†(τ') := imaginaryTimeEvolve ε τ'
(create j)`, and an arbitrary weight `w`. -/
noncomputable def thermalGreenFunction (ε : Mode → ℝ) (w : FermionOccupation Mode → ℂ) (i j : Mode)
    (τ τ' : ℝ) : ℂ :=
  - thermalExpectation w
      (timeOrderedProduct (Statistics.zetaInt Statistics.fermion)
        (imaginaryTimeEvolve ε τ (annihilate i)) (imaginaryTimeEvolve ε τ' (create j)) τ τ')

/-- **At equal times**, the time-ordering resolves to the plain (un-ordered) product: `G_{ij}(τ,
τ) = -⟨c_i(τ) c_j†(τ)⟩_w`. -/
theorem thermalGreenFunction_self_time (ε : Mode → ℝ) (w : FermionOccupation Mode → ℂ) (i j : Mode)
    (τ : ℝ) :
    thermalGreenFunction ε w i j τ τ =
      - thermalExpectation w
          ((imaginaryTimeEvolve ε τ (annihilate i)).comp (imaginaryTimeEvolve ε τ (create j))) := by
  rw [thermalGreenFunction, timeOrderedProduct_self_time]

end SecondQuantization
