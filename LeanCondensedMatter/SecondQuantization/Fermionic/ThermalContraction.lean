import LeanCondensedMatter.SecondQuantization.Fermionic.ThermalGreenFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.ParticleNumberCharge

set_option linter.style.header false

/-!
# Same-type thermal contractions vanish

Phase 9, step 4 (`notes/roadmaps/second-quantization.md`): the first piece of the finite-mode
fermionic Wick/Bloch–De Dominicis theorem — for *any* occupation-number-diagonal weight `w`
(`weightedTrace`/`thermalExpectation`'s `Σₙ w(n)⟨n|A|n⟩` structure is diagonal in the
occupation-number basis by construction, not just for the genuine free Boltzmann weight), the
thermal time-ordered two-point function of two annihilation operators, or of two creation
operators, is identically zero:

`⟨T_τ[c_i(τ) c_j(τ')]⟩_w = 0`, `⟨T_τ[c_i†(τ) c_j†(τ')]⟩_w = 0`.

**This is a `U(1)` particle-number selection rule, not a fact about fermions specifically.** The
combination `cᵢcⱼ` carries particle-number charge `-2`, and `cᵢ†cⱼ†` carries charge `+2`; any
occupation-number-diagonal state functional — hence `U(1)`-symmetric, though the converse fails
(a state functional can be `U(1)`-symmetric, commuting with the total number operator, without
being occupation-number-*diagonal*: it may still mix distinct occupation states of equal total
particle number) — annihilates an operator of nonzero charge, since such an operator only ever
connects basis states of *different* particle number, and an occupation-number-diagonal state
functional only ever reads off diagonal (`m = n`) matrix elements. This file formalizes the
occupation-number-diagonal special case (`weightedTrace`/`thermalExpectation`'s `Σₙ w(n)⟨n|A|n⟩`
structure); more generally, the same charge-selection rule holds for any `U(1)`-invariant state
functional, occupation-number-diagonal or not. Nothing here depends on the exchange statistics —
the identical argument holds for bosonic annihilation/creation operators against any
occupation-number-diagonal bosonic state functional.
**This does *not* extend to non-number-conserving quasi-free states** (e.g. a superconducting/
Bogoliubov state), where the state functional is no longer occupation-number-diagonal and these
same-type "anomalous" contractions are generically nonzero — they are exactly the pairing
correlations superconductivity's anomalous Green functions describe. So: in the number-conserving
free Gibbs state considered throughout this project, only mixed create–annihilate contractions can
be nonzero (`ThermalGreenFunction.lean`'s `thermalGreenFunction`) — that claim is scoped to this
project's number-conserving setting, not a universal statement about all quasi-free states.

The basis-level vanishing is now an instance of `Common/ParticleNumberSelectionRule.lean`'s
general particle-number selection rule, rather than a fermion-specific case analysis:
`carriesParticleNumberCharge_annihilate`/`_create` (`Fermionic/ParticleNumberCharge.lean`) show
`annihilate i`/`create i` carry particle-number charge `∓1`,
`Common.CarriesGradingDegree.comp` combines these into charge `∓2` for the composite
operators, and `Common.diagonalCoeff_eq_zero_of_carriesGradingDegree` concludes that any
operator of nonzero charge has vanishing diagonal matrix coefficients everywhere. That makes the
weighted trace — hence the thermal expectation — vanish termwise for any occupation-number-
diagonal weight `w` (the only kind `weightedTrace` accepts), with no need to know anything about
`w`'s specific values.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-! ## Basis-level vanishing -/

omit [Fintype Mode] in
/-- **Annihilating twice never returns to the same occupation state.** `(annihilate i).comp
(annihilate j)` carries particle-number charge `-2` (`carriesParticleNumberCharge_annihilate`
composed via `Common.CarriesGradingDegree.comp`), so by the particle-number selection rule
(`Common.diagonalCoeff_eq_zero_of_carriesGradingDegree`) its diagonal matrix coefficients
vanish identically. -/
theorem matrixCoeff_annihilate_comp_annihilate (i j : Mode) (n : FermionOccupation Mode) :
    matrixCoeff ((annihilate i).comp (annihilate j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesGradingDegree
    ((carriesParticleNumberCharge_annihilate i).comp (carriesParticleNumberCharge_annihilate j))
    (by norm_num) n

omit [Fintype Mode] in
/-- **Creating twice never returns to the same occupation state**, the creation-side mirror of
`matrixCoeff_annihilate_comp_annihilate`: `(create i).comp (create j)` carries particle-number
charge `+2`. -/
theorem matrixCoeff_create_comp_create (i j : Mode) (n : FermionOccupation Mode) :
    matrixCoeff ((create i).comp (create j)) n n = 0 :=
  Common.diagonalCoeff_eq_zero_of_carriesGradingDegree
    ((carriesParticleNumberCharge_create i).comp (carriesParticleNumberCharge_create j))
    (by norm_num) n

/-! ## Vanishing at the level of the thermal weighted trace and expectation value -/

theorem weightedTrace_annihilate_comp_annihilate (w : FermionOccupation Mode → ℂ) (i j : Mode) :
    weightedTrace w ((annihilate i).comp (annihilate j)) = 0 := by
  simp [weightedTrace, matrixCoeff_annihilate_comp_annihilate]

theorem weightedTrace_create_comp_create (w : FermionOccupation Mode → ℂ) (i j : Mode) :
    weightedTrace w ((create i).comp (create j)) = 0 := by
  simp [weightedTrace, matrixCoeff_create_comp_create]

theorem thermalExpectation_annihilate_comp_annihilate (w : FermionOccupation Mode → ℂ)
    (i j : Mode) : thermalExpectation w ((annihilate i).comp (annihilate j)) = 0 := by
  rw [thermalExpectation, weightedTrace_annihilate_comp_annihilate, zero_div]

theorem thermalExpectation_create_comp_create (w : FermionOccupation Mode → ℂ) (i j : Mode) :
    thermalExpectation w ((create i).comp (create j)) = 0 := by
  rw [thermalExpectation, weightedTrace_create_comp_create, zero_div]

/-! ## Vanishing for the evolved, time-ordered thermal two-point function -/

/-- **`⟨T_τ[c_i(τ) c_j(τ')]⟩_w = 0`**: the imaginary-time-evolved, time-ordered thermal expectation
of two annihilation operators vanishes, for any occupation-number-diagonal weight `w`. Combines
`imaginaryTimeEvolve_annihilate` (each evolved annihilation operator is a scalar multiple of the
un-evolved one) with `thermalExpectation_annihilate_comp_annihilate` on both time-ordering
branches. -/
theorem thermalExpectation_timeOrderedProduct_annihilate_annihilate (ε : Mode → ℝ)
    (w : FermionOccupation Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    thermalExpectation w
      (timeOrderedProduct
        (imaginaryTimeEvolve ε τ (annihilate i)) (imaginaryTimeEvolve ε τ' (annihilate j)) τ τ')
      = 0 := by
  rw [imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_annihilate]
  rcases lt_trichotomy τ' τ with h | h | h
  · rw [timeOrderedProduct_of_gt _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_annihilate_comp_annihilate]
  · subst h
    rw [timeOrderedProduct_self_time]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_add, thermalExpectation_neg,
      thermalExpectation_annihilate_comp_annihilate]
  · rw [timeOrderedProduct_of_lt _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_neg, thermalExpectation_annihilate_comp_annihilate]

/-- **`⟨T_τ[c_i†(τ) c_j†(τ')]⟩_w = 0`**: the creation-side mirror of
`thermalExpectation_timeOrderedProduct_annihilate_annihilate`. -/
theorem thermalExpectation_timeOrderedProduct_create_create (ε : Mode → ℝ)
    (w : FermionOccupation Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    thermalExpectation w
      (timeOrderedProduct
        (imaginaryTimeEvolve ε τ (create i)) (imaginaryTimeEvolve ε τ' (create j)) τ τ')
      = 0 := by
  rw [imaginaryTimeEvolve_create, imaginaryTimeEvolve_create]
  rcases lt_trichotomy τ' τ with h | h | h
  · rw [timeOrderedProduct_of_gt _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_create_comp_create]
  · subst h
    rw [timeOrderedProduct_self_time]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_add, thermalExpectation_neg, thermalExpectation_create_comp_create]
  · rw [timeOrderedProduct_of_lt _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_neg, thermalExpectation_create_comp_create]

end SecondQuantization
