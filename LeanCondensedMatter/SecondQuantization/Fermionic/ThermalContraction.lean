import LeanCondensedMatter.SecondQuantization.Fermionic.ThermalGreenFunction

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

The underlying fact is purely about occupation-number bookkeeping: annihilating twice (composing
`annihilate i` with `annihilate j`, in either order) always changes the particle number by `-2` or
produces `0` outright, so it can never map a basis state `|n⟩` back to a multiple of itself. The
`(n, n)` matrix coefficient of any such composite operator is therefore `0` for every `n`, making
the weighted trace — hence the thermal expectation — vanish termwise for any occupation-number-
diagonal weight `w` (the only kind `weightedTrace` accepts), with no need to know anything about
`w`'s specific values.
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-! ## Basis-level vanishing -/

omit [Fintype Mode] in
/-- **Annihilating twice never returns to the same occupation state.** Composing `annihilate i`
with `annihilate j` (in this order) sends `basisState n` to a scalar multiple of `basisState m`
for some `m` with strictly fewer particles than `n` (or to `0` outright) — either way, `m ≠ n`. -/
theorem matrixCoeff_annihilate_comp_annihilate (i j : Mode) (n : FermionOccupation Mode) :
    matrixCoeff ((annihilate i).comp (annihilate j)) n n = 0 := by
  change ((annihilate i).comp (annihilate j)) (basisState n) n = 0
  by_cases hj : j ∈ n
  · rw [LinearMap.comp_apply, annihilate_basisState_of_mem hj, map_smul]
    by_cases hi : i ∈ removeOccupation j n
    · rw [annihilate_basisState_of_mem hi, smul_smul]
      have hcard1 := fermionParticleNumber_removeOccupation_of_mem hj
      have hcard2 := fermionParticleNumber_removeOccupation_of_mem hi
      have hne : removeOccupation i (removeOccupation j n) ≠ n := by
        intro heq
        rw [heq] at hcard2
        omega
      exact Common.smul_basisState_apply_of_ne _ hne
    · rw [annihilate_basisState_of_not_mem hi, smul_zero]
      simp
  · rw [LinearMap.comp_apply, annihilate_basisState_of_not_mem hj, map_zero]
    simp

omit [Fintype Mode] in
/-- **Creating twice never returns to the same occupation state**, the creation-side mirror of
`matrixCoeff_annihilate_comp_annihilate`: `create i ∘ create j` sends `basisState n` to a scalar
multiple of `basisState m` with strictly more particles than `n` (or to `0` outright, from Pauli
exclusion). -/
theorem matrixCoeff_create_comp_create (i j : Mode) (n : FermionOccupation Mode) :
    matrixCoeff ((create i).comp (create j)) n n = 0 := by
  change ((create i).comp (create j)) (basisState n) n = 0
  by_cases hj : j ∈ n
  · rw [LinearMap.comp_apply, create_basisState_of_mem hj, map_zero]
    simp
  · rw [LinearMap.comp_apply, create_basisState_of_not_mem hj, map_smul]
    by_cases hi : i ∈ insertOccupation j n
    · rw [create_basisState_of_mem hi, smul_zero]
      simp
    · rw [create_basisState_of_not_mem hi, smul_smul]
      have hcard1 := fermionParticleNumber_insertOccupation_of_not_mem hj
      have hcard2 := fermionParticleNumber_insertOccupation_of_not_mem hi
      have hne : insertOccupation i (insertOccupation j n) ≠ n := by
        intro heq
        rw [heq] at hcard2
        omega
      exact Common.smul_basisState_apply_of_ne _ hne

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
      (timeOrderedProduct (Statistics.zetaInt Statistics.fermion)
        (imaginaryTimeEvolve ε τ (annihilate i)) (imaginaryTimeEvolve ε τ' (annihilate j)) τ τ')
      = 0 := by
  rw [imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_annihilate]
  rcases lt_trichotomy τ' τ with h | h | h
  · rw [timeOrderedProduct_of_gt _ _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_annihilate_comp_annihilate]
  · subst h
    rw [timeOrderedProduct_self_time]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_add, thermalExpectation_neg,
      thermalExpectation_annihilate_comp_annihilate]
  · rw [timeOrderedProduct_of_lt _ _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_neg, thermalExpectation_annihilate_comp_annihilate]

/-- **`⟨T_τ[c_i†(τ) c_j†(τ')]⟩_w = 0`**: the creation-side mirror of
`thermalExpectation_timeOrderedProduct_annihilate_annihilate`. -/
theorem thermalExpectation_timeOrderedProduct_create_create (ε : Mode → ℝ)
    (w : FermionOccupation Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    thermalExpectation w
      (timeOrderedProduct (Statistics.zetaInt Statistics.fermion)
        (imaginaryTimeEvolve ε τ (create i)) (imaginaryTimeEvolve ε τ' (create j)) τ τ')
      = 0 := by
  rw [imaginaryTimeEvolve_create, imaginaryTimeEvolve_create]
  rcases lt_trichotomy τ' τ with h | h | h
  · rw [timeOrderedProduct_of_gt _ _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_create_comp_create]
  · subst h
    rw [timeOrderedProduct_self_time]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_add, thermalExpectation_neg, thermalExpectation_create_comp_create]
  · rw [timeOrderedProduct_of_lt _ _ _ h]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, thermalExpectation_smul,
      thermalExpectation_neg, thermalExpectation_create_comp_create]

end SecondQuantization
