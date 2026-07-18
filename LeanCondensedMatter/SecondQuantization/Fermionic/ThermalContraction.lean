import LeanCondensedMatter.SecondQuantization.Fermionic.ThermalGreenFunction

set_option linter.style.header false

/-!
# Same-type thermal contractions vanish

Phase 9, step 4 (`notes/roadmaps/second-quantization.md`): the first piece of the finite-mode
fermionic Wick/Bloch–De Dominicis theorem — for *any* weight `w` (not just the genuine free
Boltzmann weight), the thermal time-ordered two-point function of two annihilation operators, or
of two creation operators, is identically zero:

`⟨T_τ[c_i(τ) c_j(τ')]⟩_w = 0`, `⟨T_τ[c_i†(τ) c_j†(τ')]⟩_w = 0`.

Only the fermionic "type" (annihilate vs. create) determines this, not the specific `i`, `j`,
`τ`, `τ'`, or even the weight `w` — the underlying fact is purely about occupation-number
bookkeeping: annihilating twice (composing `annihilate i` with `annihilate j`, in either order)
always changes the particle number by `-2` or produces `0` outright, so it can never map a basis
state `|n⟩` back to a multiple of itself. The `(n, n)` matrix coefficient of any such composite
operator is therefore `0` for every `n`, making the weighted trace — hence the thermal
expectation — vanish termwise, with no need to know anything about `w`. This is the operator-level
reason the only nonzero "contraction" in Wick's theorem pairs an annihilation operator with a
creation operator (`ThermalGreenFunction.lean`'s `thermalGreenFunction`).
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

/-! ## Linearity of `matrixCoeff`/`weightedTrace`/`thermalExpectation` in the operator argument -/

omit [LinearOrder Mode] [Fintype Mode] in
theorem matrixCoeff_smul (c : ℂ) (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (m n : FermionOccupation Mode) : matrixCoeff (c • A) m n = c * matrixCoeff A m n := by
  simp [matrixCoeff, Common.matrixCoeff]

omit [LinearOrder Mode] [Fintype Mode] in
theorem matrixCoeff_add (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode)
    (m n : FermionOccupation Mode) :
    matrixCoeff (A + B) m n = matrixCoeff A m n + matrixCoeff B m n := by
  simp [matrixCoeff, Common.matrixCoeff]

omit [LinearOrder Mode] in
theorem weightedTrace_smul (c : ℂ) (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    weightedTrace w (c • A) = c * weightedTrace w A := by
  simp only [weightedTrace, matrixCoeff_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

omit [LinearOrder Mode] in
theorem weightedTrace_add (w : FermionOccupation Mode → ℂ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    weightedTrace w (A + B) = weightedTrace w A + weightedTrace w B := by
  simp only [weightedTrace, matrixCoeff_add, mul_add]
  exact Finset.sum_add_distrib

omit [LinearOrder Mode] in
theorem thermalExpectation_smul (c : ℂ) (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    thermalExpectation w (c • A) = c * thermalExpectation w A := by
  rw [thermalExpectation, thermalExpectation, weightedTrace_smul, mul_div_assoc]

omit [LinearOrder Mode] in
theorem thermalExpectation_add (w : FermionOccupation Mode → ℂ)
    (A B : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    thermalExpectation w (A + B) = thermalExpectation w A + thermalExpectation w B := by
  rw [thermalExpectation, thermalExpectation, thermalExpectation, weightedTrace_add, add_div]

omit [LinearOrder Mode] in
theorem thermalExpectation_neg (w : FermionOccupation Mode → ℂ)
    (A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) :
    thermalExpectation w (-A) = -thermalExpectation w A := by
  rw [show (-A : FockSpaceFermionic Mode →ₗ[ℂ] FockSpaceFermionic Mode) = (-1 : ℂ) • A from
    (neg_one_smul ℂ A).symm, thermalExpectation_smul, neg_one_mul]

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
of two annihilation operators vanishes, for *any* weight `w`. Combines
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
