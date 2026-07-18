import LeanCondensedMatter.SecondQuantization.Fermionic.FreePartitionFunction
import LeanCondensedMatter.SecondQuantization.Fermionic.ThermalGreenFunction

set_option linter.style.header false

/-!
# The closed-form free thermal Green function

Phase 9 follow-up (`notes/roadmaps/second-quantization.md`): the mixed contraction closed forms
`⟨c_i c_j†⟩` and `⟨c_j† c_i⟩` that `thermalGreenFunction_of_gt`/`_of_lt` reduce
`freeThermalGreenFunction` to, closing the remaining gap `FreeBoltzmannWeight.lean`'s module
docstring flags: `G₀,ᵢⱼ = 0` for `i ≠ j`.

**Off-diagonal (`i ≠ j`) vanishing is *not* an instance of the `U(1)` particle-number selection
rule** (`Common/ParticleNumberSelectionRule.lean`): `(annihilate i).comp (create j)` carries
charge `-1 + 1 = 0`, so the selection rule says nothing about it. The vanishing here is a
different, finer fact — a basis-level mismatch specific to *which* mode is toggled: acting with
`create j` then `annihilate i` (`i ≠ j`) on `basisState n` either returns `0` outright, or lands on
`basisState ((n \ {i}) ∪ {j})`, a set that differs from `n` at mode `i` (removed) whenever it's
nonzero — so it can never contribute to a diagonal matrix coefficient, regardless of any weight.
This holds for *any* weight `w`, not just the free Boltzmann one.

The diagonal (`i = j`) case, by contrast, does *not* need a new argument: it follows directly from
CAR's `{c_i, c_i†} = id` (`anticomm_annihilate_create`, `CanonicalAnticommutationRelations.lean`),
which rewrites `(annihilate i).comp (create i)` as `id - numberOperator i` — so its thermal
expectation is `1 - ⟨N_i⟩₀,β`, already computed in `FreePartitionFunction.lean`. **The equal-time,
same-mode case `G₀,ᵢᵢ(τ,τ)` is a separate, third closed form**
(`freeThermalGreenFunction_self_time_self`), not a limit of either one-sided formula: it comes from
`timeOrderedProduct`'s `θ(0) = 1/2` symmetrization convention, and is genuinely discontinuous
against both one-sided limits (`G₀,ᵢᵢ(τ,τ'⁺) → -(1-f_i)`, `G₀,ᵢᵢ(τ,τ'⁻) → f_i` as `τ' → τ`, their
difference forced to `-1` by CAR — `ThermalGreenFunction.lean`'s module docstring already flags
this discontinuity).
-/

namespace SecondQuantization

variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]

/-! ## Off-diagonal (`i ≠ j`): both mixed contractions vanish identically, for any weight -/

omit [Fintype Mode] in
/-- **`⟨n| c_i c_j† |n⟩ = 0` for `i ≠ j`.** Acting with `create j` then `annihilate i` on
`basisState n` either vanishes outright, or lands on a basis state that differs from `n` at mode
`i` (removed by `annihilate i`, and never reintroduced since `i ≠ j`) — so it can never return a
nonzero `n`-coefficient. -/
theorem matrixCoeff_annihilate_comp_create_of_ne {i j : Mode} (hij : i ≠ j)
    (n : FermionOccupation Mode) :
    matrixCoeff ((annihilate i).comp (create j)) n n = 0 := by
  change ((annihilate i).comp (create j)) (basisState n) n = 0
  by_cases hj : j ∈ n
  · rw [LinearMap.comp_apply, create_basisState_of_mem hj, map_zero]
    simp
  · rw [LinearMap.comp_apply, create_basisState_of_not_mem hj, map_smul]
    by_cases hi : i ∈ insertOccupation j n
    · rw [annihilate_basisState_of_mem hi, smul_smul]
      have hine : i ∈ n := by
        rcases Finset.mem_insert.1 hi with h | h
        · exact absurd h hij
        · exact h
      have hne : removeOccupation i (insertOccupation j n) ≠ n := by
        intro heq
        rw [← heq] at hine
        exact Finset.notMem_erase i (insertOccupation j n) hine
      exact Common.smul_basisState_apply_of_ne _ hne
    · rw [annihilate_basisState_of_not_mem hi, smul_zero]
      simp

omit [Fintype Mode] in
/-- **`⟨n| c_j† c_i |n⟩ = 0` for `i ≠ j`**, the mirror of
`matrixCoeff_annihilate_comp_create_of_ne`, via CAR's `{c_i, c_j†} = 0`
(`anticomm_annihilate_create`) at `i ≠ j`: the two orders sum to zero, so one vanishing forces the
other. -/
theorem matrixCoeff_create_comp_annihilate_of_ne {i j : Mode} (hij : i ≠ j)
    (n : FermionOccupation Mode) :
    matrixCoeff ((create j).comp (annihilate i)) n n = 0 := by
  have hanticomm := anticomm_annihilate_create i j
  rw [if_neg hij, anticomm] at hanticomm
  have hzero : ((annihilate i).comp (create j) + (create j).comp (annihilate i))
      (basisState n) = 0 := by rw [hanticomm]; simp
  rw [LinearMap.add_apply] at hzero
  have hcoeff := DFunLike.congr_fun hzero n
  simp only [Finsupp.add_apply, Finsupp.zero_apply] at hcoeff
  have h1 : ((annihilate i).comp (create j)) (basisState n) n = 0 :=
    matrixCoeff_annihilate_comp_create_of_ne hij n
  change ((create j).comp (annihilate i)) (basisState n) n = 0
  linear_combination hcoeff - h1

theorem weightedTrace_annihilate_comp_create_of_ne (w : FermionOccupation Mode → ℂ) {i j : Mode}
    (hij : i ≠ j) : weightedTrace w ((annihilate i).comp (create j)) = 0 := by
  simp [weightedTrace, matrixCoeff_annihilate_comp_create_of_ne hij]

theorem weightedTrace_create_comp_annihilate_of_ne (w : FermionOccupation Mode → ℂ) {i j : Mode}
    (hij : i ≠ j) : weightedTrace w ((create j).comp (annihilate i)) = 0 := by
  simp [weightedTrace, matrixCoeff_create_comp_annihilate_of_ne hij]

theorem thermalExpectation_annihilate_comp_create_of_ne (w : FermionOccupation Mode → ℂ)
    {i j : Mode} (hij : i ≠ j) : thermalExpectation w ((annihilate i).comp (create j)) = 0 := by
  rw [thermalExpectation, weightedTrace_annihilate_comp_create_of_ne w hij, zero_div]

theorem thermalExpectation_create_comp_annihilate_of_ne (w : FermionOccupation Mode → ℂ)
    {i j : Mode} (hij : i ≠ j) : thermalExpectation w ((create j).comp (annihilate i)) = 0 := by
  rw [thermalExpectation, weightedTrace_create_comp_annihilate_of_ne w hij, zero_div]

/-! ## Diagonal (`i = j`): the free hole/occupation numbers `1 - f_i`, `f_i` -/

omit [Fintype Mode] in
/-- **`c_i c_i† = id - N_i`**, from CAR's `{c_i, c_i†} = id`. -/
theorem annihilate_comp_create_self (i : Mode) :
    (annihilate i).comp (create i) = LinearMap.id - numberOperator i := by
  have hanticomm := anticomm_annihilate_create i i
  rw [if_pos rfl, anticomm] at hanticomm
  rw [eq_sub_iff_add_eq]
  exact hanticomm

/-- **The free hole number** `⟨c_i c_i†⟩₀,β = 1 - ⟨N_i⟩₀,β = e^{βε_i}/(e^{βε_i}+1)`. -/
theorem freeThermalExpectation_annihilate_comp_create_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) :
    freeThermalExpectation ε β ((annihilate i).comp (create i)) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) := by
  rw [annihilate_comp_create_self, freeThermalExpectation, thermalExpectation_sub,
    thermalExpectation_id _ (partitionFunction_freeBoltzmannWeight_ne_zero ε β),
    show thermalExpectation (freeBoltzmannWeight ε β) (numberOperator i) =
      freeThermalExpectation ε β (numberOperator i) from rfl, freeThermalExpectation_numberOperator]
  have hE : Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 ≠ 0 := by
    rw [show Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 =
      ((Real.exp (β * ε i) + 1 : ℝ) : ℂ) by push_cast [Complex.ofReal_exp]; ring]
    exact Complex.ofReal_ne_zero.2 (by positivity)
  field_simp
  ring

/-! ## The closed-form free thermal Green function -/

/-- **`G₀,ᵢᵢ(τ, τ')` for `τ' < τ`**: `-e^{-(τ-τ')ε_i} · e^{βε_i}/(e^{βε_i}+1)`. -/
theorem freeThermalGreenFunction_of_gt_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ' < τ) :
    freeThermalGreenFunction ε β i i τ τ' =
      - (Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1))) := by
  rw [freeThermalGreenFunction, thermalGreenFunction_of_gt ε (freeBoltzmannWeight ε β) i i h,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul, thermalExpectation_smul, ← freeThermalExpectation,
    freeThermalExpectation_annihilate_comp_create_self]
  rw [show Complex.exp (-(τ : ℂ) * (ε i : ℂ)) * Complex.exp ((τ' : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- **`G₀,ᵢᵢ(τ, τ')` for `τ < τ'`**: `e^{-(τ-τ')ε_i} · 1/(e^{βε_i}+1)`. -/
theorem freeThermalGreenFunction_of_lt_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) {τ τ' : ℝ}
    (h : τ < τ') :
    freeThermalGreenFunction ε β i i τ τ' =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) *
        (1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)) := by
  rw [freeThermalGreenFunction, thermalGreenFunction_of_lt ε (freeBoltzmannWeight ε β) i i h,
    imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create, LinearMap.smul_comp,
    LinearMap.comp_smul, smul_smul,
    show (create i).comp (annihilate i) = numberOperator i from rfl, thermalExpectation_smul,
    ← freeThermalExpectation, freeThermalExpectation_numberOperator]
  rw [show Complex.exp ((τ' : ℂ) * (ε i : ℂ)) * Complex.exp (-(τ : ℂ) * (ε i : ℂ)) =
      Complex.exp (-(τ - τ' : ℝ) * (ε i : ℂ)) by
    rw [← Complex.exp_add]; congr 1; push_cast; ring]

/-- **`G₀,ᵢᵢ(τ, τ)`, the equal-time, same-mode case**, `f_i - 1/2`. Not a limit of either one-sided
formula above: `timeOrderedProduct`'s `θ(0) = 1/2` convention symmetrizes
`½(⟨c_i(τ) c_i†(τ)⟩ - ⟨c_i†(τ) c_i(τ)⟩) = ½((1-f_i) - f_i) = 1/2 - f_i`, giving `G₀,ᵢᵢ(τ,τ) =
-(1/2 - f_i) = f_i - 1/2` — genuinely discontinuous against both one-sided limits `G₀,ᵢᵢ(τ,τ'⁺) →
-（1-f_i)` and `G₀,ᵢᵢ(τ,τ'⁻) → f_i` as `τ' → τ` (their difference is `-1`, forced by CAR, matching
`thermalGreenFunction_self_time`'s module-level remark). -/
theorem freeThermalGreenFunction_self_time_self (ε : Mode → ℝ) (β : ℝ) (i : Mode) (τ : ℝ) :
    freeThermalGreenFunction ε β i i τ τ =
      1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) - (2 : ℂ)⁻¹ := by
  rw [freeThermalGreenFunction, thermalGreenFunction_self_time, imaginaryTimeEvolve_annihilate,
    imaginaryTimeEvolve_create]
  simp only [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, ← Complex.exp_add,
    show -(τ : ℂ) * (ε i : ℂ) + (τ : ℂ) * (ε i : ℂ) = 0 by ring,
    show (τ : ℂ) * (ε i : ℂ) + -(τ : ℂ) * (ε i : ℂ) = 0 by ring, Complex.exp_zero, one_smul,
    show (create i).comp (annihilate i) = numberOperator i from rfl]
  rw [Statistics.zetaInt_fermion, Int.cast_neg, Int.cast_one, neg_smul, thermalExpectation_smul,
    thermalExpectation_add, thermalExpectation_neg, thermalExpectation_smul, one_mul,
    show thermalExpectation (freeBoltzmannWeight ε β) ((annihilate i).comp (create i)) =
      freeThermalExpectation ε β ((annihilate i).comp (create i)) from rfl,
    show thermalExpectation (freeBoltzmannWeight ε β) (numberOperator i) =
      freeThermalExpectation ε β (numberOperator i) from rfl,
    freeThermalExpectation_annihilate_comp_create_self, freeThermalExpectation_numberOperator]
  have hE : Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 ≠ 0 := by
    rw [show Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1 =
      ((Real.exp (β * ε i) + 1 : ℝ) : ℂ) by push_cast [Complex.ofReal_exp]; ring]
    exact Complex.ofReal_ne_zero.2 (by positivity)
  field_simp
  ring

/-! ## All-index (`if i = j then ... else 0`) forms, for Wick's theorem's contraction kernel -/

/-- **`⟨c_j† c_i⟩₀,β`, all indices**: `δᵢⱼ · f_i`, `0` off-diagonal. Combines
`freeThermalExpectation_numberOperator` (`i = j`) with
`thermalExpectation_create_comp_annihilate_of_ne` (`i ≠ j`, which holds for any weight, hence
specializes directly to `freeBoltzmannWeight`). -/
theorem freeThermalExpectation_create_comp_annihilate (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    freeThermalExpectation ε β ((create j).comp (annihilate i)) =
      if i = j then 1 / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1) else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl]
    exact freeThermalExpectation_numberOperator ε β i
  · rw [if_neg hij]
    exact thermalExpectation_create_comp_annihilate_of_ne (freeBoltzmannWeight ε β) hij

/-- **`⟨c_i c_j†⟩₀,β`, all indices**: `δᵢⱼ · (1 - f_i)`, `0` off-diagonal. The mirror of
`freeThermalExpectation_create_comp_annihilate`. -/
theorem freeThermalExpectation_annihilate_comp_create (ε : Mode → ℝ) (β : ℝ) (i j : Mode) :
    freeThermalExpectation ε β ((annihilate i).comp (create j)) =
      if i = j then
        Complex.exp ((β : ℂ) * (ε i : ℂ)) / (Complex.exp ((β : ℂ) * (ε i : ℂ)) + 1)
      else 0 := by
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl, freeThermalExpectation_annihilate_comp_create_self]
  · rw [if_neg hij]
    exact thermalExpectation_annihilate_comp_create_of_ne (freeBoltzmannWeight ε β) hij

/-- **`G₀,ᵢⱼ(τ, τ') = 0` for `i ≠ j`**, at any `τ, τ'` (both time-ordering branches vanish
identically, from `thermalExpectation_annihilate_comp_create_of_ne`/
`_create_comp_annihilate_of_ne`). -/
theorem freeThermalGreenFunction_of_ne (ε : Mode → ℝ) (β : ℝ) {i j : Mode} (hij : i ≠ j)
    (τ τ' : ℝ) : freeThermalGreenFunction ε β i j τ τ' = 0 := by
  rw [freeThermalGreenFunction, thermalGreenFunction]
  rcases lt_trichotomy τ' τ with h | h | h
  · rw [timeOrderedProduct_of_gt _ _ _ h, imaginaryTimeEvolve_annihilate,
      imaginaryTimeEvolve_create]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, thermalExpectation_smul,
      thermalExpectation_annihilate_comp_create_of_ne _ hij]
  · subst h
    rw [timeOrderedProduct_self_time, imaginaryTimeEvolve_annihilate, imaginaryTimeEvolve_create]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, thermalExpectation_smul,
      thermalExpectation_add, thermalExpectation_neg,
      thermalExpectation_annihilate_comp_create_of_ne _ hij,
      thermalExpectation_create_comp_annihilate_of_ne _ hij]
  · rw [timeOrderedProduct_of_lt _ _ _ h, imaginaryTimeEvolve_annihilate,
      imaginaryTimeEvolve_create, Statistics.zetaInt_fermion]
    simp [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, thermalExpectation_smul,
      thermalExpectation_neg, thermalExpectation_create_comp_annihilate_of_ne _ hij]

end SecondQuantization
