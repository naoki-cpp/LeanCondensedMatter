import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Diagonal
import LeanCondensedMatter.SecondQuantization.Bosonic.CompletedSpace.Ladder

set_option linter.style.header false

/-!
# Product domains for completed bosonic ladder operators

For one bosonic mode `i`, both mixed ladder products are naturally defined on the maximal
single-mode number-operator domain. This file proves the required domain inclusions and packages

`aᵢ† aᵢ` and `aᵢ aᵢ†`

as honest linear maps with source `Dom(Nᵢ)`. Their coordinate actions recover `Nᵢ` and
`Nᵢ + 1`, respectively, so the equal-mode completed CCR is an identity of linear maps on this
explicit common domain.
-/

namespace SecondQuantization
namespace Bosonic

open scoped ENNReal

noncomputable section

variable {Mode : Type*}

private theorem sqrt_natCast_le_natCast_add_one (k : ℕ) :
    Real.sqrt (k : ℝ) ≤ (k : ℝ) + 1 := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hk : 0 ≤ (k : ℝ) := by positivity
    nlinarith

private theorem sqrt_natCast_add_one_le_natCast_add_one (k : ℕ) :
    Real.sqrt ((k : ℝ) + 1) ≤ (k : ℝ) + 1 := by
  apply (Real.sqrt_le_self_iff).2
  right
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  linarith

private theorem norm_sqrt_natCast_le_norm_natCast_add_one (k : ℕ) :
    ‖(Real.sqrt (k : ℝ) : ℂ)‖ ≤ ‖(k : ℂ) + 1‖ := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hcast : (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) := by
    norm_num
  rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact sqrt_natCast_le_natCast_add_one k

private theorem norm_sqrt_natCast_add_one_le_norm_natCast_add_one (k : ℕ) :
    ‖(Real.sqrt ((k : ℝ) + 1) : ℂ)‖ ≤ ‖(k : ℂ) + 1‖ := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hcast : (k : ℂ) + 1 = (((k : ℝ) + 1 : ℝ) : ℂ) := by
    norm_num
  rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact sqrt_natCast_add_one_le_natCast_add_one k

private theorem mem_completedNumberOperatorDomain_add_one
    (i : Mode) {ψ : CompletedFockSpace Mode}
    (hψ : ψ ∈ completedNumberOperatorDomain i) :
    ψ ∈ Common.completedDiagonalDomain (fun n : Occupation Mode => (n i : ℂ) + 1) := by
  exact Common.mem_completedDiagonalDomain_add_const
    (fun n : Occupation Mode => (n i : ℂ)) 1 hψ

/-- The number-operator domain lies in the annihilation domain. -/
theorem completedNumberOperatorDomain_le_completedAnnihilateDomain (i : Mode) :
    completedNumberOperatorDomain i ≤ completedAnnihilateDomain i := by
  intro ψ hψ
  rw [Common.mem_completedDiagonalDomain_iff]
  have hshift :=
    mem_completedNumberOperatorDomain_add_one i hψ
  rw [Common.mem_completedDiagonalDomain_iff] at hshift
  exact hshift.mono' fun n => by
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_sqrt_natCast_le_norm_natCast_add_one (n i)) (norm_nonneg _)

/-- The number-operator domain lies in the creation domain. -/
theorem completedNumberOperatorDomain_le_completedCreateDomain (i : Mode) :
    completedNumberOperatorDomain i ≤ completedCreateDomain i := by
  intro ψ hψ
  rw [Common.mem_completedDiagonalDomain_iff]
  have hshift :=
    mem_completedNumberOperatorDomain_add_one i hψ
  rw [Common.mem_completedDiagonalDomain_iff] at hshift
  exact hshift.mono' fun n => by
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (norm_sqrt_natCast_add_one_le_norm_natCast_add_one (n i)) (norm_nonneg _)

/-- On `Dom(Nᵢ)`, annihilation lands in the creation domain. -/
theorem completedAnnihilate_mem_completedCreateDomain_of_mem_completedNumberOperatorDomain
    (i : Mode) (ψ : completedNumberOperatorDomain i) :
    completedAnnihilate i
        ⟨(ψ : CompletedFockSpace Mode),
          completedNumberOperatorDomain_le_completedAnnihilateDomain i ψ.2⟩ ∈
      completedCreateDomain i := by
  rw [Common.mem_completedDiagonalDomain_iff]
  have hmem :=
    lp.memℓp
      (Common.completedCoordinatePullback
        (createOccupation i) (createOccupation_injective i)
        (completedNumberOperator i ψ))
  convert hmem using 1
  funext n
  rw [completedAnnihilate_apply, Common.completedCoordinatePullback_apply]
  change
    (Real.sqrt (n i + 1 : ℝ) : ℂ) *
        ((Real.sqrt (n i + 1 : ℝ) : ℂ) *
          (ψ : CompletedFockSpace Mode) (createOccupation i n)) =
      ((createOccupation i n i : ℂ) *
        (ψ : CompletedFockSpace Mode) (createOccupation i n))
  rw [← mul_assoc]
  have hsqrt := sqrt_natCast_mul_self (n i + 1)
  rw [show (Real.sqrt (n i + 1 : ℝ) : ℂ) *
      (Real.sqrt (n i + 1 : ℝ) : ℂ) = (n i + 1 : ℂ) by
        simpa [Nat.cast_add, Nat.cast_one] using hsqrt]
  rw [createOccupation_apply_same]
  norm_num

/-- On `Dom(Nᵢ)`, creation lands in the annihilation domain. -/
theorem completedCreate_mem_completedAnnihilateDomain_of_mem_completedNumberOperatorDomain
    (i : Mode) (ψ : completedNumberOperatorDomain i) :
    completedCreate i
        ⟨(ψ : CompletedFockSpace Mode),
          completedNumberOperatorDomain_le_completedCreateDomain i ψ.2⟩ ∈
      completedAnnihilateDomain i := by
  rw [Common.mem_completedDiagonalDomain_iff]
  have hshift :=
    mem_completedNumberOperatorDomain_add_one i ψ.2
  let x :
      (Common.completedDiagonalOperator
        (fun n : Occupation Mode => (n i : ℂ) + 1)).domain :=
    ⟨(ψ : CompletedFockSpace Mode), hshift⟩
  have hmem :=
    lp.memℓp
      (Common.completedCoordinateEmbedding
        (createOccupation i) (createOccupation_injective i)
        (Common.completedDiagonalOperator
          (fun n : Occupation Mode => (n i : ℂ) + 1) x))
  convert hmem using 1
  funext n
  rw [Common.completedCoordinateEmbedding_apply]
  by_cases hni : n i = 0
  · rw [hni]
    simp only [Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero, zero_mul]
    rw [Function.extend_apply']
    · rfl
    · intro h
      rcases h with ⟨m, hm⟩
      have hcoord := congrArg (fun q : Occupation Mode => q i) hm
      rw [createOccupation_apply_same, hni] at hcoord
      omega
  · have hrepr : createOccupation i (removeOccupation i n) = n :=
      createOccupation_removeOccupation_of_pos hni
    have hcoord : (removeOccupation i n) i + 1 = n i := by
      have h := congrArg (fun q : Occupation Mode => q i) hrepr
      simpa only [createOccupation_apply_same] using h
    conv_rhs => rw [← hrepr]
    rw [(createOccupation_injective i).extend_apply,
      completedCreate_apply, ite_eq_right hni,
      Common.completedDiagonalOperator_apply]
    dsimp [x]
    change
      (Real.sqrt (n i : ℝ) : ℂ) *
          ((Real.sqrt (n i : ℝ) : ℂ) *
            (ψ : CompletedFockSpace Mode) (removeOccupation i n)) =
        (((removeOccupation i n) i : ℂ) + 1) *
          (ψ : CompletedFockSpace Mode) (removeOccupation i n)
    rw [← mul_assoc, sqrt_natCast_mul_self]
    exact congrArg
      (fun z : ℂ => z * (ψ : CompletedFockSpace Mode) (removeOccupation i n))
      (by exact_mod_cast hcoord)

private theorem mem_completedNumberOperatorDomain_of_annihilate_mem_createDomain
    (i : Mode) {ψ : CompletedFockSpace Mode} (hψ : ψ ∈ completedAnnihilateDomain i)
    (hout :
      completedAnnihilate i ⟨ψ, hψ⟩ ∈ completedCreateDomain i) :
    ψ ∈ completedNumberOperatorDomain i := by
  change ψ ∈ Common.completedDiagonalDomain
    (fun n : Occupation Mode => (n i : ℂ))
  rw [Common.mem_completedDiagonalDomain_iff]
  let y : (completedCreate i).domain :=
    ⟨completedAnnihilate i ⟨ψ, hψ⟩, hout⟩
  have hmem :=
    lp.memℓp
      (Common.completedCoordinateEmbedding
        (createOccupation i) (createOccupation_injective i)
        (Common.completedDiagonalOperator
          (fun n : Occupation Mode => (Real.sqrt (n i + 1 : ℝ) : ℂ)) y))
  convert hmem using 1
  funext n
  rw [Common.completedCoordinateEmbedding_apply]
  by_cases hni : n i = 0
  · rw [hni]
    simp only [Nat.cast_zero, zero_mul]
    rw [Function.extend_apply']
    · rfl
    · intro h
      rcases h with ⟨m, hm⟩
      have hcoord := congrArg (fun q : Occupation Mode => q i) hm
      rw [createOccupation_apply_same, hni] at hcoord
      omega
  · have hrepr : createOccupation i (removeOccupation i n) = n :=
      createOccupation_removeOccupation_of_pos hni
    have hcoord : (removeOccupation i n) i + 1 = n i := by
      have h := congrArg (fun q : Occupation Mode => q i) hrepr
      simpa only [createOccupation_apply_same] using h
    conv_rhs => rw [← hrepr]
    rw [(createOccupation_injective i).extend_apply]
    change
      (n i : ℂ) * ψ n =
        (Real.sqrt ((removeOccupation i n) i + 1 : ℝ) : ℂ) *
          ((Real.sqrt ((removeOccupation i n) i + 1 : ℝ) : ℂ) *
            ψ (createOccupation i (removeOccupation i n)))
    rw [hrepr, ← mul_assoc]
    have hsqrt := sqrt_natCast_mul_self (n i)
    rw [show (Real.sqrt ((removeOccupation i n) i + 1 : ℝ) : ℂ) *
        (Real.sqrt ((removeOccupation i n) i + 1 : ℝ) : ℂ) = (n i : ℂ) by
          rw [show ((removeOccupation i n) i : ℝ) + 1 = (n i : ℝ) by
            exact_mod_cast hcoord]
          exact hsqrt]

private theorem mem_completedNumberOperatorDomain_of_create_mem_annihilateDomain
    (i : Mode) {ψ : CompletedFockSpace Mode} (hψ : ψ ∈ completedCreateDomain i)
    (hout :
      completedCreate i ⟨ψ, hψ⟩ ∈ completedAnnihilateDomain i) :
    ψ ∈ completedNumberOperatorDomain i := by
  have hplus :
      ψ ∈ Common.completedDiagonalDomain
        (fun n : Occupation Mode => (n i : ℂ) + 1) := by
    rw [Common.mem_completedDiagonalDomain_iff]
    let y : (completedAnnihilate i).domain :=
      ⟨completedCreate i ⟨ψ, hψ⟩, hout⟩
    have hmem :=
      lp.memℓp
        (Common.completedCoordinatePullback
          (createOccupation i) (createOccupation_injective i)
          (Common.completedDiagonalOperator
            (fun n : Occupation Mode => (Real.sqrt (n i : ℝ) : ℂ)) y))
    convert hmem using 1
    funext n
    rw [Common.completedCoordinatePullback_apply]
    change
      ((n i : ℂ) + 1) * ψ n =
        (Real.sqrt (createOccupation i n i : ℝ) : ℂ) *
          (completedCreate i ⟨ψ, hψ⟩) (createOccupation i n)
    rw [completedCreate_apply]
    have hpos : createOccupation i n i ≠ 0 := by
      rw [createOccupation_apply_same]
      omega
    rw [ite_eq_right hpos, removeOccupation_createOccupation,
      createOccupation_apply_same, ← mul_assoc]
    have hsqrt := sqrt_natCast_mul_self (n i + 1)
    simpa [Nat.cast_add, Nat.cast_one] using
      (congrArg (fun z : ℂ => z * ψ n) hsqrt).symm
  have hback :=
    Common.mem_completedDiagonalDomain_add_const
      (fun n : Occupation Mode => (n i : ℂ) + 1) (-1) hplus
  change ψ ∈ Common.completedDiagonalDomain
    (fun n : Occupation Mode => (n i : ℂ))
  simpa only [add_neg_cancel_right] using hback

/-- The maximal domain of `aᵢ† aᵢ` is exactly the number-operator domain. -/
theorem mem_completedNumberOperatorDomain_iff_annihilate_mem_completedCreateDomain
    (i : Mode) (ψ : CompletedFockSpace Mode) :
    ψ ∈ completedNumberOperatorDomain i ↔
      ∃ hψ : ψ ∈ completedAnnihilateDomain i,
        completedAnnihilate i ⟨ψ, hψ⟩ ∈ completedCreateDomain i := by
  constructor
  · intro hψ
    let x : completedNumberOperatorDomain i := ⟨ψ, hψ⟩
    exact
      ⟨completedNumberOperatorDomain_le_completedAnnihilateDomain i hψ,
        completedAnnihilate_mem_completedCreateDomain_of_mem_completedNumberOperatorDomain i x⟩
  · rintro ⟨hψ, hout⟩
    exact mem_completedNumberOperatorDomain_of_annihilate_mem_createDomain i hψ hout

/-- The maximal domain of `aᵢ aᵢ†` is exactly the number-operator domain. -/
theorem mem_completedNumberOperatorDomain_iff_create_mem_completedAnnihilateDomain
    (i : Mode) (ψ : CompletedFockSpace Mode) :
    ψ ∈ completedNumberOperatorDomain i ↔
      ∃ hψ : ψ ∈ completedCreateDomain i,
        completedCreate i ⟨ψ, hψ⟩ ∈ completedAnnihilateDomain i := by
  constructor
  · intro hψ
    let x : completedNumberOperatorDomain i := ⟨ψ, hψ⟩
    exact
      ⟨completedNumberOperatorDomain_le_completedCreateDomain i hψ,
        completedCreate_mem_completedAnnihilateDomain_of_mem_completedNumberOperatorDomain i x⟩
  · rintro ⟨hψ, hout⟩
    exact mem_completedNumberOperatorDomain_of_create_mem_annihilateDomain i hψ hout

/-- Annihilation restricted from `Dom(Nᵢ)` to its natural domain. -/
private noncomputable def completedAnnihilateFromNumberDomain (i : Mode) :
    completedNumberOperatorDomain i →ₗ[ℂ] (completedAnnihilate i).domain :=
  Submodule.inclusion (completedNumberOperatorDomain_le_completedAnnihilateDomain i)

/-- Creation restricted from `Dom(Nᵢ)` to its natural domain. -/
private noncomputable def completedCreateFromNumberDomain (i : Mode) :
    completedNumberOperatorDomain i →ₗ[ℂ] (completedCreate i).domain :=
  Submodule.inclusion (completedNumberOperatorDomain_le_completedCreateDomain i)

private noncomputable def completedAnnihilateIntoCreateDomain (i : Mode) :
    completedNumberOperatorDomain i →ₗ[ℂ] (completedCreate i).domain :=
  LinearMap.codRestrict
    (completedCreate i).domain
    ((completedAnnihilate i).toFun.comp (completedAnnihilateFromNumberDomain i))
    (fun ψ =>
      completedAnnihilate_mem_completedCreateDomain_of_mem_completedNumberOperatorDomain i ψ)

private noncomputable def completedCreateIntoAnnihilateDomain (i : Mode) :
    completedNumberOperatorDomain i →ₗ[ℂ] (completedAnnihilate i).domain :=
  LinearMap.codRestrict
    (completedAnnihilate i).domain
    ((completedCreate i).toFun.comp (completedCreateFromNumberDomain i))
    (fun ψ =>
      completedCreate_mem_completedAnnihilateDomain_of_mem_completedNumberOperatorDomain i ψ)

/-- The product `aᵢ† aᵢ` as an honest linear map on `Dom(Nᵢ)`. -/
noncomputable def completedCreateAfterAnnihilate (i : Mode) :
    completedNumberOperatorDomain i →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedCreate i).toFun.comp (completedAnnihilateIntoCreateDomain i)

/-- The product `aᵢ aᵢ†` as an honest linear map on `Dom(Nᵢ)`. -/
noncomputable def completedAnnihilateAfterCreate (i : Mode) :
    completedNumberOperatorDomain i →ₗ[ℂ] CompletedFockSpace Mode :=
  (completedAnnihilate i).toFun.comp (completedCreateIntoAnnihilateDomain i)

/-- On its product domain, `aᵢ† aᵢ = Nᵢ`. -/
theorem completedCreateAfterAnnihilate_eq_numberOperator (i : Mode) :
    completedCreateAfterAnnihilate i = (completedNumberOperator i).toFun := by
  apply LinearMap.ext
  intro ψ
  apply lp.ext
  funext n
  change
    completedCreate i
        ⟨completedAnnihilate i
            ⟨(ψ : CompletedFockSpace Mode),
              completedNumberOperatorDomain_le_completedAnnihilateDomain i ψ.2⟩,
          completedAnnihilate_mem_completedCreateDomain_of_mem_completedNumberOperatorDomain i ψ⟩ n =
      (n i : ℂ) * (ψ : CompletedFockSpace Mode) n
  rw [completedCreate_apply]
  by_cases hni : n i = 0
  · rw [ite_eq_left hni, hni]
    simp
  · rw [ite_eq_right hni, completedAnnihilate_apply]
    have hrepr : createOccupation i (removeOccupation i n) = n :=
      createOccupation_removeOccupation_of_pos hni
    have hcoord : (removeOccupation i n) i + 1 = n i := by
      have h := congrArg (fun q : Occupation Mode => q i) hrepr
      simpa only [createOccupation_apply_same] using h
    have hcoord_real : ((removeOccupation i n) i : ℝ) + 1 = (n i : ℝ) := by
      exact_mod_cast hcoord
    rw [hcoord_real, ← mul_assoc, sqrt_natCast_mul_self, hrepr]

/-- On the common product domain, `aᵢ aᵢ† = aᵢ† aᵢ + 1`. Combined with
`completedCreateAfterAnnihilate_eq_numberOperator`, this is `aᵢ aᵢ† = Nᵢ + 1`. -/
theorem completedAnnihilateAfterCreate_eq_createAfterAnnihilate_add_id (i : Mode) :
    completedAnnihilateAfterCreate i =
      completedCreateAfterAnnihilate i + (completedNumberOperatorDomain i).subtype := by
  apply LinearMap.ext
  intro ψ
  apply lp.ext
  funext n
  change
    completedAnnihilate i
        ⟨completedCreate i
            ⟨(ψ : CompletedFockSpace Mode),
              completedNumberOperatorDomain_le_completedCreateDomain i ψ.2⟩,
          completedCreate_mem_completedAnnihilateDomain_of_mem_completedNumberOperatorDomain i ψ⟩ n =
      completedCreateAfterAnnihilate i ψ n + (ψ : CompletedFockSpace Mode) n
  rw [completedCreateAfterAnnihilate_eq_numberOperator]
  change
    completedAnnihilate i
        ⟨completedCreate i
            ⟨(ψ : CompletedFockSpace Mode),
              completedNumberOperatorDomain_le_completedCreateDomain i ψ.2⟩,
          completedCreate_mem_completedAnnihilateDomain_of_mem_completedNumberOperatorDomain i ψ⟩ n =
      (n i : ℂ) * (ψ : CompletedFockSpace Mode) n +
        (ψ : CompletedFockSpace Mode) n
  rw [completedAnnihilate_apply, completedCreate_apply]
  have hpos : createOccupation i n i ≠ 0 := by
    rw [createOccupation_apply_same]
    omega
  rw [ite_eq_right hpos, removeOccupation_createOccupation]
  have hsqrt := sqrt_natCast_mul_self (n i + 1)
  rw [← mul_assoc]
  rw [show (Real.sqrt (n i + 1 : ℝ) : ℂ) *
      (Real.sqrt (createOccupation i n i : ℝ) : ℂ) = ((n i : ℂ) + 1) by
        rw [createOccupation_apply_same]
        simpa [Nat.cast_add, Nat.cast_one] using hsqrt]
  ring

/-- Equal-mode completed bosonic CCR on the explicit common product domain `Dom(Nᵢ)`. -/
theorem completedComm_annihilate_create_self (i : Mode) :
    completedAnnihilateAfterCreate i - completedCreateAfterAnnihilate i =
      (completedNumberOperatorDomain i).subtype := by
  rw [completedAnnihilateAfterCreate_eq_createAfterAnnihilate_add_id]
  abel

end
end Bosonic
end SecondQuantization
