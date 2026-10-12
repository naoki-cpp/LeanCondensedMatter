import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.NumberOperator
import Mathlib.LinearAlgebra.Span.Basic

set_option linter.style.header false

/-!
# Exact local Holstein-Primakoff representation

The natural number `twiceSpin` represents 2s. The physical subspace at a site has
occupation at most 2s. The ordering is S+ = hbar sqrt(2s-N) a and
S- = hbar a† sqrt(2s-N), with Sz = hbar(s-N).
Source: Stancil-Prabhakar, Section 2.7.1, equations (2.146), (2.149), and (2.150).
The ambient domain is algebraic bosonic Fock space. No square-root expansion,
quadratic Hamiltonian, Hilbert-space completion, or finite-dimensional CCR is assumed.
-/

namespace Models.HolsteinPrimakoff

open SecondQuantization
open SecondQuantization.Bosonic

noncomputable section
variable {Mode : Type*}

/-- The physical occupation sector at one site, with occupation at most 2s.
Other modes are spectators. A many-site physical domain imposes each site's cap. -/
def physicalSubspace (twiceSpin : ℕ) (i : Mode) : Submodule ℂ (FockSpace Mode) :=
  Submodule.span ℂ (basisState '' {n : Occupation Mode | n i ≤ twiceSpin})

/-- The square-root occupation factor sqrt(2s-N), diagonal in the occupation basis.
Only its action on the capped physical sector is interpreted as a spin operator. -/
def deviationFactor (twiceSpin : ℕ) (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  Common.diagonalOperator (fun n : Occupation Mode => (Real.sqrt ((twiceSpin : ℝ) - n i) : ℂ))

/-- Exact spin raising: sqrt(2s-N) acts after bosonic annihilation.
Stancil-Prabhakar, Section 2.7.1, equation (2.149). -/
def spinPlus (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (hbar : ℂ) • (deviationFactor twiceSpin i).comp (annihilate i)

/-- Exact spin lowering: sqrt(2s-N) acts before bosonic creation.
Stancil-Prabhakar, Section 2.7.1, equation (2.150). -/
def spinMinus (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (hbar : ℂ) • (create i).comp (deviationFactor twiceSpin i)

/-- Longitudinal spin component relative to the polarized reference.
Stancil-Prabhakar, Section 2.7.1, equation (2.146). -/
def spinZ (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (hbar : ℂ) • (((twiceSpin : ℂ) / 2) • LinearMap.id - numberOperator i)

theorem deviationFactor_basisState (twiceSpin : ℕ) (i : Mode) (n : Occupation Mode) :
    deviationFactor twiceSpin i (basisState n) =
      (Real.sqrt ((twiceSpin : ℝ) - n i) : ℂ) • basisState n := by
  exact Common.diagonalOperator_basisState _ n

theorem spinPlus_basisState (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) (n : Occupation Mode) :
    spinPlus hbar twiceSpin i (basisState n) =
      ((hbar : ℂ) * (Real.sqrt (n i : ℝ) : ℂ) *
        (Real.sqrt ((twiceSpin : ℝ) - (n i - 1 : ℕ)) : ℂ)) •
          basisState (removeOccupation i n) := by
  simp only [spinPlus, LinearMap.smul_apply, LinearMap.comp_apply,
    annihilate_basisState_eq, map_smul, deviationFactor_basisState,
    removeOccupation_apply_same, smul_smul]
  congr 1
  ring

theorem spinMinus_basisState (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) (n : Occupation Mode) :
    spinMinus hbar twiceSpin i (basisState n) =
      ((hbar : ℂ) * (Real.sqrt ((n i : ℝ) + 1) : ℂ) *
        (Real.sqrt ((twiceSpin : ℝ) - n i) : ℂ)) • basisState (createOccupation i n) := by
  simp only [spinMinus, LinearMap.smul_apply, LinearMap.comp_apply,
    deviationFactor_basisState, map_smul, create_basisState_eq, smul_smul]
  congr 1
  ring

theorem spinZ_basisState (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) (n : Occupation Mode) :
    spinZ hbar twiceSpin i (basisState n) =
      ((hbar : ℂ) * ((twiceSpin : ℂ) / 2 - n i)) • basisState n := by
  simp only [spinZ, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
    numberOperator_basisState]
  rw [← sub_smul, smul_smul]

/-- Spin raising vanishes at the fully polarized endpoint n=0. -/
theorem spinPlus_basisState_of_zero (hbar : ℝ) (twiceSpin : ℕ) (i : Mode)
    (n : Occupation Mode) (hn : n i = 0) : spinPlus hbar twiceSpin i (basisState n) = 0 := by
  simp [spinPlus_basisState, hn]

/-- Spin lowering vanishes at the endpoint n=2s, rather than leaving the physical sector. -/
theorem spinMinus_basisState_of_top (hbar : ℝ) (twiceSpin : ℕ) (i : Mode)
    (n : Occupation Mode) (hn : n i = twiceSpin) :
    spinMinus hbar twiceSpin i (basisState n) = 0 := by
  simp [spinMinus_basisState, hn]

theorem basisState_mem_physicalSubspace (twiceSpin : ℕ) (i : Mode) (n : Occupation Mode)
    (hn : n i ≤ twiceSpin) : basisState n ∈ physicalSubspace twiceSpin i :=
  Submodule.subset_span ⟨n, hn, rfl⟩

private theorem preserves_physicalSubspace (twiceSpin : ℕ) (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (hA : ∀ n : Occupation Mode, n i ≤ twiceSpin →
      A (basisState n) ∈ physicalSubspace twiceSpin i)
    (ψ : FockSpace Mode) (hψ : ψ ∈ physicalSubspace twiceSpin i) :
    A ψ ∈ physicalSubspace twiceSpin i := by
  have h : physicalSubspace twiceSpin i ≤ (physicalSubspace twiceSpin i).comap A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, hn, rfl⟩
    exact hA n hn
  exact h hψ

theorem spinPlus_mem_physicalSubspace (hbar : ℝ) (twiceSpin : ℕ) (i : Mode)
    (ψ : FockSpace Mode) (hψ : ψ ∈ physicalSubspace twiceSpin i) :
    spinPlus hbar twiceSpin i ψ ∈ physicalSubspace twiceSpin i := by
  apply preserves_physicalSubspace twiceSpin i _ _ ψ hψ
  intro n hn
  rw [spinPlus_basisState]
  apply Submodule.smul_mem
  apply basisState_mem_physicalSubspace
  simp only [removeOccupation_apply_same]
  omega

theorem spinMinus_mem_physicalSubspace (hbar : ℝ) (twiceSpin : ℕ) (i : Mode)
    (ψ : FockSpace Mode) (hψ : ψ ∈ physicalSubspace twiceSpin i) :
    spinMinus hbar twiceSpin i ψ ∈ physicalSubspace twiceSpin i := by
  apply preserves_physicalSubspace twiceSpin i _ _ ψ hψ
  intro n hn
  by_cases ht : n i = twiceSpin
  · rw [spinMinus_basisState_of_top hbar twiceSpin i n ht]
    exact Submodule.zero_mem _
  · rw [spinMinus_basisState]
    apply Submodule.smul_mem
    apply basisState_mem_physicalSubspace
    simp only [createOccupation_apply_same]
    omega

theorem spinZ_mem_physicalSubspace (hbar : ℝ) (twiceSpin : ℕ) (i : Mode)
    (ψ : FockSpace Mode) (hψ : ψ ∈ physicalSubspace twiceSpin i) :
    spinZ hbar twiceSpin i ψ ∈ physicalSubspace twiceSpin i := by
  apply preserves_physicalSubspace twiceSpin i _ _ ψ hψ
  intro n hn
  rw [spinZ_basisState]
  exact Submodule.smul_mem _ _ (basisState_mem_physicalSubspace twiceSpin i n hn)

private theorem sqrt_nat_sq (n : ℕ) :
    (Real.sqrt (n : ℝ) : ℂ) ^ 2 = n := by
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)

private theorem sqrt_deviation_sq (twiceSpin n : ℕ) (hn : n ≤ twiceSpin) :
    (Real.sqrt ((twiceSpin : ℝ) - n) : ℂ) ^ 2 = (twiceSpin : ℂ) - n := by
  have h : (0 : ℝ) ≤ (twiceSpin : ℝ) - n :=
    sub_nonneg.mpr (by exact_mod_cast hn)
  exact_mod_cast Real.sq_sqrt h

private theorem pred_cast (n : ℕ) (hn : n ≠ 0) :
    ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
  have h : ((n - 1 : ℕ) : ℂ) + 1 = (n : ℂ) := by
    exact_mod_cast (show n - 1 + 1 = n by omega)
  linear_combination h

private theorem spinPlus_spinMinus_basisState (hbar : ℝ) (twiceSpin : ℕ) (i : Mode)
    (n : Occupation Mode) (hn : n i ≤ twiceSpin) :
    spinPlus hbar twiceSpin i (spinMinus hbar twiceSpin i (basisState n)) =
      ((hbar : ℂ) ^ 2 * ((n i : ℂ) + 1) * ((twiceSpin : ℂ) - n i)) • basisState n := by
  rw [spinMinus_basisState, map_smul, spinPlus_basisState]
  simp only [createOccupation_apply_same, removeOccupation_createOccupation,
    Nat.add_sub_cancel, smul_smul, Nat.cast_add, Nat.cast_one]
  have hs := sqrt_nat_sq (n i + 1)
  push_cast at hs
  have hd := sqrt_deviation_sq twiceSpin (n i) hn
  congr 1
  calc
    _ = (hbar : ℂ) ^ 2 * (Real.sqrt ((n i : ℝ) + 1) : ℂ) ^ 2 *
        (Real.sqrt ((twiceSpin : ℝ) - n i) : ℂ) ^ 2 := by ring
    _ = _ := by rw [hs, hd]

private theorem spinMinus_spinPlus_basisState (hbar : ℝ) (twiceSpin : ℕ) (i : Mode)
    (n : Occupation Mode) (hn : n i ≤ twiceSpin) :
    spinMinus hbar twiceSpin i (spinPlus hbar twiceSpin i (basisState n)) =
      ((hbar : ℂ) ^ 2 * (n i : ℂ) * ((twiceSpin : ℂ) - n i + 1)) • basisState n := by
  by_cases hz : n i = 0
  · rw [spinPlus_basisState_of_zero hbar twiceSpin i n hz]
    simp [hz]
  · rw [spinPlus_basisState, map_smul, spinMinus_basisState,
      createOccupation_removeOccupation_of_pos hz]
    simp only [removeOccupation_apply_same, smul_smul]
    have hp : (n i - 1 : ℕ) + 1 = n i := by omega
    have hpr : ((n i - 1 : ℕ) : ℝ) + 1 = (n i : ℝ) := by exact_mod_cast hp
    rw [hpr]
    have hd := sqrt_deviation_sq twiceSpin (n i - 1) (by omega)
    congr 1
    calc
      _ = (hbar : ℂ) ^ 2 * (Real.sqrt (n i : ℝ) : ℂ) ^ 2 *
          (Real.sqrt ((twiceSpin : ℝ) - (n i - 1 : ℕ)) : ℂ) ^ 2 := by ring
      _ = _ := by rw [sqrt_nat_sq, hd, pred_cast (n i) hz]; ring

private theorem eq_on_physicalSubspace (twiceSpin : ℕ) (i : Mode)
    (A B : FockSpace Mode →ₗ[ℂ] FockSpace Mode)
    (hAB : ∀ n : Occupation Mode, n i ≤ twiceSpin → A (basisState n) = B (basisState n))
    (ψ : FockSpace Mode) (hψ : ψ ∈ physicalSubspace twiceSpin i) : A ψ = B ψ := by
  have h : physicalSubspace twiceSpin i ≤ LinearMap.ker (A - B) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, hn, rfl⟩
    change A (basisState n) - B (basisState n) = 0
    exact sub_eq_zero.mpr (hAB n hn)
  have hker := h hψ
  change A ψ - B ψ = 0 at hker
  exact sub_eq_zero.mp hker

/-- The exact local spin ladder commutator [S+, S-] = 2 hbar Sz on the physical sector.
The occupation cap is required; no unrestricted boson-spin equivalence is asserted. -/
theorem comm_spinPlus_spinMinus (hbar : ℝ) (twiceSpin : ℕ) (i : Mode)
    (ψ : FockSpace Mode) (hψ : ψ ∈ physicalSubspace twiceSpin i) :
    ScalarExchange.zetaCommutator (1 : ℂ) (spinPlus hbar twiceSpin i)
      (spinMinus hbar twiceSpin i) ψ =
        (2 * (hbar : ℂ)) • spinZ hbar twiceSpin i ψ := by
  apply eq_on_physicalSubspace twiceSpin i _
    ((2 * (hbar : ℂ)) • spinZ hbar twiceSpin i) _ ψ hψ
  intro n hn
  simp only [ScalarExchange.zetaCommutator_apply, one_smul,
    spinPlus_spinMinus_basisState hbar twiceSpin i n hn,
    spinMinus_spinPlus_basisState hbar twiceSpin i n hn,
    LinearMap.smul_apply, spinZ_basisState, smul_smul]
  rw [← sub_smul]
  congr 1
  ring

/-- [Sz, S+] = hbar S+; the ambient algebraic operator identity also holds outside the cap. -/
theorem comm_spinZ_spinPlus (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) :
    ScalarExchange.zetaCommutator (1 : ℂ) (spinZ hbar twiceSpin i)
      (spinPlus hbar twiceSpin i) = (hbar : ℂ) • spinPlus hbar twiceSpin i := by
  apply Common.linearMap_ext_basisState
  intro n
  change ScalarExchange.zetaCommutator (1 : ℂ) (spinZ hbar twiceSpin i)
    (spinPlus hbar twiceSpin i) (basisState n) =
      (hbar : ℂ) • spinPlus hbar twiceSpin i (basisState n)
  by_cases hz : n i = 0
  · simp [ScalarExchange.zetaCommutator_apply, spinPlus_basisState_of_zero,
      spinZ_basisState, hz]
  · simp only [ScalarExchange.zetaCommutator_apply, one_smul, spinPlus_basisState,
      spinZ_basisState, map_smul, removeOccupation_apply_same,
      LinearMap.smul_apply, smul_smul]
    rw [pred_cast (n i) hz, ← sub_smul]
    congr 1
    ring

/-- [Sz, S-] = -hbar S-; the ambient algebraic operator identity also holds outside the cap. -/
theorem comm_spinZ_spinMinus (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) :
    ScalarExchange.zetaCommutator (1 : ℂ) (spinZ hbar twiceSpin i)
      (spinMinus hbar twiceSpin i) = (-(hbar : ℂ)) • spinMinus hbar twiceSpin i := by
  apply Common.linearMap_ext_basisState
  intro n
  change ScalarExchange.zetaCommutator (1 : ℂ) (spinZ hbar twiceSpin i)
    (spinMinus hbar twiceSpin i) (basisState n) =
      (-(hbar : ℂ)) • spinMinus hbar twiceSpin i (basisState n)
  simp only [ScalarExchange.zetaCommutator_apply, one_smul, spinMinus_basisState,
    spinZ_basisState, map_smul, createOccupation_apply_same,
    LinearMap.smul_apply, smul_smul, Nat.cast_add, Nat.cast_one]
  rw [← sub_smul]
  congr 1
  ring

end
end Models.HolsteinPrimakoff
