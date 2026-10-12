import LeanCondensedMatter.SecondQuantization.Bosonic.Algebra.NumberOperator
import Mathlib.LinearAlgebra.Span.Basic

set_option linter.style.header false

/-!
# Exact local Holstein-Primakoff representation

The natural number `twiceSpin` represents 2s. The physical subspace at a site has
occupation at most 2s. The ordering is S+ = hbar sqrt(2s-N) a and
S- = hbar a† sqrt(2s-N), with Sz = hbar(s-N).
Source: Stancil-Prabhakar, Section 2.7.1, equations (2.146)-(2.153).
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
Stancil-Prabhakar, Section 2.7.1, equation (2.146). -/
def spinPlus (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (hbar : ℂ) • (deviationFactor twiceSpin i).comp (annihilate i)

/-- Exact spin lowering: sqrt(2s-N) acts before bosonic creation.
Stancil-Prabhakar, Section 2.7.1, equation (2.147). -/
def spinMinus (hbar : ℝ) (twiceSpin : ℕ) (i : Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  (hbar : ℂ) • (create i).comp (deviationFactor twiceSpin i)

/-- Longitudinal spin component relative to the polarized reference.
Stancil-Prabhakar, Section 2.7.1, equation (2.148). -/
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
  simp [spinZ, numberOperator_basisState, sub_smul, smul_smul]

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

end
end Models.HolsteinPrimakoff
