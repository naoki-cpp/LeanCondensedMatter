import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.DiagonalAnalytic

set_option linter.style.header false

/-!
# Heat operators for completed diagonal Hamiltonians

A lower-bounded real configuration energy defines a bounded positive heat operator on completed
Fock space by coordinatewise multiplication with `exp (-β E(c))` for positive inverse temperature.
This is a pure-point/diagonal specialization; it does not provide a general functional calculus for
unbounded self-adjoint operators.
-/

namespace SecondQuantization
namespace Common

noncomputable section

variable {Config : Type*}

private theorem completedDiagonalHeatWeight_bound
    (energy : Config → ℝ) (β E₀ : ℝ) (hβ : 0 < β)
    (hlower : ∀ c, E₀ ≤ energy c) (c : Config) :
    ‖(Real.exp (-β * energy c) : ℂ)‖ ≤ Real.exp (-β * E₀) := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_exp.mpr
  have hmul : 0 ≤ β * (energy c - E₀) :=
    mul_nonneg hβ.le (sub_nonneg.mpr (hlower c))
  nlinarith

/-- Bounded heat multiplication associated with a lower-bounded diagonal energy. -/
noncomputable def completedDiagonalHeatOperator
    (energy : Config → ℝ) (β E₀ : ℝ) (hβ : 0 < β)
    (hlower : ∀ c, E₀ ≤ energy c) :
    CompletedFock Config →L[ℂ] CompletedFock Config :=
  completedBoundedDiagonalOperator
    (fun c => (Real.exp (-β * energy c) : ℂ))
    (Real.exp_nonneg (-β * E₀))
    (completedDiagonalHeatWeight_bound energy β E₀ hβ hlower)

/-- The heat operator acts coordinatewise by the Boltzmann factor. -/
@[simp]
theorem completedDiagonalHeatOperator_apply
    (energy : Config → ℝ) (β E₀ : ℝ) (hβ : 0 < β)
    (hlower : ∀ c, E₀ ≤ energy c)
    (ψ : CompletedFock Config) (c : Config) :
    completedDiagonalHeatOperator energy β E₀ hβ hlower ψ c =
      (Real.exp (-β * energy c) : ℂ) * ψ c := by
  exact completedBoundedDiagonalOperator_apply
    (fun c => (Real.exp (-β * energy c) : ℂ))
    (Real.exp_nonneg (-β * E₀))
    (completedDiagonalHeatWeight_bound energy β E₀ hβ hlower) ψ c

/-- The heat-operator norm is bounded by the Boltzmann factor at the supplied lower energy bound. -/
theorem norm_completedDiagonalHeatOperator_le
    (energy : Config → ℝ) (β E₀ : ℝ) (hβ : 0 < β)
    (hlower : ∀ c, E₀ ≤ energy c) :
    ‖completedDiagonalHeatOperator energy β E₀ hβ hlower‖ ≤ Real.exp (-β * E₀) := by
  exact norm_completedBoundedDiagonalOperator_le
    (fun c => (Real.exp (-β * energy c) : ℂ))
    (Real.exp_nonneg (-β * E₀))
    (completedDiagonalHeatWeight_bound energy β E₀ hβ hlower)

/-- Canonical configuration basis states are heat-operator eigenvectors with Boltzmann eigenvalue. -/
@[simp]
theorem completedDiagonalHeatOperator_basisState
    (energy : Config → ℝ) (β E₀ : ℝ) (hβ : 0 < β)
    (hlower : ∀ c, E₀ ≤ energy c) (c : Config) :
    completedDiagonalHeatOperator energy β E₀ hβ hlower (completedBasisState c) =
      (Real.exp (-β * energy c) : ℂ) • completedBasisState c := by
  exact completedBoundedDiagonalOperator_basisState
    (fun c => (Real.exp (-β * energy c) : ℂ))
    (Real.exp_nonneg (-β * E₀))
    (completedDiagonalHeatWeight_bound energy β E₀ hβ hlower) c

/-- A completed diagonal heat operator is positive. -/
theorem completedDiagonalHeatOperator_isPositive
    (energy : Config → ℝ) (β E₀ : ℝ) (hβ : 0 < β)
    (hlower : ∀ c, E₀ ≤ energy c) :
    (completedDiagonalHeatOperator energy β E₀ hβ hlower).IsPositive := by
  exact completedBoundedDiagonalOperator_isPositive_of_nonneg
    (fun c => Real.exp (-β * energy c))
    (Real.exp_nonneg (-β * E₀))
    (completedDiagonalHeatWeight_bound energy β E₀ hβ hlower)
    (fun c => Real.exp_nonneg _)

/-- A completed diagonal heat operator is self-adjoint. -/
theorem completedDiagonalHeatOperator_isSelfAdjoint
    (energy : Config → ℝ) (β E₀ : ℝ) (hβ : 0 < β)
    (hlower : ∀ c, E₀ ≤ energy c) :
    (completedDiagonalHeatOperator energy β E₀ hβ hlower).IsSelfAdjoint :=
  (completedDiagonalHeatOperator_isPositive energy β E₀ hβ hlower).isSelfAdjoint

/-- On a nonempty configuration space, the completed diagonal heat operator is nonzero. -/
theorem completedDiagonalHeatOperator_ne_zero [Nonempty Config]
    (energy : Config → ℝ) (β E₀ : ℝ) (hβ : 0 < β)
    (hlower : ∀ c, E₀ ≤ energy c) :
    completedDiagonalHeatOperator energy β E₀ hβ hlower ≠ 0 := by
  classical
  let c : Config := Classical.choice (inferInstance : Nonempty Config)
  intro hzero
  have happly := congrArg
    (fun T : CompletedFock Config →L[ℂ] CompletedFock Config => T (completedBasisState c)) hzero
  rw [completedDiagonalHeatOperator_basisState] at happly
  have hcoord := congrArg (fun ψ : CompletedFock Config => ψ c) happly
  simp at hcoord

/-- Every eigenvector of the maximal diagonal Hamiltonian is an eigenvector of its bounded heat
operator with the expected Boltzmann eigenvalue. -/
theorem completedDiagonalHeatOperator_apply_of_eigenvector
    (energy : Config → ℝ) (β E₀ : ℝ) (hβ : 0 < β)
    (hlower : ∀ c, E₀ ≤ energy c)
    (x : (completedDiagonalOperator (fun c => (energy c : ℂ))).domain) (E : ℝ)
    (hx :
      completedDiagonalOperator (fun c => (energy c : ℂ)) x =
        (E : ℂ) • (x : CompletedFock Config)) :
    completedDiagonalHeatOperator energy β E₀ hβ hlower (x : CompletedFock Config) =
      (Real.exp (-β * E) : ℂ) • (x : CompletedFock Config) := by
  ext c
  rw [completedDiagonalHeatOperator_apply]
  by_cases hc : (x : CompletedFock Config) c = 0
  · simp [hc]
  · have hcoord := congrArg (fun ψ : CompletedFock Config => ψ c) hx
    rw [completedDiagonalOperator_apply] at hcoord
    change (energy c : ℂ) * (x : CompletedFock Config) c =
      (E : ℂ) * (x : CompletedFock Config) c at hcoord
    have henergyComplex : (energy c : ℂ) = (E : ℂ) :=
      mul_right_cancel₀ hc hcoord
    have henergy : energy c = E := Complex.ofReal_injective henergyComplex
    rw [henergy]
    rfl

end
end Common
end SecondQuantization
