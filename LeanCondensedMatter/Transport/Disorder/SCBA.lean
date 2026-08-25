import LeanCondensedMatter.Transport.Disorder.Finite
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Bounded self-consistent Born data

This module provides the bounded one-particle SCBA foundation used by the conserving impurity
program in issue #688. It refines the exact finite second moment from the finite-disorder ensemble
layer to a bounded complex-linear covariance superoperator and records supplied retarded/advanced
self-consistent Born approximation (SCBA) solutions.

SCBA is not identified with the exact finite disorder average. A solution stores its self-energy
fixed-point equations and two-sided Green-operator inverse identities explicitly. The covariance
used by the retarded and advanced equations is the same operator, and adjoint compatibility is
visible data. From these assumptions the module proves the finite Ward-consistency identity

`Σᴿ - Σᴬ = C(Ḡᴿ - Ḡᴬ)`

and the retarded/advanced adjoint relation for the self-energy. The bounded algebraic foundation is
dimension-independent; finite-dimensionality is added only at ordinary-trace and finite-matrix
vertex boundaries.

No existence theorem for the nonlinear SCBA fixed point, ladder vertex, vertex-corrected
conductivity, crossed diagram, trace per unit volume, thermodynamic limit, or zero-broadening limit
is included here.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

variable {H Ω : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype Ω]

namespace FiniteDisorderEnsemble

variable (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))

/-- Finite-disorder covariance represented as a bounded complex-linear superoperator on bounded
endomorphisms. It is connected to the exact finite second moment and is required to preserve
adjoints. -/
structure FiniteCovarianceSuperoperator where
  /-- Bounded complex-linear covariance action. -/
  covariance : (H →L[ℂ] H) →L[ℂ] (H →L[ℂ] H)
  /-- Identification with the exact normalized finite second moment `E[Vω X Vω]`. -/
  covariance_eq_secondMoment : ∀ kernel,
    covariance kernel =
      ensemble.operatorAverage (fun ω =>
        (ensemble.impurityPotential ω).1 * kernel *
          (ensemble.impurityPotential ω).1)
  /-- Compatibility of the covariance action with the operator adjoint. -/
  covariance_star : ∀ kernel,
    covariance (star kernel) = star (covariance kernel)

variable (covarianceData : FiniteCovarianceSuperoperator ensemble)

/-- SCBA retarded shift `zᴿ I - H₀ - Σᴿ`. -/
noncomputable def scbaRetardedShift
    (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  algebraMap ℂ (H →L[ℂ] H) (retardedSpectralParameter energy broadening) -
    ensemble.baseHamiltonian.1 - selfEnergy

/-- SCBA advanced shift `zᴬ I - H₀ - Σᴬ`. -/
noncomputable def scbaAdvancedShift
    (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  algebraMap ℂ (H →L[ℂ] H) (advancedSpectralParameter energy broadening) -
    ensemble.baseHamiltonian.1 - selfEnergy

/-- Supplied bounded retarded/advanced SCBA solution at fixed real energy and positive broadening.
The structure records approximation equations rather than identifying these operators with the
exact ensemble average. -/
structure FiniteSCBASolution (energy broadening : ℝ) where
  /-- The SCBA regulator remains strictly positive. -/
  broadening_pos : 0 < broadening
  /-- Retarded SCBA self-energy. -/
  retardedSelfEnergy : H →L[ℂ] H
  /-- Advanced SCBA self-energy. -/
  advancedSelfEnergy : H →L[ℂ] H
  /-- Retarded SCBA Green operator. -/
  retardedGreen : H →L[ℂ] H
  /-- Advanced SCBA Green operator. -/
  advancedGreen : H →L[ℂ] H
  /-- Retarded self-energy fixed-point equation `Σᴿ = C(Ḡᴿ)`. -/
  retardedSelfEnergy_eq_covariance :
    retardedSelfEnergy = covarianceData.covariance retardedGreen
  /-- Advanced self-energy fixed-point equation `Σᴬ = C(Ḡᴬ)`. -/
  advancedSelfEnergy_eq_covariance :
    advancedSelfEnergy = covarianceData.covariance advancedGreen
  /-- The retarded shift is a left inverse of the supplied retarded Green operator. -/
  retardedShift_mul_green :
    ensemble.scbaRetardedShift energy broadening retardedSelfEnergy * retardedGreen = 1
  /-- The retarded shift is a right inverse of the supplied retarded Green operator. -/
  green_mul_retardedShift :
    retardedGreen * ensemble.scbaRetardedShift energy broadening retardedSelfEnergy = 1
  /-- The advanced shift is a left inverse of the supplied advanced Green operator. -/
  advancedShift_mul_green :
    ensemble.scbaAdvancedShift energy broadening advancedSelfEnergy * advancedGreen = 1
  /-- The advanced shift is a right inverse of the supplied advanced Green operator. -/
  green_mul_advancedShift :
    advancedGreen * ensemble.scbaAdvancedShift energy broadening advancedSelfEnergy = 1
  /-- Retarded and advanced SCBA Green operators are related by the operator adjoint. -/
  advancedGreen_eq_star_retarded :
    advancedGreen = star retardedGreen

variable {energy broadening : ℝ}
variable (solution : FiniteSCBASolution ensemble covarianceData energy broadening)

/-- The supplied SCBA self-energies inherit the retarded/advanced adjoint relation from the common
adjoint-compatible covariance superoperator. -/
theorem FiniteSCBASolution.advancedSelfEnergy_eq_star_retarded :
    solution.advancedSelfEnergy = star solution.retardedSelfEnergy := by
  calc
    solution.advancedSelfEnergy =
        covarianceData.covariance solution.advancedGreen :=
      solution.advancedSelfEnergy_eq_covariance
    _ = covarianceData.covariance (star solution.retardedGreen) :=
      congrArg covarianceData.covariance solution.advancedGreen_eq_star_retarded
    _ = star (covarianceData.covariance solution.retardedGreen) :=
      covarianceData.covariance_star solution.retardedGreen
    _ = star solution.retardedSelfEnergy :=
      congrArg star solution.retardedSelfEnergy_eq_covariance.symm

/-- Finite SCBA Ward-consistency identity. The retarded and advanced self-energy difference is the
same covariance superoperator applied to the Green-operator difference. -/
theorem FiniteSCBASolution.selfEnergy_sub_eq_covariance_green_sub :
    solution.retardedSelfEnergy - solution.advancedSelfEnergy =
      covarianceData.covariance
        (solution.retardedGreen - solution.advancedGreen) := by
  calc
    solution.retardedSelfEnergy - solution.advancedSelfEnergy =
        covarianceData.covariance solution.retardedGreen -
          covarianceData.covariance solution.advancedGreen := by
      rw [solution.retardedSelfEnergy_eq_covariance,
        solution.advancedSelfEnergy_eq_covariance]
    _ = covarianceData.covariance
        (solution.retardedGreen - solution.advancedGreen) :=
      (covarianceData.covariance.map_sub _ _).symm

/-- The supplied retarded Green operator is a unit whose inverse is its SCBA shift. -/
theorem FiniteSCBASolution.retardedGreen_isUnit :
    IsUnit solution.retardedGreen := by
  refine ⟨⟨solution.retardedGreen,
    ensemble.scbaRetardedShift energy broadening solution.retardedSelfEnergy,
    solution.green_mul_retardedShift,
    solution.retardedShift_mul_green⟩, rfl⟩

/-- The supplied advanced Green operator is a unit whose inverse is its SCBA shift. -/
theorem FiniteSCBASolution.advancedGreen_isUnit :
    IsUnit solution.advancedGreen := by
  refine ⟨⟨solution.advancedGreen,
    ensemble.scbaAdvancedShift energy broadening solution.advancedSelfEnergy,
    solution.green_mul_advancedShift,
    solution.advancedShift_mul_green⟩, rfl⟩

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
