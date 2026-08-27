import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Bounded self-consistent Born data

This module provides the bounded one-particle SCBA foundation used by the conserving impurity
program in issue #688. It consumes the canonical exact finite second-moment bounded complex-linear
map from the finite-disorder moment layer and records supplied retarded/advanced self-consistent
Born approximation (SCBA) solutions.

SCBA is not identified with the exact finite disorder average. A solution stores its self-energy
fixed-point equations, a two-sided inverse identity for the retarded Green operator, and the
retarded/advanced adjoint relation. The advanced inverse identities are then derived by adjointing
the retarded identities. Both retarded and advanced fixed-point equations use the same canonical
second-moment action, whose complex linearity and adjoint compatibility are proved upstream from
the finite ensemble. The module derives

`Σᴿ - Σᴬ = C₂(Ḡᴿ - Ḡᴬ)`

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

/-- Adjointing a retarded SCBA shift gives the advanced shift with adjointed self-energy. -/
theorem star_scbaRetardedShift
    (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) :
    star (ensemble.scbaRetardedShift energy broadening selfEnergy) =
      ensemble.scbaAdvancedShift energy broadening (star selfEnergy) := by
  unfold scbaRetardedShift scbaAdvancedShift
  rw [star_sub, star_sub, ensemble.baseHamiltonian.2.star_eq]
  simp [Algebra.algebraMap_eq_smul_one]

/-- Supplied bounded retarded/advanced SCBA solution at fixed real energy and positive broadening.
The structure records approximation equations rather than identifying these operators with the
exact ensemble average. The self-energy map is the canonical exact second-moment action `C₂`; no
separate covariance object or compatibility proof is supplied. Only the retarded two-sided inverse
identities are supplied: the advanced inverse identities follow from adjoint compatibility. -/
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
  /-- Retarded self-energy fixed-point equation `Σᴿ = C₂(Ḡᴿ)`. -/
  retardedSelfEnergy_eq_secondMoment :
    retardedSelfEnergy = ensemble.exactSecondMoment retardedGreen
  /-- Advanced self-energy fixed-point equation `Σᴬ = C₂(Ḡᴬ)`. -/
  advancedSelfEnergy_eq_secondMoment :
    advancedSelfEnergy = ensemble.exactSecondMoment advancedGreen
  /-- The retarded shift is a left inverse of the supplied retarded Green operator. -/
  retardedShift_mul_green :
    ensemble.scbaRetardedShift energy broadening retardedSelfEnergy * retardedGreen = 1
  /-- The retarded shift is a right inverse of the supplied retarded Green operator. -/
  green_mul_retardedShift :
    retardedGreen * ensemble.scbaRetardedShift energy broadening retardedSelfEnergy = 1
  /-- Retarded and advanced SCBA Green operators are related by the operator adjoint. -/
  advancedGreen_eq_star_retarded :
    advancedGreen = star retardedGreen

variable {energy broadening : ℝ}
variable (solution : FiniteSCBASolution ensemble energy broadening)

/-- The supplied SCBA self-energies inherit the retarded/advanced adjoint relation from the
canonical adjoint-compatible exact second-moment action. -/
theorem FiniteSCBASolution.advancedSelfEnergy_eq_star_retarded :
    solution.advancedSelfEnergy = star solution.retardedSelfEnergy := by
  calc
    solution.advancedSelfEnergy =
        ensemble.exactSecondMoment solution.advancedGreen :=
      solution.advancedSelfEnergy_eq_secondMoment
    _ = ensemble.exactSecondMoment (star solution.retardedGreen) :=
      congrArg ensemble.exactSecondMoment solution.advancedGreen_eq_star_retarded
    _ = star (ensemble.exactSecondMoment solution.retardedGreen) :=
      ensemble.exactSecondMoment_star solution.retardedGreen
    _ = star solution.retardedSelfEnergy :=
      congrArg star solution.retardedSelfEnergy_eq_secondMoment.symm

/-- The advanced SCBA shift is the adjoint of the retarded SCBA shift. -/
theorem FiniteSCBASolution.advancedShift_eq_star_retardedShift :
    ensemble.scbaAdvancedShift energy broadening solution.advancedSelfEnergy =
      star (ensemble.scbaRetardedShift energy broadening solution.retardedSelfEnergy) := by
  rw [ensemble.star_scbaRetardedShift]
  rw [solution.advancedSelfEnergy_eq_star_retarded]

/-- The advanced shift is a left inverse of the advanced Green operator, derived by adjointing the
retarded right-inverse identity. -/
theorem FiniteSCBASolution.advancedShift_mul_green :
    ensemble.scbaAdvancedShift energy broadening solution.advancedSelfEnergy *
        solution.advancedGreen = 1 := by
  simpa only [star_mul, star_one, solution.advancedShift_eq_star_retardedShift,
    solution.advancedGreen_eq_star_retarded] using
    congrArg star solution.green_mul_retardedShift

/-- The advanced shift is a right inverse of the advanced Green operator, derived by adjointing the
retarded left-inverse identity. -/
theorem FiniteSCBASolution.green_mul_advancedShift :
    solution.advancedGreen *
        ensemble.scbaAdvancedShift energy broadening solution.advancedSelfEnergy = 1 := by
  simpa only [star_mul, star_one, solution.advancedShift_eq_star_retardedShift,
    solution.advancedGreen_eq_star_retarded] using
    congrArg star solution.retardedShift_mul_green

/-- Finite SCBA Ward-consistency identity. The retarded and advanced self-energy difference is the
canonical exact second-moment action applied to the Green-operator difference. -/
theorem FiniteSCBASolution.selfEnergy_sub_eq_secondMoment_green_sub :
    solution.retardedSelfEnergy - solution.advancedSelfEnergy =
      ensemble.exactSecondMoment
        (solution.retardedGreen - solution.advancedGreen) := by
  calc
    solution.retardedSelfEnergy - solution.advancedSelfEnergy =
        ensemble.exactSecondMoment solution.retardedGreen -
          ensemble.exactSecondMoment solution.advancedGreen := by
      rw [solution.retardedSelfEnergy_eq_secondMoment,
        solution.advancedSelfEnergy_eq_secondMoment]
    _ = ensemble.exactSecondMoment
        (solution.retardedGreen - solution.advancedGreen) :=
      (ensemble.exactSecondMoment_sub _ _).symm

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
