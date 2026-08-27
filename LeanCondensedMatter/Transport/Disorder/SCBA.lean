import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Resolvent.Basic

set_option linter.style.header false

/-!
# Bounded self-consistent Born data

This module provides the bounded one-particle SCBA foundation used by the conserving impurity
program in issue #688. It consumes the canonical exact finite second-moment bounded complex-linear
map from the finite-disorder moment layer and records supplied self-consistent Born approximation
(SCBA) data.

SCBA is not identified with the exact finite disorder average. A solution stores independent
retarded self-energy and Green data, the retarded fixed-point equation, and a two-sided inverse
identity. The advanced data are derived by adjoint. Retarded and advanced access are exposed through
`SpectralSide`, so the sign of the imaginary regulator is owned by the common spectral-side API
rather than duplicated throughout the SCBA layer. The canonical second-moment action is adjoint
compatible, which derives the advanced fixed-point equation from the retarded one. The module also
derives

`Σᴿ - Σᴬ = C₂(Ḡᴿ - Ḡᴬ)`.

The bounded algebraic foundation is dimension-independent; finite-dimensionality is added only at
ordinary-trace and finite-matrix vertex boundaries. Exact Born/Dyson identities whose
noncommutative product orientation changes under adjoint remain intentionally outside this
side-indexed commonization.

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

/-- Side-indexed SCBA shift `zˢ I - H₀ - Σˢ`. -/
noncomputable def scbaShift
    (side : SpectralSide) (energy broadening : ℝ)
    (selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
    ensemble.baseHamiltonian.1 - selfEnergy

/-- SCBA retarded shift `zᴿ I - H₀ - Σᴿ`. -/
noncomputable def scbaRetardedShift
    (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.scbaShift .retarded energy broadening selfEnergy

/-- SCBA advanced shift `zᴬ I - H₀ - Σᴬ`. -/
noncomputable def scbaAdvancedShift
    (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  ensemble.scbaShift .advanced energy broadening selfEnergy

@[simp]
theorem scbaShift_retarded
    (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) :
    ensemble.scbaShift .retarded energy broadening selfEnergy =
      ensemble.scbaRetardedShift energy broadening selfEnergy := rfl

@[simp]
theorem scbaShift_advanced
    (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) :
    ensemble.scbaShift .advanced energy broadening selfEnergy =
      ensemble.scbaAdvancedShift energy broadening selfEnergy := rfl

/-- Adjointing a retarded SCBA shift gives the advanced shift with adjointed self-energy. -/
theorem star_scbaRetardedShift
    (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) :
    star (ensemble.scbaRetardedShift energy broadening selfEnergy) =
      ensemble.scbaAdvancedShift energy broadening (star selfEnergy) := by
  unfold scbaRetardedShift scbaAdvancedShift scbaShift
  rw [star_sub, star_sub, ensemble.baseHamiltonian.2.star_eq]
  simp [spectralParameter, SpectralSide.sign, Algebra.algebraMap_eq_smul_one]

/-- Supplied bounded SCBA solution at fixed real energy and positive broadening.

Only independent retarded data are stored. Advanced Green and self-energy data are derived by
adjoint, and the side-indexed accessors below expose both retarded and advanced quantities. The
self-energy map is the canonical exact second-moment action `C₂`; this structure records an
approximate SCBA fixed point rather than identifying it with the exact finite disorder average. -/
structure FiniteSCBASolution (energy broadening : ℝ) where
  /-- The SCBA regulator remains strictly positive. -/
  broadening_pos : 0 < broadening
  /-- Retarded SCBA self-energy. -/
  retardedSelfEnergy : H →L[ℂ] H
  /-- Retarded SCBA Green operator. -/
  retardedGreen : H →L[ℂ] H
  /-- Retarded self-energy fixed-point equation `Σᴿ = C₂(Ḡᴿ)`. -/
  retardedSelfEnergy_eq_secondMoment :
    retardedSelfEnergy = ensemble.exactSecondMoment retardedGreen
  /-- The retarded shift is a left inverse of the supplied retarded Green operator. -/
  retardedShift_mul_green :
    ensemble.scbaRetardedShift energy broadening retardedSelfEnergy * retardedGreen = 1
  /-- The retarded shift is a right inverse of the supplied retarded Green operator. -/
  green_mul_retardedShift :
    retardedGreen * ensemble.scbaRetardedShift energy broadening retardedSelfEnergy = 1

namespace FiniteSCBASolution

variable {ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω)}
variable {energy broadening : ℝ}
variable (solution : FiniteSCBASolution ensemble energy broadening)

/-- Side-indexed SCBA Green operator. The advanced value is derived as the adjoint of the supplied
retarded Green operator. -/
noncomputable def green (side : SpectralSide) : H →L[ℂ] H :=
  match side with
  | .retarded => solution.retardedGreen
  | .advanced => star solution.retardedGreen

/-- Side-indexed SCBA self-energy. The advanced value is derived as the adjoint of the supplied
retarded self-energy. -/
noncomputable def selfEnergy (side : SpectralSide) : H →L[ℂ] H :=
  match side with
  | .retarded => solution.retardedSelfEnergy
  | .advanced => star solution.retardedSelfEnergy

@[simp]
theorem green_retarded :
    solution.green .retarded = solution.retardedGreen := rfl

@[simp]
theorem green_advanced :
    solution.green .advanced = star solution.retardedGreen := rfl

@[simp]
theorem selfEnergy_retarded :
    solution.selfEnergy .retarded = solution.retardedSelfEnergy := rfl

@[simp]
theorem selfEnergy_advanced :
    solution.selfEnergy .advanced = star solution.retardedSelfEnergy := rfl

/-- Advanced SCBA Green operator, retained as the conventional physics-facing specialization of the
side-indexed Green API. -/
noncomputable def advancedGreen : H →L[ℂ] H :=
  solution.green .advanced

/-- Advanced SCBA self-energy, retained as the conventional physics-facing specialization of the
side-indexed self-energy API. -/
noncomputable def advancedSelfEnergy : H →L[ℂ] H :=
  solution.selfEnergy .advanced

/-- The advanced Green operator is the adjoint of the retarded Green operator. -/
@[simp]
theorem advancedGreen_eq_star_retarded :
    solution.advancedGreen = star solution.retardedGreen := rfl

/-- The advanced self-energy is the adjoint of the retarded self-energy. -/
@[simp]
theorem advancedSelfEnergy_eq_star_retarded :
    solution.advancedSelfEnergy = star solution.retardedSelfEnergy := rfl

/-- The advanced SCBA fixed-point equation follows from the retarded equation and adjoint
compatibility of the exact second-moment action. -/
theorem advancedSelfEnergy_eq_secondMoment :
    solution.advancedSelfEnergy =
      ensemble.exactSecondMoment solution.advancedGreen := by
  calc
    solution.advancedSelfEnergy = star solution.retardedSelfEnergy :=
      solution.advancedSelfEnergy_eq_star_retarded
    _ = star (ensemble.exactSecondMoment solution.retardedGreen) :=
      congrArg star solution.retardedSelfEnergy_eq_secondMoment
    _ = ensemble.exactSecondMoment (star solution.retardedGreen) :=
      (ensemble.exactSecondMoment_star solution.retardedGreen).symm
    _ = ensemble.exactSecondMoment solution.advancedGreen := by
      rw [solution.advancedGreen_eq_star_retarded]

/-- Both spectral sides satisfy the same SCBA fixed-point equation. -/
theorem selfEnergy_eq_secondMoment (side : SpectralSide) :
    solution.selfEnergy side = ensemble.exactSecondMoment (solution.green side) := by
  cases side with
  | retarded =>
      simpa [selfEnergy, green] using solution.retardedSelfEnergy_eq_secondMoment
  | advanced =>
      simpa [selfEnergy, green, advancedSelfEnergy, advancedGreen] using
        solution.advancedSelfEnergy_eq_secondMoment

/-- The advanced SCBA shift is the adjoint of the retarded SCBA shift. -/
theorem advancedShift_eq_star_retardedShift :
    ensemble.scbaAdvancedShift energy broadening solution.advancedSelfEnergy =
      star (ensemble.scbaRetardedShift energy broadening solution.retardedSelfEnergy) := by
  simpa [advancedSelfEnergy, selfEnergy] using
    (ensemble.star_scbaRetardedShift energy broadening solution.retardedSelfEnergy).symm

/-- The advanced shift is a left inverse of the advanced Green operator, derived by adjointing the
retarded right-inverse identity. -/
theorem advancedShift_mul_green :
    ensemble.scbaAdvancedShift energy broadening solution.advancedSelfEnergy *
        solution.advancedGreen = 1 := by
  simpa only [star_mul, star_one, solution.advancedShift_eq_star_retardedShift,
    solution.advancedGreen_eq_star_retarded] using
    congrArg star solution.green_mul_retardedShift

/-- The advanced shift is a right inverse of the advanced Green operator, derived by adjointing the
retarded left-inverse identity. -/
theorem green_mul_advancedShift :
    solution.advancedGreen *
        ensemble.scbaAdvancedShift energy broadening solution.advancedSelfEnergy = 1 := by
  simpa only [star_mul, star_one, solution.advancedShift_eq_star_retardedShift,
    solution.advancedGreen_eq_star_retarded] using
    congrArg star solution.retardedShift_mul_green

/-- The side-indexed SCBA shift is a left inverse of the side-indexed Green operator. -/
theorem shift_mul_green (side : SpectralSide) :
    ensemble.scbaShift side energy broadening (solution.selfEnergy side) *
        solution.green side = 1 := by
  cases side with
  | retarded =>
      simpa [selfEnergy, green, scbaRetardedShift] using solution.retardedShift_mul_green
  | advanced =>
      simpa [selfEnergy, green, scbaAdvancedShift, advancedSelfEnergy, advancedGreen] using
        solution.advancedShift_mul_green

/-- The side-indexed Green operator is a right inverse of the side-indexed SCBA shift. -/
theorem green_mul_shift (side : SpectralSide) :
    solution.green side *
        ensemble.scbaShift side energy broadening (solution.selfEnergy side) = 1 := by
  cases side with
  | retarded =>
      simpa [selfEnergy, green, scbaRetardedShift] using solution.green_mul_retardedShift
  | advanced =>
      simpa [selfEnergy, green, scbaAdvancedShift, advancedSelfEnergy, advancedGreen] using
        solution.green_mul_advancedShift

/-- Finite SCBA Ward-consistency identity. The retarded and advanced self-energy difference is the
canonical exact second-moment action applied to the Green-operator difference. -/
theorem selfEnergy_sub_eq_secondMoment_green_sub :
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

/-- Either side-indexed SCBA Green operator is a unit whose inverse is its SCBA shift. -/
theorem green_isUnit (side : SpectralSide) :
    IsUnit (solution.green side) := by
  refine ⟨⟨solution.green side,
    ensemble.scbaShift side energy broadening (solution.selfEnergy side),
    solution.green_mul_shift side,
    solution.shift_mul_green side⟩, rfl⟩

/-- The supplied retarded Green operator is a unit whose inverse is its SCBA shift. -/
theorem retardedGreen_isUnit :
    IsUnit solution.retardedGreen := by
  simpa using solution.green_isUnit .retarded

/-- The derived advanced Green operator is a unit whose inverse is its SCBA shift. -/
theorem advancedGreen_isUnit :
    IsUnit solution.advancedGreen := by
  simpa [advancedGreen] using solution.green_isUnit .advanced

end FiniteSCBASolution

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
