import LeanCondensedMatter.Transport.Disorder.Moments
import LeanCondensedMatter.Transport.Resolvent.Basic
import LeanCondensedMatter.Transport.Resolvent.SelfEnergy

set_option linter.style.header false

/-!
# Bounded self-consistent Born data

This module provides the bounded one-particle SCBA foundation used by the conserving impurity
program in issue #688. It consumes the canonical exact finite second-moment bounded complex-linear
map from the finite-disorder moment layer and records supplied retarded self-consistent Born
approximation (SCBA) data. Advanced data are derived by adjoint through the common `SpectralSide`
interface.

SCBA is not identified with the exact finite disorder average. A solution stores only its retarded
self-energy fixed-point equation and a two-sided inverse identity for the retarded Green operator.
The advanced Green operator and self-energy are derived by adjoint compatibility, while side-indexed
fixed-point and inverse equations are proved from that supplied retarded data. Both spectral sides use
the same canonical second-moment action, whose complex linearity and adjoint compatibility are proved
upstream from the finite ensemble. The module derives

`Σᴿ - Σᴬ = C₂(Ḡᴿ - Ḡᴬ)`

and exposes side-indexed fixed-point, inverse, and unit APIs without separate retarded/advanced
routing definitions. The bounded algebraic foundation is dimension-independent;
finite-dimensionality is added only at ordinary-trace and finite-matrix vertex boundaries.

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

/-- Side-indexed SCBA shift `zˢ I - H₀ - Σˢ`. -/
noncomputable def scbaShift
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))
    (side : SpectralSide) (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) : H →L[ℂ] H :=
  algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
    ensemble.baseHamiltonian.1 - selfEnergy

private theorem star_scbaShift_retarded
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω))
    (energy broadening : ℝ) (selfEnergy : H →L[ℂ] H) :
    star (ensemble.scbaShift .retarded energy broadening selfEnergy) =
      ensemble.scbaShift .advanced energy broadening (star selfEnergy) := by
  unfold scbaShift
  rw [spectralParameter_retarded, spectralParameter_advanced]
  rw [star_sub, star_sub, ensemble.baseHamiltonian.2.star_eq]
  simp [Algebra.algebraMap_eq_smul_one, retardedSpectralParameter,
    advancedSpectralParameter, sub_eq_add_neg]

/-- Supplied bounded retarded SCBA solution at fixed real energy and positive broadening.
The structure records approximation equations rather than identifying these operators with the
exact ensemble average. The self-energy map is the canonical exact second-moment action `C₂`; no
separate covariance object or compatibility proof is supplied. Advanced Green and self-energy data
are derived by adjoint, so only the independent retarded fixed-point and two-sided inverse identities
are stored. -/
structure FiniteSCBASolution
    (ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω)) (energy broadening : ℝ) where
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
    ensemble.scbaShift .retarded energy broadening retardedSelfEnergy * retardedGreen = 1
  /-- The retarded shift is a right inverse of the supplied retarded Green operator. -/
  green_mul_retardedShift :
    retardedGreen * ensemble.scbaShift .retarded energy broadening retardedSelfEnergy = 1

namespace FiniteSCBASolution

variable {ensemble : FiniteDisorderEnsemble (H := H) (Ω := Ω)}
variable {energy broadening : ℝ}
variable (solution : FiniteSCBASolution ensemble energy broadening)

/-- SCBA Green operator on either spectral side. The advanced branch is the adjoint of the supplied
retarded branch. -/
noncomputable def green (side : SpectralSide) : H →L[ℂ] H :=
  match side with
  | .retarded => solution.retardedGreen
  | .advanced => star solution.retardedGreen

/-- SCBA self-energy on either spectral side. The advanced branch is the adjoint of the supplied
retarded branch. -/
noncomputable def selfEnergy (side : SpectralSide) : H →L[ℂ] H :=
  match side with
  | .retarded => solution.retardedSelfEnergy
  | .advanced => star solution.retardedSelfEnergy

/-- The SCBA self-energy satisfies the same canonical second-moment fixed-point equation on either
spectral side. The advanced case is derived from retarded data by adjoint compatibility. -/
theorem selfEnergy_eq_secondMoment (side : SpectralSide) :
    solution.selfEnergy side = ensemble.exactSecondMoment (solution.green side) := by
  cases side with
  | retarded =>
      exact solution.retardedSelfEnergy_eq_secondMoment
  | advanced =>
      change star solution.retardedSelfEnergy =
        ensemble.exactSecondMoment (star solution.retardedGreen)
      calc
        star solution.retardedSelfEnergy =
            star (ensemble.exactSecondMoment solution.retardedGreen) :=
          congrArg star solution.retardedSelfEnergy_eq_secondMoment
        _ = ensemble.exactSecondMoment (star solution.retardedGreen) :=
          (ensemble.exactSecondMoment_star solution.retardedGreen).symm

/-- The side-indexed SCBA shift is a left inverse of the side-indexed Green operator. -/
theorem shift_mul_green (side : SpectralSide) :
    ensemble.scbaShift side energy broadening (solution.selfEnergy side) *
        solution.green side = 1 := by
  cases side with
  | retarded =>
      exact solution.retardedShift_mul_green
  | advanced =>
      change ensemble.scbaShift .advanced energy broadening (star solution.retardedSelfEnergy) *
        star solution.retardedGreen = 1
      simpa only [star_mul, star_one, ensemble.star_scbaShift_retarded] using
        congrArg star solution.green_mul_retardedShift

/-- The side-indexed Green operator is a left inverse of its side-indexed SCBA shift. -/
theorem green_mul_shift (side : SpectralSide) :
    solution.green side *
        ensemble.scbaShift side energy broadening (solution.selfEnergy side) = 1 := by
  cases side with
  | retarded =>
      exact solution.green_mul_retardedShift
  | advanced =>
      change star solution.retardedGreen *
        ensemble.scbaShift .advanced energy broadening (star solution.retardedSelfEnergy) = 1
      simpa only [star_mul, star_one, ensemble.star_scbaShift_retarded] using
        congrArg star solution.retardedShift_mul_green

/-- The SCBA self-energy satisfies both abstract Dyson orientations on either spectral side. -/
theorem isSelfEnergy (side : SpectralSide) :
    IsSelfEnergy
      (spectralResolvent side ensemble.baseHamiltonian.1 energy broadening)
      (solution.green side)
      (solution.selfEnergy side) := by
  refine IsSelfEnergy.of_shift
    (freeShift :=
      algebraMap ℂ (H →L[ℂ] H) (spectralParameter side energy broadening) -
        ensemble.baseHamiltonian.1)
    (dressedShift :=
      ensemble.scbaShift side energy broadening (solution.selfEnergy side))
    ?_ ?_ ?_ ?_ ?_
  · exact spectralResolvent_mul_spectralShift
      side ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energy broadening (ne_of_gt solution.broadening_pos)
  · exact spectralShift_mul_spectralResolvent
      side ensemble.baseHamiltonian.1 ensemble.baseHamiltonian.2
      energy broadening (ne_of_gt solution.broadening_pos)
  · exact solution.shift_mul_green side
  · exact solution.green_mul_shift side
  · unfold FiniteDisorderEnsemble.scbaShift
    noncomm_ring

/-- Finite SCBA Ward-consistency identity. The retarded and advanced self-energy difference is the
canonical exact second-moment action applied to the Green-operator difference. -/
theorem selfEnergy_sub_eq_secondMoment_green_sub :
    solution.selfEnergy .retarded - solution.selfEnergy .advanced =
      ensemble.exactSecondMoment
        (solution.green .retarded - solution.green .advanced) := by
  rw [solution.selfEnergy_eq_secondMoment .retarded,
    solution.selfEnergy_eq_secondMoment .advanced]
  exact (ensemble.exactSecondMoment_sub _ _).symm

/-- The side-indexed SCBA Green operator is a unit whose inverse is its side-indexed shift. -/
theorem green_isUnit (side : SpectralSide) :
    IsUnit (solution.green side) := by
  refine ⟨⟨solution.green side,
    ensemble.scbaShift side energy broadening (solution.selfEnergy side),
    solution.green_mul_shift side,
    solution.shift_mul_green side⟩, rfl⟩

end FiniteSCBASolution

end FiniteDisorderEnsemble

end
end Transport
end QuantumTheory
