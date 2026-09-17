import LeanCondensedMatter.Analysis.PowerSeries
import LeanCondensedMatter.Combinatorics.Cumulant.ConnectedDecompositionInversion

set_option linter.style.header false

/-!
# Formal source generating functionals

This module packages the normalized source-side part of a finite linked-cluster expansion.  A
generating functional is represented by its normalized formal moments on finite sets of external
insertions; taking their finite-set cumulant gives the connected source coefficients.  The
pre-normalization source series and its vacuum division belong to a later concrete layer.

The representation is deliberately statistics-independent and does not introduce Grassmann
variables.  Fermionic signs and diagram amplitudes remain in the concrete external-insertion
layers that supply the normalized moments.
-/

namespace SecondQuantization
namespace Common

open Combinatorics

/--
A normalized source generating functional over a commutative coefficient ring.

The `moment` field stores the source moments after any vacuum normalization has already been
performed.  Its `connected` transform is the source-side linked-cluster operation used by concrete
diagram expansions.
-/
structure GeneratingFunctional (Source R : Type*) [DecidableEq Source] [CommRing R] where
  /-- Moment assigned to each finite set of source insertions. -/
  moment : NormalizedSetFunction Source R

namespace GeneratingFunctional

variable {Source R : Type*} [DecidableEq Source] [CommRing R]

/-- The connected source coefficients of a normalized generating functional. -/
noncomputable def connected (Z : GeneratingFunctional Source R) :
    NormalizedSetFunction Source R :=
  Z.moment.cumulant

@[simp]
theorem connected_apply (Z : GeneratingFunctional Source R) (S : Finset Source) :
    Z.connected S = Finpartition.cumulantFromMoment Z.moment S := by
  rfl

/-- Connected source coefficients reconstruct the normalized source moments. -/
theorem connected_moment (Z : GeneratingFunctional Source R) :
    Z.connected.moment = Z.moment := by
  exact NormalizedSetFunction.moment_cumulant Z.moment

/-- A normalized source functional whose moments are total weights of a multiplicative connected
decomposition has connected coefficients equal to the connected-object contribution. -/
theorem connected_eq_connectedContribution
    {D : ConnectedDecomposition Source} (Z : GeneratingFunctional Source R)
    (W : MultiplicativeWeight D R)
    (hMoment : ∀ S, Z.moment S = W.objectMoment S)
    {S : Finset Source} (hS : S ≠ ∅) :
    Z.connected S = W.connectedContribution S := by
  change Finpartition.cumulantFromMoment Z.moment.toFun S = W.connectedContribution S
  rw [show Z.moment.toFun = W.objectMoment from funext hMoment]
  exact W.cumulantFromMoment_objectMoment hS

end GeneratingFunctional

/--
The source functional encoded by the factorial-normalized coefficients of a normalized formal
power series.  This is the abstract source-side view of the formal logarithm/cumulant bridge.
-/
noncomputable def powerSeriesGeneratingFunctional
    {Source : Type*} [DecidableEq Source]
    (Z : PowerSeries ℂ) (hZ : PowerSeries.constantCoeff Z = 1) :
    GeneratingFunctional Source ℂ where
  moment :=
    { toFun := fun S => Combinatorics.powerSeriesMomentCoeff Z S.card
      map_empty := by
        simpa [Combinatorics.powerSeriesMomentCoeff,
          PowerSeries.coeff_zero_eq_constantCoeff] using hZ }

/-- The formal logarithm coefficient is the connected coefficient of its source functional. -/
theorem factorial_mul_coeff_logOf_normalizeByConstantCoeff_eq_connected
    {Z : PowerSeries ℂ} (hZ : PowerSeries.constantCoeff Z ≠ 0)
    {Source : Type*} [DecidableEq Source] {S : Finset Source} (hS : S ≠ ∅) :
    (S.card.factorial : ℂ) *
        PowerSeries.coeff S.card
          (PowerSeries.logOf (PowerSeries.normalizeByConstantCoeff Z)) =
      (powerSeriesGeneratingFunctional
        (Source := Source) (PowerSeries.normalizeByConstantCoeff Z)
        (PowerSeries.constantCoeff_normalizeByConstantCoeff hZ)).connected S := by
  change (S.card.factorial : ℂ) *
      PowerSeries.coeff S.card
        (PowerSeries.logOf (PowerSeries.normalizeByConstantCoeff Z)) =
    Finpartition.cumulantFromMoment
      (fun T : Finset Source =>
        Combinatorics.powerSeriesMomentCoeff
          (PowerSeries.normalizeByConstantCoeff Z) T.card) S
  exact Combinatorics.factorial_mul_coeff_logOf_eq_cumulantFromMoment
    (PowerSeries.constantCoeff_normalizeByConstantCoeff hZ) hS

end Common
end SecondQuantization
