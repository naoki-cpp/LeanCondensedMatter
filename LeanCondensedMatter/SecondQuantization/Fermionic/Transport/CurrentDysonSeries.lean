import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CurrentInsertions
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.CauchySeries

set_option linter.style.header false

/-!
# Connected two-current Dyson series

A bilinear current supplies two elementary fermionic external legs. The
connected two-current series is the vacuum-normalized four-leg series minus
the product of the vacuum-normalized two-leg series for each current.

This is the cumulant of the *two composite currents*, not the four-fermion
cumulant. The diagram series are free-Gibbs specializations; identifying their
coefficients with physical time-ordered currents in all time chambers is a
separate task.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

private def currentExternalLabels (i j : Mode) : Fin (2 * 1) → ExternalFieldLabel Mode :=
  fun e => if e.val = 0 then .creation i else .annihilation j

private def currentPairExternalLabels (i j k l : Mode) :
    Fin (2 * 2) → ExternalFieldLabel Mode :=
  fun e =>
    if e.val = 0 then .creation i
    else if e.val = 1 then .annihilation j
    else if e.val = 2 then .creation k
    else .annihilation l

private def currentPairExternalTimes (τ τ' : ℝ) : Fin (2 * 2) → ℝ :=
  fun e => if e.val < 2 then τ else τ'

/-- Formal connected correlator of two bilinear currents, computed from the
existing partition-normalized arbitrary-external-insertion Dyson series.
The subtraction is a product of *two-current* one-point series, which gives a
Cauchy convolution at each perturbation order. -/
noncomputable def connectedCurrentDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ) : PowerSeries ℂ :=
  (∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
    (jx i j * jy k l) •
      partitionFunctionNormalizedExternalInsertionDysonSeries ε β g
        (currentPairExternalLabels i j k l) (currentPairExternalTimes τ τ')) -
  (∑ i : Mode, ∑ j : Mode, jx i j •
      partitionFunctionNormalizedExternalInsertionDysonSeries ε β g
        (currentExternalLabels i j) (fun _ => τ)) *
  (∑ k : Mode, ∑ l : Mode, jy k l •
      partitionFunctionNormalizedExternalInsertionDysonSeries ε β g
        (currentExternalLabels k l) (fun _ => τ'))

/-- The connected *composite-current* Dyson series is the vacuum-free four-field
series minus the product of two vacuum-free two-field series. Vacuum removal
does not itself imply that all four elementary external legs are connected. -/
theorem connectedCurrentDysonSeries_eq_vacuumFree_sub
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ) :
    connectedCurrentDysonSeries ε β g τ τ' jx jy =
      (∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
        (jx i j * jy k l) •
          vacuumFreeExternalInsertionDysonSeries ε β g
            (currentPairExternalLabels i j k l) (currentPairExternalTimes τ τ')) -
      (∑ i : Mode, ∑ j : Mode, jx i j •
        vacuumFreeExternalInsertionDysonSeries ε β g
          (currentExternalLabels i j) (fun _ => τ)) *
      (∑ k : Mode, ∑ l : Mode, jy k l •
        vacuumFreeExternalInsertionDysonSeries ε β g
          (currentExternalLabels k l) (fun _ => τ')) := by
  unfold connectedCurrentDysonSeries
  simp_rw [partitionFunctionNormalizedExternalInsertionDysonSeries_eq_vacuumFreeExternalInsertionDysonSeries
    ε β hβ g]

end Transport
end Fermionic
end SecondQuantization
