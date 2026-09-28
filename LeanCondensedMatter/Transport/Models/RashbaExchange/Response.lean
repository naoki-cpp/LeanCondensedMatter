import LeanCondensedMatter.Transport.Analysis.ContinuumMeasure
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import LeanCondensedMatter.Transport.Models.RashbaExchange.Model
import LeanCondensedMatter.Transport.Streda.ConductivityNormalization
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite Rashba-exchange anomalous-Hall response

This layer keeps Berry data, occupation, response normalization, and the final conductivity tensor
distinct. The finite clean Hall benchmark is a finite-cutoff, finite-broadening algebraic kernel:
broadening regularizes the interband denominator, while the cutoff and momentum measure remain
explicit. It is not a zero-broadening, thermodynamic, or universal Hall-value statement.

The ordered Hall kernel is defined from the model Berry curvature and supplied occupation law.
Antisymmetry is introduced only at the response boundary by the orientation of the ordered Cartesian
pair; no spin-current or device-level Hall observable is identified with this charge-current
response.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

open QuantumTheory.Transport

def UsesCanonicalMomentumMeasure (params : Parameters) : Prop :=
  params.momentumMeasureNormalization = momentumMeasurePrefactor params.hbar

/-- Lorentzian finite-broadening factor multiplying the clean interband Berry kernel. -/
def finiteBroadeningFactor (params : Parameters) (px py : ℝ) : ℝ :=
  spinOrbitEnergy params px py ^ 2 /
    (spinOrbitEnergy params px py ^ 2 + params.broadening ^ 2)

/-- Occupation-weighted finite-broadening Berry kernel before momentum integration. -/
def finiteBroadeningBerryHallKernel
    (occupationLaw : ℝ → ℝ) (params : Parameters) (px py : ℝ) : ℝ :=
  ∑ band : Band,
    occupation occupationLaw params band px py *
      berryCurvature params band px py *
        finiteBroadeningFactor params px py

/-- Orientation of an ordered Cartesian Hall pair: `xy = +1`, `yx = -1`, diagonal entries zero. -/
def hallOrientation (measured source : Fin 2) : ℝ :=
  if measured = source then 0 else if measured = 0 then 1 else -1

/-- Ordered finite clean Hall-response kernel. This is the response/vertex boundary that downstream
clean or disorder code can consume without reconstructing the model's band/Berry algebra. -/
def finiteCleanHallKernel
    (occupationLaw : ℝ → ℝ) (params : Parameters)
    (measured source : Fin 2) (px py : ℝ) : ℝ :=
  hallOrientation measured source *
    finiteBroadeningBerryHallKernel occupationLaw params px py

@[simp] theorem hallOrientation_self (direction : Fin 2) :
    hallOrientation direction direction = 0 := by
  simp [hallOrientation]

theorem hallOrientation_swap (measured source : Fin 2) :
    hallOrientation source measured = -hallOrientation measured source := by
  fin_cases measured <;> fin_cases source <;> simp [hallOrientation]

theorem finiteCleanHallKernel_swap
    (occupationLaw : ℝ → ℝ) (params : Parameters)
    (measured source : Fin 2) (px py : ℝ) :
    finiteCleanHallKernel occupationLaw params source measured px py =
      -finiteCleanHallKernel occupationLaw params measured source px py := by
  rw [finiteCleanHallKernel, finiteCleanHallKernel, hallOrientation_swap]
  ring

@[simp] theorem finiteCleanHallKernel_self
    (occupationLaw : ℝ → ℝ) (params : Parameters)
    (direction : Fin 2) (px py : ℝ) :
    finiteCleanHallKernel occupationLaw params direction direction px py = 0 := by
  simp [finiteCleanHallKernel]

@[simp] theorem finiteBroadeningBerryHallKernel_exchange_zero
    (occupationLaw : ℝ → ℝ) (params : Parameters) (px py : ℝ)
    (hDelta : params.exchangeSplitting = 0) :
    finiteBroadeningBerryHallKernel occupationLaw params px py = 0 := by
  simp [finiteBroadeningBerryHallKernel, berryCurvature_exchange_zero params _ px py hDelta]

@[simp] theorem finiteBroadeningBerryHallKernel_rashba_zero
    (occupationLaw : ℝ → ℝ) (params : Parameters) (px py : ℝ)
    (hAlpha : params.rashbaVelocity = 0) :
    finiteBroadeningBerryHallKernel occupationLaw params px py = 0 := by
  simp [finiteBroadeningBerryHallKernel, berryCurvature_rashba_zero params _ px py hAlpha]

/-- Charge-current Hall normalization before momentum integration. The two current vertices
contribute `q²`; the static trace prefactor remains the common Bastin–Středa `ℏ/(2π)`. -/
def hallResponseNormalization (params : Parameters) : ℝ :=
  params.signedCharge ^ 2 * bastinStredaTraceConductivityPrefactor params.hbar

/-- A zero carrier charge kills the physical charge-current normalization without changing the
underlying Berry data. -/
@[simp] theorem hallResponseNormalization_charge_zero
    (params : Parameters) (hq : params.signedCharge = 0) :
    hallResponseNormalization params = 0 := by
  simp [hallResponseNormalization, hq]

end
end QuantumTheory.Transport.Models.RashbaExchange
