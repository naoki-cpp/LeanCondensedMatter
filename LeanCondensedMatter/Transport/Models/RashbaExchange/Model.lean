import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.Transport.Analysis.BandOccupation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite Rashba-exchange two-band model

The momentum variables `px, py` are physical momenta. With this convention

```text
H(p) = p²/(2 m_eff) I + α_R (p_y σ_x - p_x σ_y) + Δ σ_z,
v_i = ∂H/∂p_i,
j_i = q v_i.
```

Thus `α_R` has velocity dimension. `signedCharge` is the carrier charge itself, so electrons use
a negative value. Chemical potential and the occupation law remain explicit and separate: the
spectrum is model data, while occupation is supplied by a consumer through the generic
`bandStateOccupation` interface.

The two-dimensional momentum domain is the closed disk `p_x² + p_y² ≤ p_max²`; `p_max` is kept
finite. No disorder, zero-broadening limit, or device-level Hall observable is introduced here.
-/

namespace QuantumTheory.Transport.Models.RashbaExchange

noncomputable section

abbrev Matrix2 := InternalSpace.PauliMatrix
abbrev PauliAxis := InternalSpace.PauliAxis

structure Parameters where
  effectiveMass : ℝ
  rashbaVelocity : ℝ
  exchangeSplitting : ℝ
  chemicalPotential : ℝ
  momentumCutoff : ℝ
  broadening : ℝ
  signedCharge : ℝ
  hbar : ℝ
  momentumMeasureNormalization : ℝ

structure Parameters.IsRegular (params : Parameters) : Prop where
  effectiveMass_pos : 0 < params.effectiveMass
  momentumCutoff_nonneg : 0 ≤ params.momentumCutoff
  broadening_pos : 0 < params.broadening
  hbar_pos : 0 < params.hbar

inductive Band where
  | lower
  | upper
  deriving DecidableEq

instance : Fintype Band where
  elems := {.lower, .upper}
  complete := by intro band; cases band <;> simp

def bandSign : Band → ℝ
  | .lower => -1
  | .upper => 1

def radialMomentumSq (px py : ℝ) : ℝ := px ^ 2 + py ^ 2

def inMomentumDomain (params : Parameters) (px py : ℝ) : Prop :=
  radialMomentumSq px py ≤ params.momentumCutoff ^ 2

def kineticEnergy (params : Parameters) (px py : ℝ) : ℝ :=
  radialMomentumSq px py / (2 * params.effectiveMass)

def spinOrbitEnergySq (params : Parameters) (px py : ℝ) : ℝ :=
  params.rashbaVelocity ^ 2 * radialMomentumSq px py + params.exchangeSplitting ^ 2

def spinOrbitEnergy (params : Parameters) (px py : ℝ) : ℝ :=
  Real.sqrt (spinOrbitEnergySq params px py)

def rashbaPauliCoefficients (params : Parameters) (px py : ℝ) : PauliAxis → ℂ
  | .x => ((params.rashbaVelocity * py : ℝ) : ℂ)
  | .y => ((-params.rashbaVelocity * px : ℝ) : ℂ)
  | .z => ((params.exchangeSplitting : ℝ) : ℂ)

def hamiltonian (params : Parameters) (px py : ℝ) : Matrix2 :=
  ((kineticEnergy params px py : ℝ) : ℂ) • (1 : Matrix2) +
    InternalSpace.pauliCombination (rashbaPauliCoefficients params px py)

def bandEnergy (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  kineticEnergy params px py + bandSign band * spinOrbitEnergy params px py

def relativeBandEnergy (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  bandEnergy params band px py - params.chemicalPotential

def occupation
    (occupationLaw : ℝ → ℝ) (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  bandStateOccupation occupationLaw
    (fun b (p : ℝ × ℝ) => relativeBandEnergy params b p.1 p.2)
    band (px, py)

def velocityOperator (params : Parameters) (direction : Fin 2) (px py : ℝ) : Matrix2 :=
  if direction = 0 then
    (((px / params.effectiveMass : ℝ) : ℂ)) • (1 : Matrix2) -
      ((params.rashbaVelocity : ℝ) : ℂ) • InternalSpace.pauliY
  else
    (((py / params.effectiveMass : ℝ) : ℂ)) • (1 : Matrix2) +
      ((params.rashbaVelocity : ℝ) : ℂ) • InternalSpace.pauliX

def currentOperator (params : Parameters) (direction : Fin 2) (px py : ℝ) : Matrix2 :=
  (((params.signedCharge : ℝ) : ℂ)) • velocityOperator params direction px py

/-- Berry curvature in physical-momentum coordinates. For the stated Rashba convention,
`Ω_b = -s_b Δ α_R² / (2 |d|³)`. -/
def berryCurvature (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  -(bandSign band * params.exchangeSplitting * params.rashbaVelocity ^ 2) /
    (2 * spinOrbitEnergy params px py ^ 3)

@[simp] theorem berryCurvature_exchange_zero
    (params : Parameters) (band : Band) (px py : ℝ)
    (hDelta : params.exchangeSplitting = 0) :
    berryCurvature params band px py = 0 := by
  simp [berryCurvature, hDelta]

@[simp] theorem berryCurvature_rashba_zero
    (params : Parameters) (band : Band) (px py : ℝ)
    (hAlpha : params.rashbaVelocity = 0) :
    berryCurvature params band px py = 0 := by
  simp [berryCurvature, hAlpha]

end
end QuantumTheory.Transport.Models.RashbaExchange
