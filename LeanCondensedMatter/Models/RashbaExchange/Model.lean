import LeanCondensedMatter.Analysis.Matrix.Pauli
import LeanCondensedMatter.QuantumTheory.TwoBand
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Finite Rashba-exchange two-band model

The momentum variables `px, py` are physical momenta. With this convention

```text
H(p) = p²/(2 m_eff) I + α_R (p_y σ_x - p_x σ_y) + Δ σ_z,
v_i = ∂H/∂p_i.
```

Thus `α_R` has velocity dimension. The clean Hamiltonian, spectrum, velocity and Berry
curvature use only `HamiltonianParameters`. The lower and upper branches are represented by
`QuantumTheory.TwoBand`; the scalar kinetic term shifts both energies equally.
The signed carrier charge, chemical potential,
finite broadening, momentum cutoff and continuum normalization are owned downstream by
`ResponseParameters`; the current vertex is defined in `Operator`.

The finite momentum disk and all response or device-level Hall observables are downstream.
No disorder or limiting procedure is assumed in this clean model.
-/

namespace QuantumTheory.Models.RashbaExchange

open QuantumTheory.TwoBand

noncomputable section

/-- The three parameters determining the clean Rashba-exchange Hamiltonian and spectrum. -/
structure HamiltonianParameters where
  /-- Effective mass in the scalar parabolic dispersion. -/
  effectiveMass : ℝ
  /-- Rashba coefficient in velocity units because the model uses physical momentum. -/
  rashbaVelocity : ℝ
  /-- Exchange splitting multiplying σ_z. -/
  exchangeSplitting : ℝ

/-- Scalar parabolic kinetic energy. -/
def kineticEnergy (params : HamiltonianParameters) (px py : ℝ) : ℝ :=
  (px ^ 2 + py ^ 2) / (2 * params.effectiveMass)

/-- Squared magnitude of the Rashba-exchange Pauli vector. -/
def spinOrbitEnergySq (params : HamiltonianParameters) (px py : ℝ) : ℝ :=
  params.rashbaVelocity ^ 2 * (px ^ 2 + py ^ 2) + params.exchangeSplitting ^ 2

/-- Magnitude of the Rashba-exchange Pauli vector. -/
def spinOrbitEnergy (params : HamiltonianParameters) (px py : ℝ) : ℝ :=
  Real.sqrt (spinOrbitEnergySq params px py)

/-- Pauli-vector coefficients (α p_y, -α p_x, Δ). -/
def rashbaPauliCoefficients (params : HamiltonianParameters) (px py : ℝ) : InternalSpace.PauliAxis → ℂ
  | .x => ((params.rashbaVelocity * py : ℝ) : ℂ)
  | .y => ((-params.rashbaVelocity * px : ℝ) : ℂ)
  | .z => ((params.exchangeSplitting : ℝ) : ℂ)

/-- Two-band Rashba-exchange Hamiltonian in physical-momentum coordinates. -/
def hamiltonian (params : HamiltonianParameters) (px py : ℝ) : InternalSpace.PauliMatrix :=
  ((kineticEnergy params px py : ℝ) : ℂ) • (1 : InternalSpace.PauliMatrix) +
    InternalSpace.pauliCombination (rashbaPauliCoefficients params px py)

/-- Energy of a selected lower or upper band. -/
def bandEnergy (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) : ℝ :=
  kineticEnergy params px py + bandSign band * spinOrbitEnergy params px py

/-- Matrix velocity operator ∂H/∂p_i for an in-plane direction. -/
def velocityOperator (params : HamiltonianParameters) (direction : Fin 2) (px py : ℝ) : InternalSpace.PauliMatrix :=
  if direction = 0 then
    (((px / params.effectiveMass : ℝ) : ℂ)) • (1 : InternalSpace.PauliMatrix) -
      ((params.rashbaVelocity : ℝ) : ℂ) • InternalSpace.pauliY
  else
    (((py / params.effectiveMass : ℝ) : ℂ)) • (1 : InternalSpace.PauliMatrix) +
      ((params.rashbaVelocity : ℝ) : ℂ) • InternalSpace.pauliX

/-- Berry curvature in physical-momentum coordinates. For the stated Rashba convention,
`Ω_b = -s_b Δ α_R² / (2 |d|³)`. -/
def berryCurvature (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) : ℝ :=
  -(bandSign band * params.exchangeSplitting * params.rashbaVelocity ^ 2) /
    (2 * spinOrbitEnergy params px py ^ 3)

@[simp] theorem berryCurvature_exchange_zero
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ)
    (hDelta : params.exchangeSplitting = 0) :
    berryCurvature params band px py = 0 := by
  simp [berryCurvature, hDelta]

@[simp] theorem berryCurvature_rashba_zero
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ)
    (hAlpha : params.rashbaVelocity = 0) :
    berryCurvature params band px py = 0 := by
  simp [berryCurvature, hAlpha]

/-- Opposite bands carry opposite Berry curvature wherever the totalized closed formula is used. -/
@[simp] theorem berryCurvature_oppositeBand
    (params : HamiltonianParameters) (band : TwoBand) (px py : ℝ) :
    berryCurvature params (oppositeBand band) px py =
      -berryCurvature params band px py := by
  simp [berryCurvature, bandSign_oppositeBand]
  ring

end
end QuantumTheory.Models.RashbaExchange
