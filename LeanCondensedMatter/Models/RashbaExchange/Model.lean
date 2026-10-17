import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite Rashba-exchange two-band model

The momentum variables `px, py` are physical momenta. With this convention

```text
H(p) = p²/(2 m_eff) I + α_R (p_y σ_x - p_x σ_y) + Δ σ_z,
v_i = ∂H/∂p_i.
```

Thus `α_R` has velocity dimension. The clean Hamiltonian, spectrum, velocity and Berry
curvature use only `HamiltonianParameters`. The signed carrier charge, chemical potential,
finite broadening, momentum cutoff and continuum normalization are owned downstream by
`ResponseParameters`; the current vertex is defined in `Operator`.

The finite momentum disk and all response or device-level Hall observables are downstream.
No disorder or limiting procedure is assumed in this clean model.
-/

namespace QuantumTheory.Models.RashbaExchange

noncomputable section

/-- The three parameters determining the clean Rashba-exchange Hamiltonian and spectrum. -/
structure HamiltonianParameters where
  /-- Effective mass in the scalar parabolic dispersion. -/
  effectiveMass : ℝ
  /-- Rashba coefficient in velocity units because the model uses physical momentum. -/
  rashbaVelocity : ℝ
  /-- Exchange splitting multiplying σ_z. -/
  exchangeSplitting : ℝ

/-- The lower and upper eigenvalue branches of the two-band Hamiltonian. -/
inductive Band where
  | lower
  | upper
  deriving DecidableEq

instance : Fintype Band where
  elems := {.lower, .upper}
  complete := by intro band; cases band <;> simp

/-- Eigenvalue-branch sign: -1 for lower and +1 for upper. -/
def bandSign : Band → ℝ
  | .lower => -1
  | .upper => 1

/-- A finite sum over the two Rashba-exchange bands. -/
theorem sum_band {M : Type*} [AddCommMonoid M] (f : Band → M) :
    ∑ band : Band, f band = f .lower + f .upper := by
  change ∑ band ∈ ({.lower, .upper} : Finset Band), f band = _
  simp

/-- The opposite branch of the two-band spectrum. -/
def oppositeBand : Band → Band
  | .lower => .upper
  | .upper => .lower

@[simp] theorem oppositeBand_lower : oppositeBand .lower = .upper := rfl
@[simp] theorem oppositeBand_upper : oppositeBand .upper = .lower := rfl

@[simp] theorem oppositeBand_oppositeBand (band : Band) :
    oppositeBand (oppositeBand band) = band := by
  cases band <;> rfl

@[simp] theorem bandSign_oppositeBand (band : Band) :
    bandSign (oppositeBand band) = -bandSign band := by
  cases band <;> simp [oppositeBand, bandSign]

@[simp] theorem bandSign_sq (band : Band) : bandSign band ^ 2 = 1 := by
  cases band <;> simp [bandSign]

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
def bandEnergy (params : HamiltonianParameters) (band : Band) (px py : ℝ) : ℝ :=
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
def berryCurvature (params : HamiltonianParameters) (band : Band) (px py : ℝ) : ℝ :=
  -(bandSign band * params.exchangeSplitting * params.rashbaVelocity ^ 2) /
    (2 * spinOrbitEnergy params px py ^ 3)

@[simp] theorem berryCurvature_exchange_zero
    (params : HamiltonianParameters) (band : Band) (px py : ℝ)
    (hDelta : params.exchangeSplitting = 0) :
    berryCurvature params band px py = 0 := by
  simp [berryCurvature, hDelta]

@[simp] theorem berryCurvature_rashba_zero
    (params : HamiltonianParameters) (band : Band) (px py : ℝ)
    (hAlpha : params.rashbaVelocity = 0) :
    berryCurvature params band px py = 0 := by
  simp [berryCurvature, hAlpha]

/-- Opposite bands carry opposite Berry curvature wherever the totalized closed formula is used. -/
@[simp] theorem berryCurvature_oppositeBand
    (params : HamiltonianParameters) (band : Band) (px py : ℝ) :
    berryCurvature params (oppositeBand band) px py =
      -berryCurvature params band px py := by
  simp [berryCurvature, bandSign_oppositeBand]
  ring

end
end QuantumTheory.Models.RashbaExchange
