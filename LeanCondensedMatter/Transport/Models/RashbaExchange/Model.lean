import LeanCondensedMatter.Analysis.InternalSpace.Pauli
import LeanCondensedMatter.Transport.Analysis.BandOccupation
import LeanCondensedMatter.Transport.Analysis.FourierGeometry
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

/-- Physical and normalization data for one finite Rashba-exchange benchmark. -/
structure Parameters where
  /-- Effective mass in the scalar parabolic dispersion. -/
  effectiveMass : ℝ
  /-- Rashba coefficient in velocity units because the model uses physical momentum. -/
  rashbaVelocity : ℝ
  /-- Exchange splitting multiplying σ_z. -/
  exchangeSplitting : ℝ
  /-- Chemical potential used as the Green-function probe energy. -/
  chemicalPotential : ℝ
  /-- Finite radial physical-momentum cutoff. -/
  momentumCutoff : ℝ
  /-- Positive retarded/advanced spectral broadening. -/
  broadening : ℝ
  /-- Signed carrier charge in the convention j = q v. -/
  signedCharge : ℝ
  /-- Reduced Planck constant. -/
  hbar : ℝ
  /-- Explicit normalization multiplying the two-dimensional momentum integral. -/
  momentumMeasureNormalization : ℝ

/-- Regular finite-parameter regime used by analytic statements about the benchmark. -/
structure Parameters.IsRegular (params : Parameters) : Prop where
  effectiveMass_pos : 0 < params.effectiveMass
  momentumCutoff_nonneg : 0 ≤ params.momentumCutoff
  broadening_pos : 0 < params.broadening
  hbar_pos : 0 < params.hbar

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

/-- Membership in the finite closed momentum disk. -/
def inMomentumDomain (params : Parameters) (px py : ℝ) : Prop :=
  momentumSq2D px py ≤ params.momentumCutoff ^ 2


/-- Scalar parabolic kinetic energy. -/
def kineticEnergy (params : Parameters) (px py : ℝ) : ℝ :=
  momentumSq2D px py / (2 * params.effectiveMass)

/-- Squared magnitude of the Rashba-exchange Pauli vector. -/
def spinOrbitEnergySq (params : Parameters) (px py : ℝ) : ℝ :=
  params.rashbaVelocity ^ 2 * momentumSq2D px py + params.exchangeSplitting ^ 2

/-- Magnitude of the Rashba-exchange Pauli vector. -/
def spinOrbitEnergy (params : Parameters) (px py : ℝ) : ℝ :=
  Real.sqrt (spinOrbitEnergySq params px py)

/-- Pauli-vector coefficients (α p_y, -α p_x, Δ). -/
def rashbaPauliCoefficients (params : Parameters) (px py : ℝ) : InternalSpace.PauliAxis → ℂ
  | .x => ((params.rashbaVelocity * py : ℝ) : ℂ)
  | .y => ((-params.rashbaVelocity * px : ℝ) : ℂ)
  | .z => ((params.exchangeSplitting : ℝ) : ℂ)

/-- Two-band Rashba-exchange Hamiltonian in physical-momentum coordinates. -/
def hamiltonian (params : Parameters) (px py : ℝ) : InternalSpace.PauliMatrix :=
  ((kineticEnergy params px py : ℝ) : ℂ) • (1 : InternalSpace.PauliMatrix) +
    InternalSpace.pauliCombination (rashbaPauliCoefficients params px py)

/-- Energy of a selected lower or upper band. -/
def bandEnergy (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  kineticEnergy params px py + bandSign band * spinOrbitEnergy params px py

/-- Band energy measured relative to the chemical potential. -/
def relativeBandEnergy (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  bandEnergy params band px py - params.chemicalPotential

/-- Consumer-supplied occupation law evaluated on energy relative to the chemical potential. -/
def occupation
    (occupationLaw : ℝ → ℝ) (params : Parameters) (band : Band) (px py : ℝ) : ℝ :=
  bandStateOccupation occupationLaw
    (fun b (p : ℝ × ℝ) => relativeBandEnergy params b p.1 p.2)
    band (px, py)

/-- Matrix velocity operator ∂H/∂p_i for an in-plane direction. -/
def velocityOperator (params : Parameters) (direction : Fin 2) (px py : ℝ) : InternalSpace.PauliMatrix :=
  if direction = 0 then
    (((px / params.effectiveMass : ℝ) : ℂ)) • (1 : InternalSpace.PauliMatrix) -
      ((params.rashbaVelocity : ℝ) : ℂ) • InternalSpace.pauliY
  else
    (((py / params.effectiveMass : ℝ) : ℂ)) • (1 : InternalSpace.PauliMatrix) +
      ((params.rashbaVelocity : ℝ) : ℂ) • InternalSpace.pauliX

/-- Charge-current matrix operator in the convention j_i = q v_i. -/
def currentOperator (params : Parameters) (direction : Fin 2) (px py : ℝ) : InternalSpace.PauliMatrix :=
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

/-- Opposite bands carry opposite Berry curvature wherever the totalized closed formula is used. -/
@[simp] theorem berryCurvature_oppositeBand
    (params : Parameters) (band : Band) (px py : ℝ) :
    berryCurvature params (oppositeBand band) px py =
      -berryCurvature params band px py := by
  simp [berryCurvature, bandSign_oppositeBand]
  ring

end
end QuantumTheory.Transport.Models.RashbaExchange
