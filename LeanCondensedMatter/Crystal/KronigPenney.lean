import LeanCondensedMatter.Crystal.Brillouin
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite Kronig–Penney Bloch-band benchmark

This module fixes one finite one-dimensional square-potential benchmark. One cell has a well of
width `wellWidth` at zero potential followed by a barrier of width `barrierWidth` and height
`barrierHeight`; their sum is the lattice period. Energies are restricted to a finite closed
interval lying strictly above the barrier, so both local wave numbers are real.

Transfer matrices act on the column state `(ψ, ∂ₓψ)` from left to right. With the cell starting at
the well, the one-cell matrix is therefore `M_barrier * M_well`. The discriminant is explicitly
normalized as one half of the one-cell trace. The Bloch phase itself is not redefined here:
`cellBlochPhase` delegates to `Crystal.blochPhase`, preserving the repository convention
`exp (i k · R)`.

The model is finite and convention-explicit. It does not introduce transport, Berry curvature,
Chern data, an infinite-crystal limit, or a thermodynamic limit.
-/

namespace LeanCondensedMatter.Crystal.KronigPenney

noncomputable section

/-- Physical and finite-domain parameters for one square-potential Kronig–Penney benchmark.

The energy zero is the well bottom, the barrier potential is `barrierHeight`, and `hbar` is the
reduced-Planck normalization entering the local wave number
`q = sqrt (2 m (E - V)) / hbar`. -/
structure Parameters where
  /-- Lattice period of one square-potential cell. -/
  period : ℝ
  /-- Width of the zero-potential well. -/
  wellWidth : ℝ
  /-- Width of the positive square barrier. -/
  barrierWidth : ℝ
  /-- Barrier potential measured from the well-bottom energy zero. -/
  barrierHeight : ℝ
  /-- Particle mass. -/
  particleMass : ℝ
  /-- Reduced Planck constant used in the wave-number normalization. -/
  hbar : ℝ
  /-- Lower endpoint of the finite energy domain. -/
  energyMin : ℝ
  /-- Upper endpoint of the finite energy domain. -/
  energyMax : ℝ

/-- Regular finite-parameter regime used by the explicit transfer-matrix formulas. -/
structure Parameters.IsRegular (params : Parameters) : Prop where
  period_pos : 0 < params.period
  wellWidth_pos : 0 < params.wellWidth
  barrierWidth_pos : 0 < params.barrierWidth
  widths_sum : params.wellWidth + params.barrierWidth = params.period
  barrierHeight_nonneg : 0 ≤ params.barrierHeight
  particleMass_pos : 0 < params.particleMass
  hbar_pos : 0 < params.hbar
  barrier_below_energyMin : params.barrierHeight < params.energyMin
  energyMin_lt_energyMax : params.energyMin < params.energyMax

/-- The well-bottom energy convention is exactly zero. -/
def wellPotential (_params : Parameters) : ℝ := 0

/-- The barrier potential in the well-bottom-zero convention. -/
def barrierPotential (params : Parameters) : ℝ := params.barrierHeight

/-- Membership in the finite energy interval carried by the benchmark. -/
def inEnergyDomain (params : Parameters) (energy : ℝ) : Prop :=
  energy ∈ Set.Icc params.energyMin params.energyMax

/-- First Brillouin-zone representative interval for the one-dimensional lattice period.

This is a coordinate representative of the existing Brillouin quotient, not a second quotient
construction. -/
def inBlochDomain (params : Parameters) (k : ℝ) : Prop :=
  k ∈ Set.Icc (-Real.pi / params.period) (Real.pi / params.period)

/-- Local real wave number in a constant-potential region. -/
def waveNumber (params : Parameters) (potential energy : ℝ) : ℝ :=
  Real.sqrt (2 * params.particleMass * (energy - potential)) / params.hbar

/-- Wave number in the zero-potential well. -/
def wellWaveNumber (params : Parameters) (energy : ℝ) : ℝ :=
  waveNumber params (wellPotential params) energy

/-- Wave number in the square barrier. -/
def barrierWaveNumber (params : Parameters) (energy : ℝ) : ℝ :=
  waveNumber params (barrierPotential params) energy

private theorem waveNumber_pos
    (params : Parameters) (potential energy : ℝ)
    (hmass : 0 < params.particleMass) (hhbar : 0 < params.hbar)
    (henergy : potential < energy) :
    0 < waveNumber params potential energy := by
  unfold waveNumber
  exact div_pos
    (Real.sqrt_pos.2
      (mul_pos (mul_pos (by norm_num) hmass) (sub_pos.mpr henergy)))
    hhbar

/-- The well wave number is nonzero throughout the regular finite energy domain. -/
theorem wellWaveNumber_ne_zero
    (params : Parameters) (hregular : params.IsRegular) {energy : ℝ}
    (henergy : inEnergyDomain params energy) :
    wellWaveNumber params energy ≠ 0 := by
  have hbarrier_lt_energy : params.barrierHeight < energy :=
    lt_of_lt_of_le hregular.barrier_below_energyMin henergy.1
  have hzero_lt_energy : 0 < energy :=
    lt_of_le_of_lt hregular.barrierHeight_nonneg hbarrier_lt_energy
  exact ne_of_gt
    (by
      simpa [wellWaveNumber, wellPotential] using
        waveNumber_pos params 0 energy hregular.particleMass_pos hregular.hbar_pos
          hzero_lt_energy)

/-- The barrier wave number is nonzero throughout the regular finite energy domain. -/
theorem barrierWaveNumber_ne_zero
    (params : Parameters) (hregular : params.IsRegular) {energy : ℝ}
    (henergy : inEnergyDomain params energy) :
    barrierWaveNumber params energy ≠ 0 := by
  have hbarrier_lt_energy : params.barrierHeight < energy :=
    lt_of_lt_of_le hregular.barrier_below_energyMin henergy.1
  exact ne_of_gt
    (by
      simpa [barrierWaveNumber, barrierPotential] using
        waveNumber_pos params params.barrierHeight energy hregular.particleMass_pos
          hregular.hbar_pos hbarrier_lt_energy)

/-- Transfer matrix through a constant-potential region of width `width` with nonzero real wave
number `q`, acting on `(ψ, ∂ₓψ)`. The totalized formula is defined for every `q`; determinant
statements below state the required nonzero hypothesis explicitly. -/
def regionTransfer (q width : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (q * width), Real.sin (q * width) / q;
    -(q * Real.sin (q * width)), Real.cos (q * width)]

/-- A constant-region transfer matrix is unimodular whenever its wave number is nonzero. -/
theorem regionTransfer_det (q width : ℝ) (hq : q ≠ 0) :
    (regionTransfer q width).det = 1 := by
  rw [Matrix.det_fin_two]
  simp [regionTransfer]
  field_simp [hq]
  nlinarith [Real.sin_sq_add_cos_sq (q * width)]

/-- Transfer through the well part of one cell. -/
def wellTransfer (params : Parameters) (energy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  regionTransfer (wellWaveNumber params energy) params.wellWidth

/-- Transfer through the barrier part of one cell. -/
def barrierTransfer (params : Parameters) (energy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  regionTransfer (barrierWaveNumber params energy) params.barrierWidth

/-- One-cell transfer matrix for the convention well first, barrier second. -/
def oneCellTransfer (params : Parameters) (energy : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  barrierTransfer params energy * wellTransfer params energy

/-- The one-cell transfer matrix is unimodular when both local wave numbers are nonzero. -/
theorem oneCellTransfer_det
    (params : Parameters) (energy : ℝ)
    (hwell : wellWaveNumber params energy ≠ 0)
    (hbarrier : barrierWaveNumber params energy ≠ 0) :
    (oneCellTransfer params energy).det = 1 := by
  rw [oneCellTransfer, Matrix.det_mul]
  rw [barrierTransfer, wellTransfer]
  rw [regionTransfer_det _ _ hbarrier, regionTransfer_det _ _ hwell]
  rfl

/-- In the regular finite energy domain, one-cell unimodularity follows from the parameter
assumptions. -/
theorem oneCellTransfer_det_of_mem
    (params : Parameters) (hregular : params.IsRegular) {energy : ℝ}
    (henergy : inEnergyDomain params energy) :
    (oneCellTransfer params energy).det = 1 :=
  oneCellTransfer_det params energy
    (wellWaveNumber_ne_zero params hregular henergy)
    (barrierWaveNumber_ne_zero params hregular henergy)

/-- Kronig–Penney discriminant with the normalization exposed explicitly as
`Δ(E) = tr M(E) / 2`. -/
def discriminant (params : Parameters) (energy : ℝ) : ℝ :=
  (oneCellTransfer params energy).trace / 2

/-- Bloch phase across one real-space period, using the canonical `Crystal.blochPhase`
normalization and orientation. -/
def cellBlochPhase (params : Parameters) (k : ℝ) : ℂ :=
  blochPhase k params.period

/-- Bloch condition for the fixed left-to-right transfer convention.

The first equality is the real discriminant form. The second pins it to the repository Bloch-phase
convention rather than introducing a model-local phase normalization. -/
def BlochCondition (params : Parameters) (energy k : ℝ) : Prop :=
  discriminant params energy = Real.cos (k * params.period) ∧
    (((2 * discriminant params energy : ℝ) : ℂ) =
      cellBlochPhase params k + (cellBlochPhase params k)⁻¹)

/-- An energy in the finite model lies in an allowed band exactly when the normalized
discriminant has absolute value at most one. -/
def AllowedBandEnergy (params : Parameters) (energy : ℝ) : Prop :=
  inEnergyDomain params energy ∧ |discriminant params energy| ≤ 1

/-- An energy in the finite model lies in a forbidden gap exactly when the normalized
discriminant has absolute value greater than one. -/
def ForbiddenGapEnergy (params : Parameters) (energy : ℝ) : Prop :=
  inEnergyDomain params energy ∧ 1 < |discriminant params energy|

/-- Every energy in the finite domain is classified by the explicit discriminant normalization as
allowed or forbidden. -/
theorem allowedBand_or_forbiddenGap
    (params : Parameters) {energy : ℝ} (henergy : inEnergyDomain params energy) :
    AllowedBandEnergy params energy ∨ ForbiddenGapEnergy params energy := by
  rcases le_or_gt |discriminant params energy| 1 with hallowed | hgap
  · exact Or.inl ⟨henergy, hallowed⟩
  · exact Or.inr ⟨henergy, hgap⟩

/-- Local data for a nondegenerate finite-model band edge.

The branch is required to stay inside the finite Bloch and energy domains, to satisfy the fixed
Bloch condition there, and to carry explicit first/second derivative data. The final
`implicitCurvatureIdentity` is the second-order implicit-dispersion relation at a stationary edge;
keeping it explicit avoids claiming an implicit-function theorem under hypotheses not represented
by this finite benchmark. -/
structure BandEdgeData (params : Parameters) where
  /-- Local band-energy branch as a function of the one-dimensional Bloch coordinate. -/
  branchEnergy : ℝ → ℝ
  /-- Bloch coordinate of the edge. -/
  blochCoordinate : ℝ
  /-- Energy at the edge. -/
  energy : ℝ
  /-- Second derivative of the band energy at the edge. -/
  curvature : ℝ
  /-- Energy derivative of the normalized discriminant at the edge. -/
  discriminantSlope : ℝ
  energy_eq : branchEnergy blochCoordinate = energy
  energy_mem : inEnergyDomain params energy
  bloch_mem : inBlochDomain params blochCoordinate
  branchEnergy_mem :
    ∀ k, inBlochDomain params k → inEnergyDomain params (branchEnergy k)
  bloch_relation :
    ∀ k, inBlochDomain params k → BlochCondition params (branchEnergy k) k
  stationary : HasDerivAt branchEnergy 0 blochCoordinate
  secondDerivative :
    HasDerivAt (fun k => deriv branchEnergy k) curvature blochCoordinate
  discriminantDerivative :
    HasDerivAt (discriminant params) discriminantSlope energy
  discriminantSlope_ne_zero : discriminantSlope ≠ 0
  curvature_ne_zero : curvature ≠ 0
  phaseCurvatureDenominator_ne_zero :
    params.period ^ 2 * Real.cos (blochCoordinate * params.period) ≠ 0
  implicitCurvatureIdentity :
    discriminantSlope * curvature =
      -(params.period ^ 2 * Real.cos (blochCoordinate * params.period))

/-- Band-edge curvature obtained from the finite Bloch discriminant relation. -/
theorem BandEdgeData.curvature_eq
    {params : Parameters} (edge : BandEdgeData params) :
    edge.curvature =
      -(params.period ^ 2 * Real.cos (edge.blochCoordinate * params.period)) /
        edge.discriminantSlope := by
  apply (eq_div_iff edge.discriminantSlope_ne_zero).2
  simpa [mul_comm] using edge.implicitCurvatureIdentity

/-- Effective mass defined from the nonzero band curvature in physical wave-vector coordinates. -/
def effectiveMass (params : Parameters) (edge : BandEdgeData params) : ℝ :=
  params.hbar ^ 2 / edge.curvature

/-- Finite-model effective-mass identity at a nondegenerate stationary band edge:
`m* = -ℏ² Δ'(E₀) / (a² cos(k₀ a))`.

All differentiability, stationary-point, and nonzero-denominator assumptions are carried explicitly
by `BandEdgeData`; no infinite-period or thermodynamic statement is used. -/
theorem BandEdgeData.effectiveMass_eq
    {params : Parameters} (edge : BandEdgeData params) :
    effectiveMass params edge =
      -(params.hbar ^ 2 * edge.discriminantSlope) /
        (params.period ^ 2 * Real.cos (edge.blochCoordinate * params.period)) := by
  rw [effectiveMass, edge.curvature_eq]
  field_simp [edge.discriminantSlope_ne_zero, edge.phaseCurvatureDenominator_ne_zero] <;> ring

end

end LeanCondensedMatter.Crystal.KronigPenney
