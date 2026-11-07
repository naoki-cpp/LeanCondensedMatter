import LeanCondensedMatter.Models.MassiveDirac.Disorder.FiniteBroadeningBornRadialScalarGenerator
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false

/-!
# Finite momentum-grid realization of the regulated massive-Dirac radial Green generator

For a fixed momentum cutoff `pMax`, the midpoint rule below replaces only the
radial integral by a finite sum. Its denominator is the **existing** finite-cutoff
Born-Dyson denominator, evaluated with self-energy cutoff `pMax`; thus neither
the propagator nor its causal broadening and disorder parameters are replaced.

The Fourier kernel retains `p * radius / hbar`, the radial Jacobian `p`,
and exactly one physical measure factor `momentumMeasurePrefactor hbar`.
The separate executable Python reference grid can approximate both the Born
self-energy integral and this Fourier sum numerically. These finite-grid
definitions do not assert convergence or identify a continuum Hall limit.
-/

namespace QuantumTheory.Models.MassiveDirac

noncomputable section

open QuantumTheory.Transport

/-- Midpoint of cell `index` in the `count`-cell partition of `[0, pMax]`.
For zero cells the grid is empty; no evaluation of a point is required. -/
def finiteCutoffBornRadialMidpoint (pMax : ℝ) (count index : ℕ) : ℝ :=
  (pMax / (count : ℝ)) * ((index : ℝ) + 1 / 2)

/-- Every sampled midpoint lies strictly inside a positive cutoff interval. -/
theorem finiteCutoffBornRadialMidpoint_mem_Ioo
    (pMax : ℝ) (count index : ℕ) (hpMax : 0 < pMax)
    (hindex : index < count) :
    0 < finiteCutoffBornRadialMidpoint pMax count index ∧
      finiteCutoffBornRadialMidpoint pMax count index < pMax := by
  have hcountNat : 0 < count := Nat.zero_lt_of_lt hindex
  have hcount : (0 : ℝ) < (count : ℝ) := by exact_mod_cast hcountNat
  have hindexReal : (index : ℝ) + 1 / 2 < (count : ℝ) := by
    have hsucc : index + 1 ≤ count := Nat.succ_le_of_lt hindex
    have hsuccReal : (index : ℝ) + 1 ≤ (count : ℝ) := by
      exact_mod_cast hsucc
    linarith
  have hstep : 0 < pMax / (count : ℝ) := div_pos hpMax hcount
  have hwidth : (pMax / (count : ℝ)) * (count : ℝ) = pMax := by
    field_simp [ne_of_gt hcount]
  constructor
  · unfold finiteCutoffBornRadialMidpoint
    exact mul_pos hstep (by positivity)
  · unfold finiteCutoffBornRadialMidpoint
    calc
      (pMax / (count : ℝ)) * ((index : ℝ) + 1 / 2) <
          (pMax / (count : ℝ)) * (count : ℝ) :=
        mul_lt_mul_of_pos_left hindexReal hstep
      _ = pMax := hwidth

/-- The *same* physical scalar Green integrand used in the interval integral:
the complex Born-Dyson denominator uses its own fixed `pMax` cutoff. -/
def finiteCutoffBornDysonRadialScalarGridKernel
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) : ℂ :=
  (p : ℂ) *
    (finiteCutoffContinuumBornDysonDenominator
      side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
    polarFourierZerothAngularKernel (p * radius / hbar)

/-- Exactly the regulated scalar Green-generator integrand, before integration. -/
theorem finiteCutoffBornDysonRadialScalarGridKernel_eq
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius p : ℝ) :
    finiteCutoffBornDysonRadialScalarGridKernel
      side v m probeEnergy broadening disorderStrength hbar pMax radius p =
      (p : ℂ) *
        (finiteCutoffContinuumBornDysonDenominator
          side v m p 0 probeEnergy broadening disorderStrength hbar pMax)⁻¹ *
        polarFourierZerothAngularKernel (p * radius / hbar) := rfl

/-- A finite `count`-point quadrature for the actual cutoff-regulated radial
scalar Green generator, including the physical `d²p/(2πℏ)²` normalization.
The Born cutoff, radial upper bound, and grid endpoints are all `pMax`. -/
def finiteCutoffBornDysonRadialScalarMidpointGrid
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ)
    (count : ℕ) : ℂ :=
  ((momentumMeasurePrefactor hbar : ℝ) : ℂ) *
    ((pMax / (count : ℝ) : ℝ) : ℂ) *
      (Finset.range count).sum (fun index =>
        finiteCutoffBornDysonRadialScalarGridKernel
          side v m probeEnergy broadening disorderStrength hbar pMax radius
          (finiteCutoffBornRadialMidpoint pMax count index))

/-- No sample points means that the numerical finite-grid value is zero. -/
@[simp] theorem finiteCutoffBornDysonRadialScalarMidpointGrid_zero_count
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar pMax radius : ℝ) :
    finiteCutoffBornDysonRadialScalarMidpointGrid
      side v m probeEnergy broadening disorderStrength hbar pMax radius 0 = 0 := by
  simp [finiteCutoffBornDysonRadialScalarMidpointGrid]

/-- The zero-width cutoff is zero at any grid resolution, regardless of
the value of the complex spectral denominator at the endpoint. -/
@[simp] theorem finiteCutoffBornDysonRadialScalarMidpointGrid_zero_cutoff
    (side : SpectralSide)
    (v m probeEnergy broadening disorderStrength hbar radius : ℝ)
    (count : ℕ) :
    finiteCutoffBornDysonRadialScalarMidpointGrid
      side v m probeEnergy broadening disorderStrength hbar 0 radius count = 0 := by
  simp [finiteCutoffBornDysonRadialScalarMidpointGrid]

end

end QuantumTheory.Models.MassiveDirac
