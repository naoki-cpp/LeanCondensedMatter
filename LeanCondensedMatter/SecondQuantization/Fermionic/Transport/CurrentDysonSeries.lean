import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CurrentInsertions
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.InteractionPictureVertexDyson

set_option linter.style.header false

/-!
# Composite-current connected Dyson series

Two bilinear fermionic currents each contain two elementary fermion fields. The current
kernels weight the existing arbitrary-external-insertion Dyson series at two and four
external legs. Partition-function normalization removes vacuum-only diagram components.

The connected *two-current* series subtracts the product of the two normalized one-current
series. It is not the four-elementary-field cumulant: a diagram need not connect all four
individual fermion legs to contribute to a connected composite-current correlation.

The operator-level bilinear-current and four-field identity, independent of the ensemble,
is owned by `CurrentInsertions`. The diagram amplitudes here use the existing free Gibbs
realization; no general claim about a fixed-particle-number state or analytic convergence
is made.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open Common
open scoped BigOperators

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The two elementary field labels in the ordered bilinear `cᵢ† cⱼ`. -/
def currentExternalLabels (i j : Mode) : Fin (2 * 1) → ExternalFieldLabel Mode :=
  fun e => if e.val = 0 then .creation i else .annihilation j

/-- Four elementary field labels for the ordered product of two bilinear currents. -/
def currentPairExternalLabels (i j k l : Mode) :
    Fin (2 * 2) → ExternalFieldLabel Mode :=
  fun e =>
    if e.val = 0 then .creation i
    else if e.val = 1 then .annihilation j
    else if e.val = 2 then .creation k
    else .annihilation l

/-- The first current carries time `τ` and the second time `τ'`. -/
def currentPairExternalTimes (τ τ' : ℝ) : Fin (2 * 2) → ℝ :=
  fun e => if e.val < 2 then τ else τ'

/-- The interaction-picture Dyson series of one bilinear current, expanded into two
elementary external fields and weighted by its one-body kernel. -/
noncomputable def currentInsertionDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ : ℝ) (j : Mode → Mode → ℂ) : PowerSeries ℂ :=
  ∑ i : Mode, ∑ k : Mode, j i k •
    externalInsertionVertexDysonSeries ε β g
      (currentExternalLabels i k) (fun _ => τ)

/-- The Dyson series of two ordered bilinear-current insertions (four external fields). -/
noncomputable def currentPairDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ) : PowerSeries ℂ :=
  ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
    (jx i j * jy k l) •
      externalInsertionVertexDysonSeries ε β g
        (currentPairExternalLabels i j k l) (currentPairExternalTimes τ τ')

/-- One current's Dyson series after removing pure-vacuum components. -/
noncomputable def vacuumFreeCurrentInsertionDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ : ℝ) (j : Mode → Mode → ℂ) : PowerSeries ℂ :=
  ∑ i : Mode, ∑ k : Mode, j i k •
    vacuumFreeExternalInsertionDysonSeries ε β g
      (currentExternalLabels i k) (fun _ => τ)

/-- The four-field current-pair Dyson series with pure-vacuum components removed. -/
noncomputable def vacuumFreeCurrentPairDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ) : PowerSeries ℂ :=
  ∑ i : Mode, ∑ j : Mode, ∑ k : Mode, ∑ l : Mode,
    (jx i j * jy k l) •
      vacuumFreeExternalInsertionDysonSeries ε β g
        (currentPairExternalLabels i j k l) (currentPairExternalTimes τ τ')

/-- Summing over a current kernel commutes with the existing vacuum-factor decomposition. -/
theorem currentInsertionDysonSeries_eq_vacuumFree_mul_partition
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (τ : ℝ) (j : Mode → Mode → ℂ) :
    currentInsertionDysonSeries ε β g τ j =
      vacuumFreeCurrentInsertionDysonSeries ε β g τ j *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)) := by
  unfold currentInsertionDysonSeries vacuumFreeCurrentInsertionDysonSeries
  simp_rw [externalInsertionVertexDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
    ε β hβ g]
  simp only [← smul_mul_assoc, ← Finset.sum_mul]

/-- The same vacuum-factor decomposition for two composite current insertions. -/
theorem currentPairDysonSeries_eq_vacuumFree_mul_partition
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ) :
    currentPairDysonSeries ε β g τ τ' jx jy =
      vacuumFreeCurrentPairDysonSeries ε β g τ τ' jx jy *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)) := by
  unfold currentPairDysonSeries vacuumFreeCurrentPairDysonSeries
  simp_rw [externalInsertionVertexDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
    ε β hβ g]
  simp only [← smul_mul_assoc, ← Finset.sum_mul]

/-- Dividing a one-current Dyson series by its free-normalized partition series
discards precisely the vacuum-only components. -/
theorem currentInsertionDysonSeries_mul_partition_inv
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (τ : ℝ) (j : Mode → Mode → ℂ) :
    currentInsertionDysonSeries ε β g τ j *
        (PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)))⁻¹ =
      vacuumFreeCurrentInsertionDysonSeries ε β g τ j := by
  apply PowerSeries.mul_inv_eq_of_eq_mul_of_constantCoeff_ne_zero
  · rw [PowerSeries.constantCoeff_normalizeByConstantCoeff
      (Common.constantCoeff_dysonTraceSeries_ne_zero
        (fermionEnergy ε) β (quarticInteraction g))]
    exact one_ne_zero
  · exact currentInsertionDysonSeries_eq_vacuumFree_mul_partition ε β hβ g τ j

/-- Vacuum normalization of the full current-pair Dyson series. -/
theorem currentPairDysonSeries_mul_partition_inv
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ) :
    currentPairDysonSeries ε β g τ τ' jx jy *
        (PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)))⁻¹ =
      vacuumFreeCurrentPairDysonSeries ε β g τ τ' jx jy := by
  apply PowerSeries.mul_inv_eq_of_eq_mul_of_constantCoeff_ne_zero
  · rw [PowerSeries.constantCoeff_normalizeByConstantCoeff
      (Common.constantCoeff_dysonTraceSeries_ne_zero
        (fermionEnergy ε) β (quarticInteraction g))]
    exact one_ne_zero
  · exact currentPairDysonSeries_eq_vacuumFree_mul_partition ε β hβ g τ τ' jx jy

/-- Formal connected correlation of the two *composite current insertions*.
Each expectation is normalized separately before the disconnected product is subtracted.
The multiplication of one-current series is the required convolution over Dyson orders. -/
noncomputable def connectedCurrentDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ) : PowerSeries ℂ :=
  let Z := PowerSeries.normalizeByConstantCoeff
    (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))
  (currentPairDysonSeries ε β g τ τ' jx jy * Z⁻¹) -
    (currentInsertionDysonSeries ε β g τ jx * Z⁻¹) *
      (currentInsertionDysonSeries ε β g τ' jy * Z⁻¹)

/-- The formal connected two-current series is the vacuum-free four-field series minus
the product of the vacuum-free two-field series for each current. This removes disconnected
*current* insertions without incorrectly imposing full four-fermion connectedness. -/
theorem connectedCurrentDysonSeries_eq_vacuumFree_sub
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ) :
    connectedCurrentDysonSeries ε β g τ τ' jx jy =
      vacuumFreeCurrentPairDysonSeries ε β g τ τ' jx jy -
        vacuumFreeCurrentInsertionDysonSeries ε β g τ jx *
          vacuumFreeCurrentInsertionDysonSeries ε β g τ' jy := by
  dsimp only [connectedCurrentDysonSeries]
  rw [currentPairDysonSeries_mul_partition_inv ε β hβ g τ τ' jx jy,
    currentInsertionDysonSeries_mul_partition_inv ε β hβ g τ jx,
    currentInsertionDysonSeries_mul_partition_inv ε β hβ g τ' jy]


/-- At each perturbative order the disconnected-current subtraction is a Cauchy
convolution, not the product of two coefficients at the same order. -/
theorem coeff_connectedCurrentDysonSeries_eq_vacuumFree_sub_cauchy
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (jx jy : Mode → Mode → ℂ) (n : ℕ) :
    PowerSeries.coeff n (connectedCurrentDysonSeries ε β g τ τ' jx jy) =
      PowerSeries.coeff n (vacuumFreeCurrentPairDysonSeries ε β g τ τ' jx jy) -
        ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
          PowerSeries.coeff p.1 (vacuumFreeCurrentInsertionDysonSeries ε β g τ jx) *
            PowerSeries.coeff p.2 (vacuumFreeCurrentInsertionDysonSeries ε β g τ' jy) := by
  rw [connectedCurrentDysonSeries_eq_vacuumFree_sub ε β hβ g τ τ' jx jy]
  simp only [map_sub, PowerSeries.coeff_mul]

end Transport
end Fermionic
end SecondQuantization
