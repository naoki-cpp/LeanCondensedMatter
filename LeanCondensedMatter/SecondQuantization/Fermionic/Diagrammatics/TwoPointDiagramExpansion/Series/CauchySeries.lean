import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.FiberCauchySum
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Series.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSubsetMoment
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option linter.style.header false

/-!
# Cauchy convolution and power-series linked-cluster theorem

The canonical external-slot fiber decomposition first identifies each order-`n` two-point Dyson
coefficient with the Cauchy convolution of externally connected coefficients and normalized vacuum
coefficients. That physical factorization is then lifted to formal power series; generic
power-series division by the normalized partition function cancels the vacuum factor.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Effective-dispersion coefficientwise Cauchy identity.

At order `n`, the complete operator-defined two-point Dyson coefficient is the Cauchy convolution of
the connected two-point coefficients with the normalized vacuum partition coefficients. -/
private theorem twoPointDysonCoefficient_zero_mu_cauchy
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    twoPointDysonCoefficient (n := n) ε β 0 g i j τ τ' =
      ∑ m ∈ Finset.range (n + 1),
        connectedTwoPointDysonCoefficient ε β 0 g i j τ τ' m *
          PowerSeries.coeff (n - m) (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) := by
  rw [← twoPointDiagramCoefficient_eq_twoPointDysonCoefficient]
  classical
  have slice : ∀ {n m k : ℕ}, m + k = n →
      (∑ T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)),
        ∑ p : {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
                ext.1.IsExternallyConnected} ×
              QuarticWickDiagram Mode n
                ((Finset.univ : Finset (Fin n)) \ T),
          ((fixedExternalFiberEquiv T).symm p).1.dysonAmplitude ε β g τ τ') =
        connectedTwoPointDysonCoefficient ε β 0 g i j τ τ' m *
          PowerSeries.coeff k (PowerSeries.normalizeByConstantCoeff (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g))) := by
    intro n m k hmk
    subst n
    rw [Finset.sum_subtype
      (p := fun T : Finset (Fin (m + k)) => T.card = m)
      (Finset.powersetCard m (Finset.univ : Finset (Fin (m + k))))
      (fun T => by simp)
      (fun T =>
        ∑ p : {ext : FixedExternalTwoPointWickDiagramOn Mode (m + k) T i j //
                ext.1.IsExternallyConnected} ×
              QuarticWickDiagram Mode (m + k)
                ((Finset.univ : Finset (Fin (m + k))) \ T),
          ((fixedExternalFiberEquiv T).symm p).1.dysonAmplitude ε β g τ τ')]
    exact fixedExternalFiberSum_eq_cauchyFactor
      ε β hβ g i j τ τ' m k
  rw [twoPointDiagramCoefficient_eq_sum_dysonAmplitude]
  rw [sum_eq_sum_powerset_fixedExternalFiber
    (Mode := Mode) (i := i) (j := j)
    (F := fun d => d.dysonAmplitude ε β g τ τ')]
  rw [Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro m hm
  have hmn : m ≤ n := by
    simpa [Nat.lt_succ_iff] using hm
  exact slice (Nat.add_sub_of_le hmn)

/-- **Coefficientwise linked-cluster Cauchy identity at arbitrary chemical potential.**
The vacuum series uses the effective grand-canonical dispersion, while the
connected coefficients restore physical-H evolution of the external fields. -/
theorem twoPointDysonCoefficient_eq_sum_connectedTwoPointDysonCoefficient_mul_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    twoPointDysonCoefficient (n := n) ε β μ g i j τ τ' =
      ∑ m ∈ Finset.range (n + 1),
        connectedTwoPointDysonCoefficient ε β μ g i j τ τ' m *
          PowerSeries.coeff (n - m)
            (PowerSeries.normalizeByConstantCoeff
              (Common.dysonTraceSeries (fermionEnergy (fun k => ε k - μ))
                β (quarticInteraction g))) := by
  rw [twoPointDysonCoefficient_eq_shiftedDispersion ε β μ,
    twoPointDysonCoefficient_zero_mu_cauchy (fun k => ε k - μ) β hβ,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hconn :
      connectedTwoPointDysonCoefficient ε β μ g i j τ τ' m =
        twoPointChemicalPotentialFactor μ τ τ' *
          connectedTwoPointDysonCoefficient (fun k => ε k - μ) β 0 g i j τ τ' m := by
    unfold connectedTwoPointDysonCoefficient
    simp only [twoPointChemicalPotentialFactor, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, one_mul, sub_zero]
  rw [hconn, mul_assoc]

/-- The full two-point Dyson series factors into its externally connected series and the normalized
zero-external-leg Dyson partition series. -/
theorem twoPointDysonSeries_eq_connectedTwoPointDysonSeries_mul_normalizedDysonPartitionSeries
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    twoPointDysonSeries ε β μ g i j τ τ' =
      connectedTwoPointDysonSeries ε β μ g i j τ τ' *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy (fun k => ε k - μ)) β (quarticInteraction g)) := by
  ext n
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [twoPointDysonSeries, connectedTwoPointDysonSeries, PowerSeries.coeff_mk]
  exact twoPointDysonCoefficient_eq_sum_connectedTwoPointDysonCoefficient_mul_normalizedDysonPartitionCoeff
    ε β μ hβ g i j τ τ' n

/-- **Finite-mode fermionic two-point linked-cluster theorem.** For the imaginary-time Dyson series
built from free Gibbs expectations and a quartic interaction, with the repository's canonical
time-order/equal-time convention, partition-function normalization leaves exactly the sum of externally
connected two-point diagrams. -/
theorem partitionFunctionNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    partitionFunctionNormalizedTwoPointDysonSeries ε β μ g i j τ τ' =
      connectedTwoPointDysonSeries ε β μ g i j τ τ' := by
  rw [partitionFunctionNormalizedTwoPointDysonSeries]
  apply PowerSeries.mul_inv_eq_of_eq_mul_of_constantCoeff_ne_zero
  · rw [PowerSeries.constantCoeff_normalizeByConstantCoeff
      (Common.constantCoeff_dysonTraceSeries_ne_zero (fermionEnergy (fun k => ε k - μ)) β (quarticInteraction g))]
    exact one_ne_zero
  · exact twoPointDysonSeries_eq_connectedTwoPointDysonSeries_mul_normalizedDysonPartitionSeries
      ε β μ hβ g i j τ τ'


/-! ## Compatibility with arbitrary external insertions -/

open Common in
/-- The physical unnormalized two-point operator series is the two-external
specialization of the arbitrary-external vertex series, at every real β and μ. -/
theorem twoPointDysonSeries_eq_externalInsertionVertexDysonSeries
    (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    twoPointDysonSeries ε β μ g i j τ τ' =
      externalInsertionVertexDysonSeries (E := 1) ε β μ g
        (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') := by
  ext n
  simp only [twoPointDysonSeries, externalInsertionVertexDysonSeries, PowerSeries.coeff_mk]
  exact twoPointDysonCoefficient_eq_externalInsertionVertexDysonCoefficient
    ε β μ g i j τ τ'

open Common in
/-- Both constructions cancel the same normalized grand-canonical vacuum
series. The remaining physical external-field factor multiplies the actual
vacuum-free diagram sum at effective dispersion. -/
theorem partitionFunctionNormalizedTwoPointDysonSeries_eq_shiftedVacuumFree
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    partitionFunctionNormalizedTwoPointDysonSeries ε β μ g i j τ τ' =
      PowerSeries.C (twoPointChemicalPotentialFactor μ τ τ') *
        vacuumFreeExternalInsertionDysonSeries (E := 1) (fun k => ε k - μ) β g
          (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') := by
  rw [partitionFunctionNormalizedTwoPointDysonSeries,
    twoPointDysonSeries_eq_externalInsertionVertexDysonSeries]
  apply PowerSeries.mul_inv_eq_of_eq_mul_of_constantCoeff_ne_zero
  · rw [PowerSeries.constantCoeff_normalizeByConstantCoeff
      (Common.constantCoeff_dysonTraceSeries_ne_zero
        (fermionEnergy (fun k => ε k - μ)) β (quarticInteraction g))]
    exact one_ne_zero
  · rw [externalInsertionVertexDysonSeries_eq_shiftedVacuumFree_mul_normalizedDysonPartitionSeries
      ε β μ hβ, externalFieldFamilyChemicalPotentialFactor_twoPoint]

open Common in
/-- The two independent physical connected diagram sums agree for two external
fields. This follows by comparing their already-established vacuum
normalizations; connectivity is not replaced by an operator definition. -/
theorem connectedTwoPointDysonSeries_eq_shiftedConnectedExternalInsertion
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    connectedTwoPointDysonSeries ε β μ g i j τ τ' =
      PowerSeries.C (twoPointChemicalPotentialFactor μ τ τ') *
        connectedExternalInsertionDysonSeries (K := 1) (fun k => ε k - μ) β g
          (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') := by
  rw [← partitionFunctionNormalizedTwoPointDysonSeries_eq_connectedTwoPointDysonSeries
    ε β μ hβ,
    partitionFunctionNormalizedTwoPointDysonSeries_eq_shiftedVacuumFree ε β μ hβ,
    vacuumFreeExternalInsertionDysonSeries_eq_connected_two]

open Common in
/-- The resulting integrated connected coefficient identity is coefficientwise
and retains the physical chemical-potential factor. -/
theorem connectedTwoPointDysonCoefficient_eq_shiftedConnectedExternalInsertion
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    connectedTwoPointDysonCoefficient ε β μ g i j τ τ' n =
      twoPointChemicalPotentialFactor μ τ τ' *
        connectedExternalInsertionDysonCoefficient (K := 1) (fun k => ε k - μ) β g
          (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') n := by
  simpa only [connectedTwoPointDysonSeries, connectedExternalInsertionDysonSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_C_mul] using
      congrArg (PowerSeries.coeff n)
        (connectedTwoPointDysonSeries_eq_shiftedConnectedExternalInsertion ε β μ hβ g i j τ τ')


open Common in
/-- The physical two-point connected series is the grand-canonical source
cumulant evaluated on the full two-element external sector. -/
theorem connectedTwoPointDysonSeries_eq_grandCanonicalSourceCumulant
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    connectedTwoPointDysonSeries ε β μ g i j τ τ' =
      externalSubsetSourceCumulantSeries (E := 1)
        (grandCanonicalExternalSubsetMomentSeries (E := 1) ε β μ g
          (twoPointExternalLabels i j) (twoPointExternalTimes τ τ'))
        Finset.univ := by
  classical
  rw [grandCanonicalExternalSubsetSourceCumulantSeries_eq_connectedDiagramSeries_two,
    connectedTwoPointDysonSeries_eq_shiftedConnectedExternalInsertion ε β μ hβ]
  let S : Finset (Fin 2) := Finset.univ
  have hS : S ≠ ∅ := by simp [S]
  have heven : Even S.card := by simp [S]
  let e := evenExternalSubsetOrderIso (E := 1) S heven
  have hidx (p : Fin 2) : (e p).1 = p := by
    have h (v : S) : (e.symm v).val = v.1.val := by
      change ((S.orderIsoOfFin _).symm v).val = v.1.val
      rw [Finset.orderIsoOfFin_symm_apply]
      simp [S, Fin.sort_univ, List.idxOf_finRange]
    apply Fin.ext
    simpa only [OrderIso.symm_apply_apply] using (h (e p)).symm
  have hlabels : evenExternalSubsetLabels (E := 1) (twoPointExternalLabels i j) S heven =
      twoPointExternalLabels i j := by
    funext p
    exact congrArg (twoPointExternalLabels i j) (hidx p)
  have htimes : evenExternalSubsetTimes (E := 1) (twoPointExternalTimes τ τ') S heven =
      twoPointExternalTimes τ τ' := by
    funext p
    exact congrArg (twoPointExternalTimes τ τ') (hidx p)
  unfold grandCanonicalExternalSubsetConnectedDiagramSeries
  change _ = (∏ p : Fin 2, PowerSeries.C
    (externalFieldChemicalPotentialFactor μ (twoPointExternalTimes τ τ' p)
      (twoPointExternalLabels i j p))) *
      externalSubsetConnectedDiagramSeries (E := 1) (fun k => ε k - μ) β g
        (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') S
  rw [← map_prod, ← externalFieldFamilyChemicalPotentialFactor,
    externalFieldFamilyChemicalPotentialFactor_twoPoint]
  simp only [externalSubsetConnectedDiagramSeries, hS, heven, dite_eq_left,
    hlabels, htimes]

end Fermionic
end SecondQuantization
