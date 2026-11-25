import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Integration.FiberCauchySum
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.Series.DysonSeries
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalSubsetMoment
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option linter.style.header false

/-!
# Cauchy convolution and power-series linked-cluster theorem

The fixed-leg equivalence transports the actual connected two-point diagrams to the general
external-insertion sector. The general physical vacuum factorization then gives the two-point
series and coefficientwise Cauchy identities without a second fiber decomposition.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

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
/-- At every real β, the actual connected two-point sum is the E=1
connected external-insertion sum with the physical external-field factor.
The proof transports each diagram, rather than cancelling a vacuum series. -/
theorem connectedTwoPointDysonCoefficient_eq_shiftedConnectedExternalInsertion
    (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    connectedTwoPointDysonCoefficient ε β μ g i j τ τ' n =
      twoPointChemicalPotentialFactor μ τ τ' *
        connectedExternalInsertionDysonCoefficient (K := 1) (fun k => ε k - μ) β g
          (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') n := by
  classical
  let S : Finset (Fin n) := Finset.univ
  let e : FixedExternalTwoPointWickDiagram Mode n i j ≃
      FixedExternalInsertionWickDiagram Mode 1 n (twoPointExternalLabels i j) :=
    (twoPointDiagramExternalInsertionEquiv S).subtypeEquiv (fun d => Iff.rfl)
  let f : {d : FixedExternalTwoPointWickDiagram Mode n i j // d.1.IsExternallyConnected} ≃
      VacuumFreeFixedExternalInsertionWickDiagram Mode 1 n (twoPointExternalLabels i j) :=
    e.subtypeEquiv (fun d => by
      rw [TwoPointDiagram.isExternallyConnected_iff_hasNoVacuumComponent]
      exact (hasNoVacuumComponent_congr_iff
        d.1.externalInsertionGraphIso (Equiv.refl (Fin 2)) (Equiv.refl ↥S)
        (fun _ => rfl) (fun _ => rfl)).symm)
  rw [← vacuumFreeExternalInsertionDysonCoefficient_eq_connected_two]
  unfold connectedTwoPointDysonCoefficient vacuumFreeExternalInsertionDysonCoefficient
  apply congrArg (fun z : ℂ => twoPointChemicalPotentialFactor μ τ τ' * z)
  rw [Finset.sum_subtype
    (p := fun d : FixedExternalTwoPointWickDiagram Mode n i j => d.1.IsExternallyConnected)
    _ (fun _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and])
    (fun d => d.dysonAmplitude (fun k => ε k - μ) β g τ τ')]
  calc
    _ = ∑ d : {d : FixedExternalTwoPointWickDiagram Mode n i j //
          d.1.IsExternallyConnected},
        (f d).1.1.dysonAmplitude (fun k => ε k - μ) β g (twoPointExternalTimes τ τ') := by
      apply Finset.sum_congr rfl
      intro d _
      exact d.1.dysonAmplitude_eq_externalInsertion (fun k => ε k - μ) β g τ τ'
    _ = _ := Equiv.sum_comp f _

open Common in
/-- Connected-series specialization, obtained coefficientwise from diagram transport,
with no restriction on β. -/
theorem connectedTwoPointDysonSeries_eq_shiftedConnectedExternalInsertion
    (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    connectedTwoPointDysonSeries ε β μ g i j τ τ' =
      PowerSeries.C (twoPointChemicalPotentialFactor μ τ τ') *
        connectedExternalInsertionDysonSeries (K := 1) (fun k => ε k - μ) β g
          (twoPointExternalLabels i j) (twoPointExternalTimes τ τ') := by
  ext n
  simp only [connectedTwoPointDysonSeries, connectedExternalInsertionDysonSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_C_mul]
  exact connectedTwoPointDysonCoefficient_eq_shiftedConnectedExternalInsertion ε β μ g i j τ τ' n

open Common in
/-- The full two-point Dyson series factors into its externally connected series and the normalized
zero-external-leg Dyson partition series. -/
theorem twoPointDysonSeries_eq_connectedTwoPointDysonSeries_mul_normalizedDysonPartitionSeries
    (ε : Mode → ℝ) (β μ : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    twoPointDysonSeries ε β μ g i j τ τ' =
      connectedTwoPointDysonSeries ε β μ g i j τ τ' *
        PowerSeries.normalizeByConstantCoeff
          (Common.dysonTraceSeries (fermionEnergy (fun k => ε k - μ)) β (quarticInteraction g)) := by
  rw [twoPointDysonSeries_eq_externalInsertionVertexDysonSeries,
    externalInsertionVertexDysonSeries_eq_shiftedVacuumFree_mul_normalizedDysonPartitionSeries
      ε β μ hβ, externalFieldFamilyChemicalPotentialFactor_twoPoint,
    vacuumFreeExternalInsertionDysonSeries_eq_connected_two,
    ← connectedTwoPointDysonSeries_eq_shiftedConnectedExternalInsertion]

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
  have h := congrArg (PowerSeries.coeff n)
    (twoPointDysonSeries_eq_connectedTwoPointDysonSeries_mul_normalizedDysonPartitionSeries
      ε β μ hβ g i j τ τ')
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [twoPointDysonSeries, connectedTwoPointDysonSeries, PowerSeries.coeff_mk] using h

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

open Common in
/-- The physical two-point connected series is the grand-canonical source
cumulant evaluated on the full two-element external sector. -/
theorem connectedTwoPointDysonSeries_eq_grandCanonicalSourceCumulant
    (ε : Mode → ℝ) (β μ : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) :
    connectedTwoPointDysonSeries ε β μ g i j τ τ' =
      externalSubsetSourceCumulantSeries (E := 1)
        (grandCanonicalExternalSubsetMomentSeries (E := 1) ε β μ g
          (twoPointExternalLabels i j) (twoPointExternalTimes τ τ'))
        Finset.univ := by
  rw [grandCanonicalExternalSubsetSourceCumulantSeries_eq_connectedDiagramSeries_two,
    connectedTwoPointDysonSeries_eq_shiftedConnectedExternalInsertion ε β μ,
    grandCanonicalExternalSubsetConnectedDiagramSeries_univ (by decide : 0 < 1),
    externalFieldFamilyChemicalPotentialFactor_twoPoint]

end Fermionic
end SecondQuantization
