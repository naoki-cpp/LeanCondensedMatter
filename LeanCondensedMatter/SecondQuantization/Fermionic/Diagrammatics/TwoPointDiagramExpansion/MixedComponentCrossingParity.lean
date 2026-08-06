import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentCrossing
import LeanCondensedMatter.Combinatorics.PerfectPairing.PairEndpoints
import LeanCondensedMatter.Combinatorics.PerfectPairing.CrossingParity

set_option linter.style.header false

/-!
# Endpoint-inversion parity for mixed-time two-point components

The geometric crossing count introduced in `MixedComponentCrossing.lean` is still phrased as a sum
over pairs.  This module converts each crossing indicator to the parity of the four endpoint
comparisons and then reindexes all pair endpoints as the complete mixed-position fibers of the two
components.

Consequently the remaining off-diagonal sign problem is reduced to one purely ordered-set statement:
the number of mixed positions of component `C` lying before positions of a distinct component `B`
is even.  The next event-block layer proves that statement from the one-leg external blocks and the
four-leg interaction blocks.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*}

/-- Mixed normalized pairs assigned to distinct full components are distinct. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPair_ne
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (p : d.MixedComponentPair τ τ' σ B)
    (q : d.MixedComponentPair τ τ' σ C) :
    p.1 ≠ q.1 := by
  intro hpq
  apply hBC
  calc
    B = d.mixedPairComponent τ τ' σ p.1 := p.2.symm
    _ = d.mixedPairComponent τ τ' σ q.1 := congrArg _ hpq
    _ = C := q.2

/-- Mixed pairs from distinct components have disjoint endpoints. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPair_endpoints_ne
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (p : d.MixedComponentPair τ τ' σ B)
    (q : d.MixedComponentPair τ τ' σ C) :
    p.1.1.1 ≠ q.1.1.1 ∧
      p.1.1.1 ≠ q.1.1.2 ∧
      p.1.1.2 ≠ q.1.1.1 ∧
      p.1.1.2 ≠ q.1.1.2 :=
  (d.pairingInMixedOrder τ τ' σ).normalizedPair_endpoints_ne_of_ne
    p.1 q.1 (d.mixedComponentPair_ne τ τ' σ B C hBC p q)

/-- The four-endpoint inversion count of two mixed pairs from distinct components has the same
parity as their unoriented geometric crossing indicator. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointInversionCount_mod_two_eq_indicator
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (p : d.MixedComponentPair τ τ' σ B)
    (q : d.MixedComponentPair τ τ' σ C) :
    pairEndpointInversionCount p.1.1 q.1.1 % 2 =
      if Crosses p.1.1 q.1.1 ∨ Crosses q.1.1 p.1.1 then 1 else 0 := by
  have hEnds := d.mixedComponentPair_endpoints_ne τ τ' σ B C hBC p q
  exact pairEndpointInversionCount_mod_two_eq_crossesIndicator
    p.1.1 q.1.1
    ((d.pairingInMixedOrder τ τ' σ).pairs_normalized p.1.2)
    ((d.pairingInMixedOrder τ τ' σ).pairs_normalized q.1.2)
    hEnds.1 hEnds.2.1 hEnds.2.2.1 hEnds.2.2.2

/-- Sum of the four-endpoint inversion counts over mixed pairs in two fixed components. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointInversionSum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) : ℕ :=
  ∑ x : d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C,
    pairEndpointInversionCount x.1.1.1 x.2.1.1

/-- Geometric crossings and pair-endpoint inversions agree modulo two for distinct components. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_pairEndpointInversionSum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 =
      d.mixedComponentPairEndpointInversionSum τ τ' σ B C % 2 := by
  symm
  exact fintype_sum_mod_two_congr _ _ fun x => by
    have h := d.mixedComponentPairEndpointInversionCount_mod_two_eq_indicator
      τ τ' σ B C hBC x.1 x.2
    split_ifs at h ⊢ <;> simpa using h

/-- Number of positions of component `C` occurring before positions of component `B` in the actual
mixed atomic order. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) : ℕ :=
  ∑ p : d.MixedComponentPosition τ τ' σ B,
    ∑ q : d.MixedComponentPosition τ τ' σ C,
      if q.1 < p.1 then 1 else 0

/-- Selecting an endpoint of a mixed component pair through the endpoint equivalence recovers that
endpoint in the ambient mixed order. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointEquiv_val
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B : d.1.componentPartition.parts)
    (p : d.MixedComponentPair τ τ' σ B) (k : Fin 2) :
    (d.mixedComponentPairEndpointEquiv τ τ' σ B (p, k)).1 =
      pairEndpointAt p.1.1 k := by
  rfl

/-- The inversion count of one pair pair is the sum of the corresponding mixed-position
comparisons. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointInversionCount_eq_sum
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts)
    (p : d.MixedComponentPair τ τ' σ B)
    (q : d.MixedComponentPair τ τ' σ C) :
    pairEndpointInversionCount p.1.1 q.1.1 =
      ∑ a : Fin 2, ∑ b : Fin 2,
        if (d.mixedComponentPairEndpointEquiv τ τ' σ C (q, b)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (p, a)).1
        then 1 else 0 := by
  rw [pairEndpointInversionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [d.mixedComponentPairEndpointEquiv_val, d.mixedComponentPairEndpointEquiv_val]

/-- Reindexing all pair endpoints gives exactly the inversion count between the complete mixed
position fibers of the two components. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointInversionSum_eq_positionInversionCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) :
    d.mixedComponentPairEndpointInversionSum τ τ' σ B C =
      d.mixedComponentPositionInversionCount τ τ' σ B C := by
  classical
  let endpointPairEquiv :
      ((d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C) ×
          (Fin 2 × Fin 2)) ≃
        (d.MixedComponentPosition τ τ' σ B ×
          d.MixedComponentPosition τ τ' σ C) :=
    (Equiv.prodProdProdComm _ _ _ _).trans
      (Equiv.prodCongr
        (d.mixedComponentPairEndpointEquiv τ τ' σ B)
        (d.mixedComponentPairEndpointEquiv τ τ' σ C))
  calc
    d.mixedComponentPairEndpointInversionSum τ τ' σ B C =
      ∑ x : (d.MixedComponentPair τ τ' σ B × d.MixedComponentPair τ τ' σ C) ×
          (Fin 2 × Fin 2),
        if (d.mixedComponentPairEndpointEquiv τ τ' σ C (x.1.2, x.2.2)).1 <
          (d.mixedComponentPairEndpointEquiv τ τ' σ B (x.1.1, x.2.1)).1
        then 1 else 0 := by
          simp only [FixedExternalTwoPointWickDiagram.mixedComponentPairEndpointInversionSum,
            Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro q _
          exact d.mixedComponentPairEndpointInversionCount_eq_sum τ τ' σ B C p q
    _ = ∑ x : d.MixedComponentPosition τ τ' σ B ×
          d.MixedComponentPosition τ τ' σ C,
        if x.2.1 < x.1.1 then 1 else 0 := by
          refine Fintype.sum_equiv endpointPairEquiv
            (fun x =>
              if (d.mixedComponentPairEndpointEquiv τ τ' σ C (x.1.2, x.2.2)).1 <
                (d.mixedComponentPairEndpointEquiv τ τ' σ B (x.1.1, x.2.1)).1
              then 1 else 0)
            (fun x => if x.2.1 < x.1.1 then 1 else 0) ?_
          intro x
          rfl
    _ = d.mixedComponentPositionInversionCount τ τ' σ B C := by
          rw [FixedExternalTwoPointWickDiagram.mixedComponentPositionInversionCount,
            Fintype.sum_prod_type]

/-- For distinct components, the geometric crossing parity is exactly the parity of the complete
mixed-position inversion count. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_positionInversionCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 =
      d.mixedComponentPositionInversionCount τ τ' σ B C % 2 := by
  rw [d.mixedComponentGeometricCrossingCount_mod_two_eq_pairEndpointInversionSum
    τ τ' σ B C hBC,
    d.mixedComponentPairEndpointInversionSum_eq_positionInversionCount τ τ' σ B C]

/-- Event-block parity is the only remaining input needed to prove even geometric crossings between
all distinct mixed-time components. -/
theorem FixedExternalTwoPointWickDiagram.mixedComponentGeometricCrossingCount_mod_two_eq_zero_of_positionInversionCount
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ)
    (B C : d.1.componentPartition.parts) (hBC : B ≠ C)
    (hEven : d.mixedComponentPositionInversionCount τ τ' σ B C % 2 = 0) :
    d.mixedComponentGeometricCrossingCount τ τ' σ B C % 2 = 0 := by
  rw [d.mixedComponentGeometricCrossingCount_mod_two_eq_positionInversionCount
    τ τ' σ B C hBC, hEven]

end Fermionic
end SecondQuantization
