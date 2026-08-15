import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.DiagramSumIntegral
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.FiberCauchySum
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

set_option linter.style.header false

/-!
# Coefficientwise Cauchy convolution for the two-point linked-cluster theorem

The canonical external-slot fiber decomposition partitions the full order-`n` diagram sum by the
number `m` of interaction vertices in the external component.  The complementary `n - m` vertices
form the vacuum half.  `FiberCauchySum` identifies every fixed-cardinality slice with the product of
the connected two-point coefficient and the normalized vacuum coefficient.  Summing those slices
therefore gives the coefficientwise Cauchy convolution.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

open Classical in
/-- A fixed-cardinality slice of the ambient powerset is the corresponding external/vacuum Cauchy
factor.  The equality `m + k = n` is used only to identify the ambient slot type with `Fin (m + k)`. -/
private theorem powersetFiberSlice_eq_cauchyFactor
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ)
    {n m k : ℕ} (hmk : m + k = n) :
    (∑ T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin n)),
      ∑ p : {ext : FixedExternalTwoPointWickDiagramOn Mode n T i j //
              ext.1.IsExternallyConnected} ×
            QuarticWickDiagram Mode n
              ((Finset.univ : Finset (Fin n)) \ T),
        ((fixedExternalFiberEquiv T).symm p).1.dysonAmplitude ε β g τ τ') =
      connectedTwoPointDysonCoefficient ε β g i j τ τ' m *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
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

/-- **Coefficientwise linked-cluster Cauchy identity.**

At order `n`, the complete two-point Dyson coefficient is the Cauchy convolution of the connected
two-point coefficients with the normalized vacuum partition coefficients.  This is the point where
the canonical component/fiber route tracked by #1001 is consumed by #894. -/
theorem twoPointDiagramCoefficient_eq_sum_connected_mul_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    twoPointDiagramCoefficient (n := n) ε β g i j τ τ' =
      ∑ m ∈ Finset.range (n + 1),
        connectedTwoPointDysonCoefficient ε β g i j τ τ' m *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) (n - m) := by
  classical
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
  exact
    powersetFiberSlice_eq_cauchyFactor
      ε β hβ g i j τ τ' (Nat.add_sub_of_le hmn)

/-- The same coefficientwise Cauchy identity for the operator-defined Dyson coefficient. -/
theorem twoPointDysonCoefficient_eq_sum_connected_mul_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ) (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    twoPointDysonCoefficient (n := n) ε β g i j τ τ' =
      ∑ m ∈ Finset.range (n + 1),
        connectedTwoPointDysonCoefficient ε β g i j τ τ' m *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) (n - m) := by
  rw [← twoPointDiagramCoefficient_eq_twoPointDysonCoefficient]
  exact twoPointDiagramCoefficient_eq_sum_connected_mul_normalizedDysonPartitionCoeff
    ε β hβ g i j τ τ' n

end Fermionic
end SecondQuantization
