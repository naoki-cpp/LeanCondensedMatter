import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointLinkedClusterTheorem
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.ExternalVacuumShuffleProduct

set_option linter.style.header false

/-!
# Coefficient convolution for the normalized two-point linked-cluster theorem

The integrated binary external/vacuum factorization is now available for every fixed size of the
external component. This file performs the final finite reindex by that size, obtains the ordinary
coefficient convolution with the normalized vacuum Dyson series, and exposes the normalized
connected two-point coefficient theorem.
-/

namespace SecondQuantization
namespace Fermionic

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Fixed-external diagrams at total order `n` whose external component contains exactly `k`
interaction vertices. -/
abbrev FixedExternalTwoPointWickDiagramAtExternalOrder
    (Mode : Type*) (n k : ℕ) (i j : Mode) :=
  {d : FixedExternalTwoPointWickDiagram Mode n i j //
    d.1.externalInteractionPart.card = k}

/-- Every full fixed-external diagram is uniquely classified by the number of interaction vertices
in its external component. -/
noncomputable def fixedExternalTwoPointWickDiagramExternalOrderEquiv
    (n : ℕ) (i j : Mode) :
    FixedExternalTwoPointWickDiagram Mode n i j ≃
      Σ k : Fin (n + 1),
        FixedExternalTwoPointWickDiagramAtExternalOrder Mode n k.1 i j where
  toFun d := by
    have hcard : d.1.externalInteractionPart.card < n + 1 := by
      apply Nat.lt_succ_of_le
      calc
        d.1.externalInteractionPart.card ≤
            (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card d.1.externalInteractionPart_subset
        _ = n := by simp
    exact ⟨⟨d.1.externalInteractionPart.card, hcard⟩, ⟨d, rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨k, d⟩
    have hk :
        (⟨d.1.1.externalInteractionPart.card, by
          apply Nat.lt_succ_of_le
          calc
            d.1.1.externalInteractionPart.card ≤
                (Finset.univ : Finset (Fin n)).card :=
              Finset.card_le_card d.1.1.externalInteractionPart_subset
            _ = n := by simp⟩ : Fin (n + 1)) = k := by
      apply Fin.ext
      exact d.2
    cases hk
    rfl

/-- The external-order fiber at `(k,m)` factors whenever `k+m=n`. -/
theorem sum_fixedExternalTwoPointWickDiagramAtExternalOrder_eq_connected_mul_vacuum
    {n k m : ℕ} (hkm : (k, m) ∈ Finset.antidiagonal n)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    (∑ d : FixedExternalTwoPointWickDiagramAtExternalOrder Mode n k i j,
        d.1.dysonAmplitude ε β g τ τ') =
      twoPointConnectedDiagramCoeff ε β g i j τ τ' k *
        normalizedDysonPartitionCoeff ε β (quarticInteraction g) m := by
  rw [Finset.mem_antidiagonal] at hkm
  subst n
  simpa [twoPointConnectedDiagramCoeff] using
    (sum_fixedExternalTwoPointWickDiagramOfExternalOrder_eq_connected_mul_vacuum
      (Mode := Mode) (k := k) (m := m) i j ε β g τ τ')

/-- The unnormalized order-`n` two-point coefficient is the ordinary convolution of the connected
external-core coefficient with the normalized vacuum Dyson coefficient. -/
theorem twoPointUnnormalizedDiagramCoeff_eq_connected_vacuum_convolution
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    twoPointUnnormalizedDiagramCoeff ε β g i j τ τ' n =
      ∑ p ∈ Finset.antidiagonal n,
        twoPointConnectedDiagramCoeff ε β g i j τ τ' p.1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) p.2 := by
  classical
  let amp : FixedExternalTwoPointWickDiagram Mode n i j → ℂ :=
    fun d => d.dysonAmplitude ε β g τ τ'
  calc
    twoPointUnnormalizedDiagramCoeff ε β g i j τ τ' n =
      ∑ d : FixedExternalTwoPointWickDiagram Mode n i j, amp d := by
        rfl
    _ = ∑ x : Σ k : Fin (n + 1),
          FixedExternalTwoPointWickDiagramAtExternalOrder Mode n k.1 i j,
        amp x.2.1 := by
      rw [← Equiv.sum_comp
        (fixedExternalTwoPointWickDiagramExternalOrderEquiv n i j).symm amp]
      rfl
    _ = ∑ k : Fin (n + 1),
        ∑ d : FixedExternalTwoPointWickDiagramAtExternalOrder Mode n k.1 i j,
          amp d.1 := by
      rw [Fintype.sum_sigma]
    _ = ∑ p : ↥(Finset.antidiagonal n),
        ∑ d : FixedExternalTwoPointWickDiagramAtExternalOrder Mode n p.1.1 i j,
          amp d.1 := by
      simpa [Finset.Nat.antidiagonalEquivFin] using
        (Equiv.sum_comp (Finset.Nat.antidiagonalEquivFin n)
          (fun k : Fin (n + 1) =>
            ∑ d : FixedExternalTwoPointWickDiagramAtExternalOrder Mode n k.1 i j,
              amp d.1)).symm
    _ = ∑ p : ↥(Finset.antidiagonal n),
        twoPointConnectedDiagramCoeff ε β g i j τ τ' p.1.1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) p.1.2 := by
      apply Fintype.sum_congr
      intro p
      exact sum_fixedExternalTwoPointWickDiagramAtExternalOrder_eq_connected_mul_vacuum
        p.2 ε β g i j τ τ'
    _ = ∑ p ∈ Finset.antidiagonal n,
        twoPointConnectedDiagramCoeff ε β g i j τ τ' p.1 *
          normalizedDysonPartitionCoeff ε β (quarticInteraction g) p.2 := by
      rw [← Finset.sum_subtype (Finset.antidiagonal n) (fun _ => Iff.rfl)]
      rfl

/-- The unnormalized numerator series factors into the connected external series and normalized
vacuum series. -/
theorem twoPointUnnormalizedDiagramSeries_eq_connected_mul_normalizedVacuum
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointUnnormalizedDiagramSeries ε β g i j τ τ' =
      twoPointConnectedDiagramSeries ε β g i j τ τ' *
        normalizedVacuumDysonSeries ε β g := by
  apply twoPointUnnormalizedDiagramSeries_eq_mul_of_coeff_convolution
  intro n
  exact twoPointUnnormalizedDiagramCoeff_eq_connected_vacuum_convolution
    ε β g i j τ τ' n

/-- The normalized formal two-point series is exactly the series of diagrams connected to the two
external legs. -/
theorem twoPointNormalizedDiagramSeries_eq_connected
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) :
    twoPointNormalizedDiagramSeries ε β g i j τ τ' =
      twoPointConnectedDiagramSeries ε β g i j τ τ' := by
  exact twoPointNormalizedDiagramSeries_eq_connected_of_factorization
    ε β g i j τ τ'
    (twoPointUnnormalizedDiagramSeries_eq_connected_mul_normalizedVacuum
      ε β g i j τ τ')

/-- **Normalized two-point linked-cluster theorem.** At every perturbative order, the normalized
finite-mode imaginary-time two-point coefficient equals the sum of fixed-external Wick diagrams
whose complete graph is externally connected. Equivalently in this two-external-leg quartic setup,
these are exactly the diagrams with no vacuum component. -/
theorem normalizedTwoPointDiagramCoeff_eq_sum_externallyConnected
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    PowerSeries.coeff n (twoPointNormalizedDiagramSeries ε β g i j τ τ') =
      twoPointConnectedDiagramCoeff ε β g i j τ τ' n := by
  rw [twoPointNormalizedDiagramSeries_eq_connected]
  exact coeff_twoPointConnectedDiagramSeries ε β g i j τ τ' n

end Fermionic
end SecondQuantization
