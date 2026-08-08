import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.ExternalVacuumEquiv
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.OrderedAmplitude
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.IntegratedDiagramSum
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonConnectedDiagramExpansion
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonVertexMoment
import Mathlib.RingTheory.PowerSeries.Inverse

set_option linter.style.header false

/-!
# Normalized two-point linked-cluster theorem

This is the final owner for the finite-mode imaginary-time two-point LCT.  The structural input is
one connected component carrying the two distinguished external legs plus an arbitrary quartic
vacuum remainder.  The analytic input is the a.e. interaction-relabel covariance and integrated
component-shuffle factorization.
-/

namespace SecondQuantization
namespace Fermionic

open PowerSeries

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-- Externally connected two-point diagrams on an arbitrary finite interaction set, with the two
external labels fixed to `T c_i c_j†`. -/
abbrev ConnectedFixedExternalTwoPointWickDiagramOn
    (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :=
  {d : Common.ExternallyConnectedTwoPointDiagram
      (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) N S //
    d.1.externalLabel = twoPointExternalLabels i j}

/-- Fixed-external diagrams on explicit interaction slots whose full graph is externally connected. -/
abbrev ConnectedFixedExternalTwoPointWickDiagram
    (Mode : Type*) (n : ℕ) (i j : Mode) :=
  {d : FixedExternalTwoPointWickDiagram Mode n i j // d.1.IsExternallyConnected}

/-- Binary decomposition data for a fixed-external two-point diagram: a connected external core on
`E` and an arbitrary quartic vacuum diagram on the complementary interaction vertices. -/
abbrev FixedExternalVacuumDecomposition
    (Mode : Type*) (N : ℕ) (S : Finset (Fin N)) (i j : Mode) :=
  Σ E : {E : Finset (Fin N) // E ⊆ S},
    ConnectedFixedExternalTwoPointWickDiagramOn Mode N E.1 i j ×
      QuarticWickDiagram Mode N (S \ E.1)

/-- Forget only the proof that the external labels are fixed. -/
noncomputable def FixedExternalVacuumDecomposition.toCommon
    {S : Finset (Fin N)} {i j : Mode}
    (x : FixedExternalVacuumDecomposition Mode N S i j) :
    Common.TwoPointDiagram.ExternalVacuumDecomposition
      (ExternalFieldLabel Mode) (QuarticVertexLabel Mode) N S :=
  ⟨x.1, x.2.1.1, x.2.2⟩

private theorem FixedExternalVacuumDecomposition.toCommon_injective
    {S : Finset (Fin N)} {i j : Mode} :
    Function.Injective
      (FixedExternalVacuumDecomposition.toCommon
        (Mode := Mode) (N := N) (S := S) (i := i) (j := j)) := by
  rintro ⟨E, external, vacuum⟩ ⟨F, external', vacuum'⟩ h
  dsimp [FixedExternalVacuumDecomposition.toCommon] at h
  cases h
  rfl

/-- Reassemble fixed-external binary decomposition data. -/
noncomputable def reassembleFixedExternalVacuumData
    {S : Finset (Fin N)} {i j : Mode}
    (x : FixedExternalVacuumDecomposition Mode N S i j) :
    FixedExternalTwoPointWickDiagramOn Mode N S i j :=
  ⟨Common.TwoPointDiagram.reassembleExternalVacuum x.1.2 x.2.1.1 x.2.2, by
    simpa using x.2.1.2⟩

private theorem reassembleFixedExternalVacuumData_injective
    {S : Finset (Fin N)} {i j : Mode} :
    Function.Injective
      (reassembleFixedExternalVacuumData
        (Mode := Mode) (N := N) (S := S) (i := i) (j := j)) := by
  intro x y h
  apply FixedExternalVacuumDecomposition.toCommon_injective
  apply Common.TwoPointDiagram.reassembleExternalVacuumData_injective
  exact congrArg Subtype.val h

private theorem reassembleFixedExternalVacuumData_surjective
    {S : Finset (Fin N)} {i j : Mode} :
    Function.Surjective
      (reassembleFixedExternalVacuumData
        (Mode := Mode) (N := N) (S := S) (i := i) (j := j)) := by
  intro d
  let external : ConnectedFixedExternalTwoPointWickDiagramOn Mode N
      d.1.externalInteractionPart i j :=
    ⟨⟨d.1.restrictExternalComponent,
      d.1.restrictExternalComponent_isExternallyConnected⟩, by
        simpa using d.2⟩
  let x : FixedExternalVacuumDecomposition Mode N S i j :=
    ⟨⟨d.1.externalInteractionPart, d.1.externalInteractionPart_subset⟩,
      external, d.1.restrictVacuumRemainder⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  exact d.1.reassemble_restrictExternal_restrictVacuumRemainder

/-- Fixed-external diagrams are exactly a connected external core on a subset of the interaction
vertices together with an arbitrary quartic vacuum remainder on the complement. -/
noncomputable def fixedExternalVacuumDecompositionEquiv
    (S : Finset (Fin N)) (i j : Mode) :
    FixedExternalTwoPointWickDiagramOn Mode N S i j ≃
      FixedExternalVacuumDecomposition Mode N S i j :=
  (Equiv.ofBijective
    (reassembleFixedExternalVacuumData
      (Mode := Mode) (N := N) (S := S) (i := i) (j := j))
    ⟨reassembleFixedExternalVacuumData_injective,
      reassembleFixedExternalVacuumData_surjective⟩).symm

/-- Reindex a finite sum over fixed-external two-point diagrams by the unique connected external
core and arbitrary vacuum remainder. -/
theorem sum_fixedExternalTwoPointWickDiagramOn_eq_sum_externalVacuum
    {S : Finset (Fin N)} (i j : Mode)
    (F : FixedExternalTwoPointWickDiagramOn Mode N S i j → ℂ) :
    (∑ d : FixedExternalTwoPointWickDiagramOn Mode N S i j, F d) =
      ∑ x : FixedExternalVacuumDecomposition Mode N S i j,
        F (reassembleFixedExternalVacuumData x) := by
  rw [← Equiv.sum_comp (fixedExternalVacuumDecompositionEquiv S i j).symm F]
  rfl

/-- The unnormalized order-`n` two-point diagram coefficient, as a finite sum of integrated
fixed-external diagram amplitudes. -/
noncomputable def twoPointUnnormalizedDiagramCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d : FixedExternalTwoPointWickDiagram Mode n i j,
    d.dysonAmplitude ε β g τ τ'

/-- The order-`n` connected external-core contribution.  In the present one-leg/one-leg quartic
setup this is equivalently the sum over diagrams with no vacuum component. -/
noncomputable def twoPointConnectedDiagramCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (n : ℕ) : ℂ :=
  ∑ d : ConnectedFixedExternalTwoPointWickDiagram Mode n i j,
    d.1.dysonAmplitude ε β g τ τ'

/-- The diagrammatic numerator coefficient is the existing integrated two-point coefficient. -/
theorem twoPointUnnormalizedDiagramCoeff_eq_twoPointDiagramCoefficient
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    twoPointUnnormalizedDiagramCoeff ε β g i j τ τ' n =
      twoPointDiagramCoefficient (n := n) ε β g i j τ τ' := by
  exact (twoPointDiagramCoefficient_eq_sum_dysonAmplitude
    ε β g i j τ τ').symm

/-- Formal unnormalized two-point numerator series. -/
noncomputable def twoPointUnnormalizedDiagramSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (twoPointUnnormalizedDiagramCoeff ε β g i j τ τ')

/-- Formal series of diagrams connected to the external pair. -/
noncomputable def twoPointConnectedDiagramSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (twoPointConnectedDiagramCoeff ε β g i j τ τ')

/-- Vacuum Dyson series normalized by the free partition function. -/
noncomputable def normalizedVacuumDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) : PowerSeries ℂ :=
  PowerSeries.normalizeByConstantCoeff
    (dysonPartitionSeries ε β (quarticInteraction g))

@[simp]
theorem coeff_twoPointUnnormalizedDiagramSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    PowerSeries.coeff n
        (twoPointUnnormalizedDiagramSeries ε β g i j τ τ') =
      twoPointUnnormalizedDiagramCoeff ε β g i j τ τ' n := by
  simp [twoPointUnnormalizedDiagramSeries]

@[simp]
theorem coeff_twoPointConnectedDiagramSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) (n : ℕ) :
    PowerSeries.coeff n
        (twoPointConnectedDiagramSeries ε β g i j τ τ') =
      twoPointConnectedDiagramCoeff ε β g i j τ τ' n := by
  simp [twoPointConnectedDiagramSeries]

@[simp]
theorem coeff_normalizedVacuumDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (n : ℕ) :
    PowerSeries.coeff n (normalizedVacuumDysonSeries ε β g) =
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) n := by
  rw [normalizedVacuumDysonSeries, PowerSeries.coeff_normalizeByConstantCoeff,
    constantCoeff_dysonPartitionSeries, coeff_dysonPartitionSeries]
  unfold normalizedDysonPartitionCoeff
  rw [div_eq_inv_mul]

@[simp]
theorem constantCoeff_normalizedVacuumDysonSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    PowerSeries.constantCoeff (normalizedVacuumDysonSeries ε β g) = 1 := by
  exact constantCoeff_normalizeByConstantCoeff_dysonPartitionSeries
    ε β (quarticInteraction g)

/-- Formal normalized two-point series, obtained by cancelling the normalized vacuum series. -/
noncomputable def twoPointNormalizedDiagramSeries
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ) : PowerSeries ℂ :=
  twoPointUnnormalizedDiagramSeries ε β g i j τ τ' *
    (normalizedVacuumDysonSeries ε β g)⁻¹

/-- Once the numerator factorization is established, formal vacuum cancellation is immediate because
the normalized vacuum series has constant coefficient one. -/
theorem twoPointNormalizedDiagramSeries_eq_connected_of_factorization
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (i j : Mode) (τ τ' : ℝ)
    (hfactor :
      twoPointUnnormalizedDiagramSeries ε β g i j τ τ' =
        twoPointConnectedDiagramSeries ε β g i j τ τ' *
          normalizedVacuumDysonSeries ε β g) :
    twoPointNormalizedDiagramSeries ε β g i j τ τ' =
      twoPointConnectedDiagramSeries ε β g i j τ τ' := by
  rw [twoPointNormalizedDiagramSeries, hfactor, mul_assoc,
    PowerSeries.mul_inv_cancel _ (by
      rw [constantCoeff_normalizedVacuumDysonSeries]
      exact one_ne_zero), mul_one]

end Fermionic
end SecondQuantization
