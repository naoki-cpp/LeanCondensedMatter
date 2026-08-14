import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.MixedOrderSignature
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentChamberRegularity

set_option linter.style.header false

/-!
# Measurability of mixed two-point component factors

The raw mixed component factor is only chamberwise continuous because its dependent normalized-pair
indexing changes across order walls. The Common-owned `TwoPointOrderSignature` gives a finite
measurable partition by mixed-event order; this module uses it to assemble a globally measurable
fermionic component factor.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Finite piecewise-continuous presentation of the actual Dyson-signed component factor, selecting
the chamber representative indexed by the current Common mixed-order signature. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonSignatureRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (B : d.1.componentPartition.parts) : (Fin n → ℝ) → ℂ :=
  fun σ =>
    ∑ s : TwoPointOrderSignature n,
      if twoPointOrderSignature τ τ' σ = s then
        d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
          (twoPointOrderSignatureBase τ τ' s) B σ
      else 0

theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonSignatureRepresentative_eq
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (B : d.1.componentPartition.parts) (σ : Fin n → ℝ) :
    d.mixedComponentDysonSignatureRepresentative ε β g τ τ' B σ =
      d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
  classical
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonSignatureRepresentative
  let s₀ := twoPointOrderSignature τ τ' σ
  have hsum :
      (∑ s : TwoPointOrderSignature n,
        if twoPointOrderSignature τ τ' σ = s then
          d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
            (twoPointOrderSignatureBase τ τ' s) B σ
        else 0) =
      d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
        (twoPointOrderSignatureBase τ τ' s₀) B σ := by
    change (∑ s : TwoPointOrderSignature n,
        if s₀ = s then
          d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
            (twoPointOrderSignatureBase τ τ' s) B σ
        else 0) =
      d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
        (twoPointOrderSignatureBase τ τ' s₀) B σ
    simp
  rw [hsum]
  exact d.mixedComponentDysonFixedTimeChamberRepresentative_eq_of_sameOrderChamber
    ε β g τ τ'
    (twoPointOrderSignatureBase τ τ' s₀) σ B
    (by simpa [s₀] using sameTwoPointOrderChamber_signatureBase τ τ' σ)

theorem FixedExternalTwoPointWickDiagram.measurable_mixedComponentDysonSignatureRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (B : d.1.componentPartition.parts) :
    Measurable (d.mixedComponentDysonSignatureRepresentative ε β g τ τ' B) := by
  classical
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonSignatureRepresentative
  apply Finset.measurable_sum
  intro s _
  have hFiber := measurableSet_twoPointOrderSignatureFiber τ τ' s
  have hRep :=
    (d.continuous_mixedComponentDysonFixedTimeChamberRepresentative
      ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) B).measurable
  simpa only [twoPointOrderSignatureFiber, Set.mem_setOf_eq] using
    (Measurable.ite hFiber hRep measurable_const)

theorem FixedExternalTwoPointWickDiagram.measurable_mixedComponentDysonFixedTimeValue
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (B : d.1.componentPartition.parts) :
    Measurable (fun σ : Fin n → ℝ =>
      d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B) := by
  have hRep :=
    d.measurable_mixedComponentDysonSignatureRepresentative ε β g τ τ' B
  have hEq :
      d.mixedComponentDysonSignatureRepresentative ε β g τ τ' B =
        fun σ : Fin n → ℝ =>
          d.mixedComponentDysonFixedTimeValue ε β g τ τ' σ B := by
    funext σ
    exact d.mixedComponentDysonSignatureRepresentative_eq ε β g τ τ' B σ
  rw [← hEq]
  exact hRep

end Fermionic
end SecondQuantization
