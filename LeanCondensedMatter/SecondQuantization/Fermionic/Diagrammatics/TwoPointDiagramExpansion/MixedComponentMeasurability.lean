import LeanCondensedMatter.SecondQuantization.Fermionic.ImaginaryTime.MixedOrderSignature
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentChamberRegularity

set_option linter.style.header false

/-!
# Measurability of mixed two-point component factors

The raw mixed component factor is only chamberwise continuous because its dependent normalized-pair
indexing changes across order walls.  The set of mixed-order chambers is nevertheless finite: it is
indexed by `TwoPointOrderSignature`, the finite set of true strict comparisons between mixed events.

For every signature we choose one realizing base assignment when it exists and use the globally
continuous chamber representative based there.  A finite sum selects the unique representative whose
signature matches the current assignment.  This produces a globally measurable function that agrees
pointwise with the actual Dyson-signed component factor, including on the deterministic equal-time
walls.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Finite piecewise-continuous presentation of one actual Dyson-signed mixed component factor. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonSignatureRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (B : d.1.componentPartition.parts) : (Fin n → ℝ) → ℂ :=
  fun σ =>
    ∑ s : TwoPointOrderSignature n,
      if twoPointOrderSignature τ τ' σ = s then
        d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
          (twoPointOrderSignatureBase τ τ' s) B σ
      else
        0

/-- The finite signature representative agrees pointwise with the actual Dyson-signed component
factor. -/
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
    (by
      simpa [s₀] using sameTwoPointOrderChamber_signatureBase τ τ' σ)

/-- The finite signature representative is globally measurable. -/
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
  change Measurable (fun σ : Fin n → ℝ =>
    if σ ∈ twoPointOrderSignatureFiber τ τ' s then
      d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ'
        (twoPointOrderSignatureBase τ τ' s) B σ
    else 0)
  exact hFiber.ite hRep measurable_const

/-- The actual Dyson-signed mixed component factor is globally measurable, although in general only
chamberwise continuous. -/
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
