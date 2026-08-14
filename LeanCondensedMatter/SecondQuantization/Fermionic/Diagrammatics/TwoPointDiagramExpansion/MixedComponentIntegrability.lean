import LeanCondensedMatter.Analysis.OrderedSimplex.FiniteSelectionIntegrability
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentLocalTime

set_option linter.style.header false

/-!
# Integrability of localized mixed two-point component factors

PR #749 expresses each ambient Dyson-signed component factor as a finite measurable selection of
continuous fixed-signature chamber representatives.  PR #760 transports the resulting measurability
to the canonical local component coordinates.

Here we transport the *branches* as well.  For every local assignment, the actual localized factor
agrees with the chamber representative indexed by that assignment's finite mixed-order signature.
The family of such branches is finite and every fixed branch is continuous.  The generic compact-box
lemma from `Analysis.OrderedSimplex.FiniteSelectionIntegrability` therefore gives a uniform bound and
Bochner integrability on the bounded coordinate box containing the ordered simplex.

No continuity of the raw selected factor across order walls is asserted.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open MeasureTheory
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The explicit order-`n` interaction-time assignment induced by one component-local assignment. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentLocalSlotTime
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts)
    (localTime : Fin (d.1.interactionComponentSize B) → ℝ) : Fin n → ℝ :=
  fun k =>
    DependentSlotEquiv.ofAssignment shuffle.slotEquiv B localTime
      (Fin.cast (by simp) k)

omit [LinearOrder Mode] [Fintype Mode] in
/-- The component-local to explicit order-`n` slot map is continuous. -/
theorem FixedExternalTwoPointWickDiagram.continuous_mixedComponentLocalSlotTime
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts) :
    Continuous (d.mixedComponentLocalSlotTime shuffle B) := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentLocalSlotTime
  exact continuous_pi fun k =>
    (continuous_apply (Fin.cast (by simp) k)).comp
      (DependentSlotEquiv.continuous_ofAssignment shuffle.slotEquiv B)

/-- The public local-slot presentation agrees definitionally with the canonical localized factor. -/
@[simp]
theorem FixedExternalTwoPointWickDiagram.mixedComponentDysonLocalIntegrand_apply
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts)
    (localTime : Fin (d.1.interactionComponentSize B) → ℝ) :
    d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B localTime =
      d.mixedComponentDysonFixedTimeValue ε β g τ τ'
        (d.mixedComponentLocalSlotTime shuffle B localTime) B := by
  rfl

/-- A fixed ambient chamber representative restricted to one component-local coordinate fiber. -/
noncomputable def FixedExternalTwoPointWickDiagram.mixedComponentDysonLocalChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ)
    (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts) :
    (Fin (d.1.interactionComponentSize B) → ℝ) → ℂ :=
  fun localTime =>
    d.mixedComponentDysonFixedTimeChamberRepresentative ε β g τ τ' σ₀ B
      (d.mixedComponentLocalSlotTime shuffle B localTime)

/-- Every fixed-signature localized chamber representative is globally continuous. -/
theorem FixedExternalTwoPointWickDiagram.continuous_mixedComponentDysonLocalChamberRepresentative
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (σ₀ : Fin n → ℝ)
    (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts) :
    Continuous (d.mixedComponentDysonLocalChamberRepresentative
      ε β g τ τ' σ₀ shuffle B) := by
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonLocalChamberRepresentative
  exact
    (d.continuous_mixedComponentDysonFixedTimeChamberRepresentative
      ε β g τ τ' σ₀ B).comp
      (d.continuous_mixedComponentLocalSlotTime shuffle B)

/-- At every local assignment the actual localized factor agrees with the continuous branch indexed
by the assignment's finite mixed-order signature. -/
theorem FixedExternalTwoPointWickDiagram.exists_mixedComponentDysonLocalChamberRepresentative_eq
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts)
    (localTime : Fin (d.1.interactionComponentSize B) → ℝ) :
    ∃ s : TwoPointOrderSignature n,
      d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B localTime =
        d.mixedComponentDysonLocalChamberRepresentative ε β g τ τ'
          (twoPointOrderSignatureBase τ τ' s) shuffle B localTime := by
  let σ := d.mixedComponentLocalSlotTime shuffle B localTime
  let s := twoPointOrderSignature τ τ' σ
  refine ⟨s, ?_⟩
  rw [d.mixedComponentDysonLocalIntegrand_apply ε β g τ τ' shuffle B localTime]
  unfold FixedExternalTwoPointWickDiagram.mixedComponentDysonLocalChamberRepresentative
  exact
    (d.mixedComponentDysonFixedTimeChamberRepresentative_eq_of_sameOrderChamber
      ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) σ B
      (by simpa [σ, s] using sameTwoPointOrderChamber_signatureBase τ τ' σ)).symm

/-- The actual canonical localized component factor is uniformly norm-bounded on the compact
ordered-simplex coordinate box. -/
theorem FixedExternalTwoPointWickDiagram.exists_norm_bound_mixedComponentDysonLocalIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts) :
    ∃ C : ℝ, ∀ localTime ∈
        intervalIntegral.orderedSimplexTimeBox (d.1.interactionComponentSize B) β,
      ‖d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B localTime‖ ≤ C := by
  apply intervalIntegral.exists_norm_bound_on_compact_of_finite_continuous_selection
    (K := intervalIntegral.orderedSimplexTimeBox (d.1.interactionComponentSize B) β)
    (hK := intervalIntegral.isCompact_orderedSimplexTimeBox
      (d.1.interactionComponentSize B) β)
    (f := d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B)
    (g := fun s : TwoPointOrderSignature n =>
      d.mixedComponentDysonLocalChamberRepresentative ε β g τ τ'
        (twoPointOrderSignatureBase τ τ' s) shuffle B)
  · intro s
    exact d.continuous_mixedComponentDysonLocalChamberRepresentative
      ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) shuffle B
  · intro localTime _
    exact d.exists_mixedComponentDysonLocalChamberRepresentative_eq
      ε β g τ τ' shuffle B localTime

/-- Every canonical localized Dyson-signed component factor is Bochner integrable on the compact
coordinate box containing its ordered-simplex integration domain for every measure finite on compact
sets. -/
theorem FixedExternalTwoPointWickDiagram.integrableOn_mixedComponentDysonLocalIntegrand
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (τ τ' : ℝ) (shuffle : d.1.ComponentInteractionShuffle)
    (B : d.1.componentPartition.parts)
    (μ : Measure (Fin (d.1.interactionComponentSize B) → ℝ))
    [IsFiniteMeasureOnCompacts μ] :
    IntegrableOn
      (d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B)
      (intervalIntegral.orderedSimplexTimeBox (d.1.interactionComponentSize B) β) μ := by
  apply intervalIntegral.integrableOn_orderedSimplexTimeBox_of_finite_continuous_selection
    (n := d.1.interactionComponentSize B) (β := β) (μ := μ)
    (f := d.mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B)
    (g := fun s : TwoPointOrderSignature n =>
      d.mixedComponentDysonLocalChamberRepresentative ε β g τ τ'
        (twoPointOrderSignatureBase τ τ' s) shuffle B)
  · exact d.measurable_mixedComponentDysonLocalIntegrand ε β g τ τ' shuffle B
  · intro s
    exact d.continuous_mixedComponentDysonLocalChamberRepresentative
      ε β g τ τ' (twoPointOrderSignatureBase τ τ' s) shuffle B
  · intro localTime _
    exact d.exists_mixedComponentDysonLocalChamberRepresentative_eq
      ε β g τ τ' shuffle B localTime

end Fermionic
end SecondQuantization
