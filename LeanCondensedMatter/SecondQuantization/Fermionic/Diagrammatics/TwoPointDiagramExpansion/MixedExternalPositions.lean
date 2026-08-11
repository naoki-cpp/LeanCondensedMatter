import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.TwoPoint.VacuumLeg
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.TwoPointDiagramExpansion.MixedComponentPairing
import LeanCondensedMatter.Combinatorics.InvolutionCard

set_option linter.style.header false

/-!
# The external component's positions in mixed-time order

The amplitude evaluates `pairingInMixedOrder`, which lives on positions ordered by interaction time,
not on the combinatorial leg indexing. Splitting the amplitude therefore has to happen there.

The payoff is that a subset of a linear order can be enumerated monotonically, so the induced
splitting satisfies the strict-monotonicity hypotheses of the crossing-sign factorization for free.
Those hypotheses are not a technical convenience: a pair value here is the expectation of an
*ordered* composition of operators, so a part only carries the same quantity the ambient does when
its embedding preserves order.

This module names the set of mixed-order positions lying in the external component, and records the
two facts a splitting needs: it is closed under the pairing, and therefore has even size.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

open Classical in
/-- The mixed-time-ordered positions lying in the external component. -/
noncomputable def FixedExternalTwoPointWickDiagram.externalMixedPositions
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) : Finset (Fin (2 * (2 * n + 1))) :=
  Finset.univ.filter fun p => ¬ d.1.LegIsVacuum (mixedTimeAmbientPositionEquiv τ τ' σ p)

open Classical in
theorem FixedExternalTwoPointWickDiagram.mem_externalMixedPositions_iff
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1))) :
    p ∈ d.externalMixedPositions τ τ' σ ↔
      ¬ d.1.LegIsVacuum (mixedTimeAmbientPositionEquiv τ τ' σ p) := by
  simp [FixedExternalTwoPointWickDiagram.externalMixedPositions]

/-- **The external positions are closed under the pairing.** A contraction never joins the external
component to a vacuum component. -/
theorem FixedExternalTwoPointWickDiagram.partner_mem_externalMixedPositions
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) (p : Fin (2 * (2 * n + 1)))
    (hp : p ∈ d.externalMixedPositions τ τ' σ) :
    (d.pairingInMixedOrder τ τ' σ).partner p ∈ d.externalMixedPositions τ τ' σ := by
  rw [d.mem_externalMixedPositions_iff] at hp ⊢
  rw [d.mixedTimeAmbientPositionEquiv_partner τ τ' σ p]
  intro hvac
  exact hp ((d.1.legIsVacuum_partner_iff _).1 hvac)

/-- **The external positions come in pairs.** -/
theorem FixedExternalTwoPointWickDiagram.even_card_externalMixedPositions
    {n : ℕ} {i j : Mode} (d : FixedExternalTwoPointWickDiagram Mode n i j)
    (τ τ' : ℝ) (σ : Fin n → ℝ) :
    Even (d.externalMixedPositions τ τ' σ).card :=
  (d.pairingInMixedOrder τ τ' σ).even_card_of_partner_mem
    (d.partner_mem_externalMixedPositions τ τ' σ)

end Fermionic
end SecondQuantization
