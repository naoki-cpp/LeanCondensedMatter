import LeanCondensedMatter.Combinatorics.PerfectPairing.Evaluation
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.WickDiagram.LegFamily
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsExpectationBridge
import LeanCondensedMatter.SecondQuantization.Common.Thermal.BlochDeDominicis.PairingWeight
import LeanCondensedMatter.Analysis.OrderedSimplex.Integral

set_option linter.style.header false

/-!
# Ordered-simplex quartic Wick-diagram amplitudes

This module assembles vertex-order transport and scalar ordered-simplex integration into the
quartic Wick-diagram amplitude. Pair contractions are defined through the canonical free Gibbs
density-state expectation; finite Gibbs coordinate formulas remain downstream evaluation tools.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode] {N : ℕ}

/-! ## Time-assigned operators, per vertex order -/

/-- The time-evolved operator at a flattened leg position for a fixed vertex order. -/
noncomputable def orderedQuarticLegOperator (ε : Mode → ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ) :
    Fin (2 * (2 * S.card)) → OccupationFock Mode →ₗ[ℂ] OccupationFock Mode :=
  quarticLegOperatorForSequence ε (fun i => d.vertexLabel (order i)) τ

/-! ## Pair contraction values -/

/-- The canonical free Gibbs density-state value of two flattened leg positions. -/
noncomputable def orderedQuarticPairValue (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ)
    (a b : Fin (2 * (2 * S.card))) : ℂ :=
  (freeGibbsDensityOperator ε β).expectation
    (Common.finiteHilbertOperator
      ((orderedQuarticLegOperator ε d order τ a).comp
        (orderedQuarticLegOperator ε d order τ b)))

/-- The Wick pair value is the canonical free Gibbs density-state expectation of the transported
operator product. -/
theorem orderedQuarticPairValue_eq_freeGibbsDensityOperator_expectation
    (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ)
    (a b : Fin (2 * (2 * S.card))) :
    orderedQuarticPairValue ε β d order τ a b =
      (freeGibbsDensityOperator ε β).expectation
        (Common.finiteHilbertOperator
          ((orderedQuarticLegOperator ε d order τ a).comp
            (orderedQuarticLegOperator ε d order τ b))) :=
  rfl

/-! ## Coupling weight compatibility -/

/-- Fermionic compatibility name for the statistics-independent Common quartic vertex weight. -/
noncomputable def QuarticWickDiagram.couplingWeight {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (g : QuarticVertexLabel Mode → ℂ) : ℂ :=
  d.vertexWeight g

/-! ## Fixed-order Wick integrand and ordered-simplex contribution -/

/-- The fixed-order Wick contraction integrand. -/
noncomputable def QuarticWickDiagram.contractionIntegrand (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S)
    (τ : Fin S.card → ℝ) : ℂ :=
  (d.pairingInOrder order).evaluation
    ((d.pairingInOrder order).weight Common.Statistics.fermion)
    (orderedQuarticPairValue ε β d order τ)

/-- The fixed-order contribution integrated over the ordered simplex. -/
noncomputable def QuarticWickDiagram.orderedSimplexContribution (ε : Mode → ℝ) (β : ℝ)
    {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S) : ℂ :=
  intervalIntegral.orderedSimplexIntegral S.card β (d.contractionIntegrand ε β order)

/-! ## Continuity in the time assignment -/

/-- Closed form of a pair value after extracting the imaginary-time exponential factors. -/
theorem orderedQuarticPairValue_eq (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S) (τ : Fin S.card → ℝ)
    (a b : Fin (2 * (2 * S.card))) :
    orderedQuarticPairValue ε β d order τ a b =
      Complex.exp
          ((τ (Common.orderedQuarticLegEquiv S.card a).1 *
              quarticLocalLegEnergyShift ε
                (d.vertexLabel (order (Common.orderedQuarticLegEquiv S.card a).1))
                (Common.orderedQuarticLegEquiv S.card a).2 : ℝ) : ℂ) *
        Complex.exp
          ((τ (Common.orderedQuarticLegEquiv S.card b).1 *
              quarticLocalLegEnergyShift ε
                (d.vertexLabel (order (Common.orderedQuarticLegEquiv S.card b).1))
                (Common.orderedQuarticLegEquiv S.card b).2 : ℝ) : ℂ) *
        (freeGibbsDensityOperator ε β).expectation
          (Common.finiteHilbertOperator
            ((quarticLocalLegOperator
                (d.vertexLabel (order (Common.orderedQuarticLegEquiv S.card a).1))
                (Common.orderedQuarticLegEquiv S.card a).2).comp
              (quarticLocalLegOperator
                (d.vertexLabel (order (Common.orderedQuarticLegEquiv S.card b).1))
                (Common.orderedQuarticLegEquiv S.card b).2))) := by
  simp only [orderedQuarticPairValue, orderedQuarticLegOperator, quarticLegOperatorForSequence,
    freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
    imaginaryTimeEvolve_quarticLocalLegOperator, LinearMap.smul_comp, LinearMap.comp_smul,
    smul_smul, Common.finiteGibbsExpectation_smul]
  ring

/-- A pair value is continuous in the time assignment. -/
theorem continuous_orderedQuarticPairValue (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S)
    (a b : Fin (2 * (2 * S.card))) :
    Continuous (fun τ : Fin S.card → ℝ => orderedQuarticPairValue ε β d order τ a b) := by
  simp only [orderedQuarticPairValue_eq]
  fun_prop

/-- The fixed-order contraction integrand is continuous. -/
theorem continuous_contractionIntegrand (ε : Mode → ℝ) (β : ℝ) {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (order : Common.QuarticVertexOrder S) :
    Continuous (d.contractionIntegrand ε β order) := by
  have heq : d.contractionIntegrand ε β order = fun τ =>
      (d.pairingInOrder order).weight Common.Statistics.fermion *
        ∏ pr ∈ (d.pairingInOrder order).pairs, orderedQuarticPairValue ε β d order τ pr.1 pr.2 :=
    rfl
  rw [heq]
  exact continuous_const.mul
    (continuous_finsetProd _ fun pr _ => continuous_orderedQuarticPairValue ε β d order pr.1 pr.2)

/-! ## The diagram amplitude -/

/-- The quartic Wick-diagram amplitude, including the Dyson sign and all vertex orders. -/
noncomputable def quarticWickDiagramAmplitude (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ) {S : Finset (Fin N)} (d : QuarticWickDiagram Mode N S) : ℂ :=
  (-1 : ℂ) ^ S.card * d.couplingWeight g *
    ∑ order : Common.QuarticVertexOrder S, d.orderedSimplexContribution ε β order

/-! ## Basic lemmas -/

/-- There is exactly one vertex order on the empty vertex set. -/
instance quarticVertexOrderUniqueEmpty : Unique (Common.QuarticVertexOrder (∅ : Finset (Fin N))) where
  default := by
    haveI : IsEmpty (↥(∅ : Finset (Fin N))) := Finset.isEmpty_coe_sort.2 rfl
    haveI : IsEmpty (Fin (Finset.card (∅ : Finset (Fin N)))) := by
      rw [Finset.card_empty]; infer_instance
    exact Equiv.equivOfIsEmpty (Fin (Finset.card (∅ : Finset (Fin N)))) _
  uniq _ := Subsingleton.elim _ _

/-- The empty-vertex-set amplitude is one. -/
@[simp]
theorem quarticWickDiagramAmplitude_empty (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (d : QuarticWickDiagram Mode N (∅ : Finset (Fin N))) :
    quarticWickDiagramAmplitude ε β g d = 1 := by
  have hcard : (∅ : Finset (Fin N)).card = 0 := Finset.card_empty
  have hcontrib : ∀ order : Common.QuarticVertexOrder (∅ : Finset (Fin N)),
      d.orderedSimplexContribution ε β order = 1 := by
    intro order
    simp only [QuarticWickDiagram.orderedSimplexContribution]
    simp [QuarticWickDiagram.contractionIntegrand, Combinatorics.Pairing.evaluation,
      Combinatorics.Pairing.pairs, Combinatorics.Pairing.crossingCount]
  simp only [quarticWickDiagramAmplitude, QuarticWickDiagram.couplingWeight,
    Common.QuarticDiagram.vertexWeight, hcard, pow_zero, one_mul]
  have hcoupling : ∏ v : (↥(∅ : Finset (Fin N))), g (d.vertexLabel v) = 1 := by
    have : IsEmpty (↥(∅ : Finset (Fin N))) := Finset.isEmpty_coe_sort.2 rfl
    exact Finset.prod_of_isEmpty _
  rw [hcoupling, one_mul, Finset.sum_congr rfl (fun order _ => hcontrib order),
    Finset.sum_const, Finset.card_univ, Fintype.card_unique]
  simp

end Fermionic
end SecondQuantization
