import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.InteractionPictureVertexProduct
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.CauchySeries

set_option linter.style.header false

/-!
# Interaction-picture quartic-vertex Dyson expansion

The interaction-picture perturbation expansion is expressed directly through
mixed-time-ordered products of full quartic interaction vertices and external
fermionic fields in the free Gibbs state. The local quartic operator products,
their fermionic ordering sign, and the time integrations agree with the
existing finite Wick-diagram Dyson coefficients.

The resulting formal series need not converge analytically, and removing
pure-vacuum components does not force different external insertions to lie in
the same connected component.
-/

namespace SecondQuantization
namespace Fermionic

open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- Order-n Dyson coefficient of full interaction-picture quartic
vertices inserted among a fixed family of external fermionic fields.

The Gibbs state is the normalized free density state; the Dyson (-1)^n
factor is distinct from the fermionic mixed-time ordering sign. -/
noncomputable def externalInsertionVertexDysonCoefficient {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) : ℂ :=
  intervalIntegral.orderedSimplexIntegral n β
    (fun σ => (-1 : ℂ) ^ n *
      ∑ q : Fin n → QuarticVertexLabel Mode,
        (∏ i : Fin n, g (q i)) *
          (freeGibbsDensityOperator ε β).expectation
            (Common.finiteHilbertOperatorAlgEquiv
              (externalInsertionMixedTimeOrderedVertexComp
                ε externalLabel externalTime q σ)))

/-- The free-Gibbs interaction-picture vertex Dyson coefficient equals the
integrated Wick-diagram coefficient at each finite perturbative order. -/
theorem externalInsertionVertexDysonCoefficient_eq_externalInsertionDysonCoefficient
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) (n : ℕ) :
    externalInsertionVertexDysonCoefficient
        ε β g externalLabel externalTime n =
      externalInsertionDysonCoefficient
        ε β g externalLabel externalTime n := by
  calc
    externalInsertionVertexDysonCoefficient ε β g externalLabel externalTime n =
        externalInsertionMixedAtomicDysonCoefficient
          ε β g externalLabel externalTime n := by
      unfold externalInsertionVertexDysonCoefficient
        externalInsertionMixedAtomicDysonCoefficient
      apply intervalIntegral.orderedSimplexIntegral_congr
      intro σ
      apply congrArg (fun z : ℂ => (-1 : ℂ) ^ n * z)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [externalInsertionMixedTimeOrderedVertexComp_eq_atomicProduct]
      simp only [freeGibbsDensityOperator_expectation_eq_finiteGibbsExpectation,
        Common.finiteGibbsExpectation_smul]
      ring
    _ = externalInsertionDysonCoefficient
          ε β g externalLabel externalTime n :=
      externalInsertionMixedAtomicDysonCoefficient_eq_externalInsertionDysonCoefficient
        ε β g externalLabel externalTime n

/-- Formal series of free-Gibbs interaction-picture vertex Dyson coefficients. -/
noncomputable def externalInsertionVertexDysonSeries {E : ℕ}
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) : PowerSeries ℂ :=
  PowerSeries.mk (externalInsertionVertexDysonCoefficient
    ε β g externalLabel externalTime)

/-- The interaction-picture vertex Dyson formal series is the already-proved
diagrammatic external-insertion series. -/
theorem externalInsertionVertexDysonSeries_eq_externalInsertionDysonSeries
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    externalInsertionVertexDysonSeries ε β g externalLabel externalTime =
      externalInsertionDysonSeries ε β g externalLabel externalTime := by
  ext n
  simp only [externalInsertionVertexDysonSeries, externalInsertionDysonSeries,
    PowerSeries.coeff_mk]
  exact externalInsertionVertexDysonCoefficient_eq_externalInsertionDysonCoefficient
    ε β g externalLabel externalTime n

/-- The interaction-picture vertex Dyson formal series contains precisely the
vacuum-free external contribution times the normalized vacuum partition
series. Externally supported but mutually disconnected components remain. -/
theorem externalInsertionVertexDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
    {E : ℕ} (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    (externalLabel : Fin (2 * E) → ExternalFieldLabel Mode)
    (externalTime : Fin (2 * E) → ℝ) :
    externalInsertionVertexDysonSeries ε β g externalLabel externalTime =
      vacuumFreeExternalInsertionDysonSeries ε β g externalLabel externalTime *
        PowerSeries.normalizeByConstantCoeff
          (dysonPartitionSeries ε β (quarticInteraction g)) := by
  rw [externalInsertionVertexDysonSeries_eq_externalInsertionDysonSeries]
  exact externalInsertionDysonSeries_eq_vacuumFree_mul_normalizedDysonPartitionSeries
    ε β hβ g externalLabel externalTime

end Fermionic
end SecondQuantization
