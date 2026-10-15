import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Pairing
import LeanCondensedMatter.SecondQuantization.Fermionic.Perturbation.DysonPartitionSeries
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Ordered

set_option linter.style.header false

/-!
# Ordered quartic vacuum contributions

A vacuum diagram in fixed ordered coordinates consists of a quartic label sequence
and a pairing. Its Dyson integrand and the sum of its integrated contributions
use no external insertion data. The sum agrees with the normalized Dyson
partition coefficient and is shared by two-point and arbitrary-external fibers.
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- The Dyson-signed vacuum integrand written only in fixed ordered quartic data. -/
noncomputable def orderedVacuumDysonIntegrand
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) {k : ℕ}
    (x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k)
    (σ : Fin k → ℝ) : ℂ :=
  (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
    flatVertexLegPairingEvaluation ε β x.1 σ x.2

/-- Summing the fixed-order Dyson contribution over ordered vacuum data gives the normalized vacuum
Dyson coefficient.  This is the fixed-order vacuum theorem with the irrelevant ambient vertex set
removed entirely. -/
theorem sum_orderedVacuumDysonContribution_eq_normalizedDysonPartitionCoeff
    (ε : Mode → ℝ) (β : ℝ) (g : QuarticVertexLabel Mode → ℂ) (k : ℕ) :
    (∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
      (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
        intervalIntegral.orderedSimplexIntegral k β
          (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) =
      normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
  classical
  have hkey :=
    dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairingEvaluation
      ε β g (Finset.univ : Finset (Fin k))
  rw [Finset.card_univ, Fintype.card_fin] at hkey
  calc
    (∑ x : Common.OrderedQuarticDiagramData (QuarticVertexLabel Mode) k,
      (-1 : ℂ) ^ k * (∏ q : Fin k, g (x.1 q)) *
        intervalIntegral.orderedSimplexIntegral k β
          (fun σ => flatVertexLegPairingEvaluation ε β x.1 σ x.2)) =
        (-1 : ℂ) ^ k *
          ∑ q : Fin k → QuarticVertexLabel Mode,
            (∏ i, g (q i)) *
              ∑ pairing : Combinatorics.Pairing (2 * k),
                intervalIntegral.orderedSimplexIntegral k β
                  (fun σ => flatVertexLegPairingEvaluation ε β q σ pairing) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.mul_sum, Finset.mul_sum]
      simp only [mul_assoc]
    _ = normalizedDysonPartitionCoeff ε β (quarticInteraction g) k := by
      have hfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero k
      apply mul_left_cancel₀ hfac
      have hconst :
          PowerSeries.constantCoeff
            (Common.dysonTraceSeries (fermionEnergy ε) β (quarticInteraction g)) =
            freePartitionFunction ε β :=
        constantCoeff_dysonPartitionSeries ε β (quarticInteraction g)
      simpa [Common.dysonTraceVertexMoment, Common.normalizedDysonTraceCoeff,
        normalizedDysonPartitionCoeff, dysonPartitionCoeff, hconst,
        mul_assoc] using hkey.symm

end Fermionic
end SecondQuantization
