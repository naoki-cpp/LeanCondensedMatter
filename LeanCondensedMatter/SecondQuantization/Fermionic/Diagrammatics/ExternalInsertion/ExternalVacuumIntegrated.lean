import LeanCondensedMatter.Analysis.OrderedSimplex.StrictAntiCongr
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.ExternalVacuumStandalone
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.ExternalInsertion.Integral

set_option linter.style.header false

/-!
# Integrated external-support/vacuum factorization on a fixed slot set

The standalone-support pointwise Dyson factorization holds whenever the inherited
vacuum times are strictly decreasing. An ambient strictly decreasing assignment
has this property automatically. Therefore the ordered-simplex integral of
the complete diagram equals the integral of the standalone-support and
vacuum product, without requiring equality on the measure-zero time diagonals.
-/

namespace SecondQuantization
namespace Fermionic

open Common
open Combinatorics

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-- For any external-support slot set, the integrated full Dyson diagram is
the ordered-simplex integral of its standalone external-support Dyson factor
times the ordered vacuum Dyson factor. This is the fixed-support analytic
bridge before reindexing all supports by binary slot shuffles. -/
theorem externalInsertionOfSlotSplit_dysonAmplitude_eq_integral_standalone_mul_vacuum
    (ε : Mode → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (g : QuarticVertexLabel Mode → ℂ)
    {E n : ℕ} (T : Finset (Fin n))
    (ext : ExternalInsertionDiagram (ExternalFieldLabel Mode)
      (QuarticVertexLabel Mode) E n T)
    (vac : QuarticDiagram (QuarticVertexLabel Mode) n
      ((Finset.univ : Finset (Fin n)) \ T))
    (externalTime : Fin (2 * E) → ℝ) :
    let S := (Finset.univ : Finset (Fin n)) \ T
    let order : QuarticVertexOrder S := (S.orderIsoOfFin rfl).toEquiv
    let f : Fin S.card → Fin n := fun i => (S.orderIsoOfFin rfl i).1
    let fT : Fin T.card → Fin n := fun i => (T.orderIsoOfFin rfl i).1
    let e : ↥T ≃ ↥(Finset.univ : Finset (Fin T.card)) :=
      (T.orderIsoOfFin rfl).toEquiv.symm.trans
        (Equiv.subtypeUnivEquiv
          (fun i : Fin T.card => Finset.mem_univ i)).symm
    let d : ExternalInsertionWickDiagram Mode E n :=
      ExternalInsertionDiagram.ofSlotSplit (Finset.subset_univ T) ext vac
    d.dysonAmplitude ε β g externalTime =
      intervalIntegral.orderedSimplexIntegral n β (fun σ =>
        ExternalInsertionWickDiagram.dysonFixedTimeAmplitude
          (ext.slotCongr e) ε β g externalTime (σ ∘ fT) *
        (((-1 : ℂ) ^ S.card * vac.vertexWeight g) *
          (vac.pairingInOrder order).evaluation
            ((vac.pairingInOrder order).weight Statistics.fermion)
            (flatVertexLegPairValue ε β
              (fun v => vac.vertexLabel (S.orderIsoOfFin rfl v)) (σ ∘ f)))) := by
  intro S order f fT e d
  rw [← d.orderedSimplexIntegral_dysonFixedTimeAmplitude ε β g externalTime]
  apply intervalIntegral.orderedSimplexIntegral_congr_of_strictAnti n β hβ
  intro σ hσ _
  have hanti : StrictAnti (σ ∘ f) := by
    intro a b hab
    exact hσ ((S.orderIsoOfFin rfl).strictMono hab)
  exact externalInsertionOfSlotSplit_dysonFixedTimeAmplitude_eq_standalone_mul_vacuum
    ε β g T ext vac externalTime σ hanti

end Fermionic
end SecondQuantization
