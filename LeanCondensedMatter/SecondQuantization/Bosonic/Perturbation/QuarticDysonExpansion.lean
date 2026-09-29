import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.Interaction
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.Perturbation.QuarticDysonExpansion

set_option linter.style.header false

/-!
# Quartic bosonic Dyson expansion

For a finitely supported bosonic quartic interaction, each vertex is an eigenoperator of the free
imaginary-time evolution. The statistics-independent ordered-simplex expansion is owned by
`SecondQuantization.Common.Perturbation.QuarticDysonExpansion`; this module supplies the bosonic
free-energy and ladder-evolution specialization.

The resulting operator identity is proved before any Gibbs expectation is taken, so it does not
require interchanging an infinite bosonic Gibbs sum with an interval integral.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

/-- The actual arbitrary-occupation-space Dyson coefficient of a finitely supported bosonic quartic
interaction is a finite sum over support-valued vertex-label sequences. Each summand is a static
bare operator product multiplied by its scalar ordered-simplex Dyson coefficient.

The ambient mode type need not be finite, and no infinite Gibbs sum/integral interchange is used. -/
theorem dysonCoeff_quarticInteractionOn_eq_sum
    (support : Finset (QuarticVertexLabel Mode))
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ∀ (n : ℕ) (t : ℝ),
      Common.dysonCoeff (freeEigenvalue ε) (quarticInteractionOn support g) n t =
        ∑ q : Fin n → ↥support,
          Common.quarticDysonSequenceCoeff ε g
              (fun i => (q i : QuarticVertexLabel Mode)) t •
            Common.quarticVertexSequenceOperator create annihilate
              (fun i => (q i : QuarticVertexLabel Mode)) := by
  intro n t
  simpa [quarticInteractionOn] using
    (Common.dysonCoeff_quarticInteractionOn_eq_sum
      (energy := freeEigenvalue ε) (ε := ε) (create := create) (annihilate := annihilate)
      support g
      (fun τ i => imaginaryTimeEvolve_create ε τ i)
      (fun τ i => imaginaryTimeEvolve_annihilate ε τ i)
      n t)

/-- On a finite mode type, the bosonic quartic Dyson coefficient is the direct specialization of
the Common all-label quartic Dyson expansion. -/
theorem dysonCoeff_quarticInteraction_eq_sum [Fintype Mode]
    (ε : Mode → ℝ) (g : QuarticVertexLabel Mode → ℂ) :
    ∀ (n : ℕ) (t : ℝ),
      Common.dysonCoeff (freeEigenvalue ε) (quarticInteraction g) n t =
        ∑ q : Fin n → QuarticVertexLabel Mode,
          Common.quarticDysonSequenceCoeff ε g q t •
            Common.quarticVertexSequenceOperator create annihilate q := by
  intro n t
  simpa [quarticInteraction] using
    (Common.dysonCoeff_quarticInteraction_eq_sum
      (energy := freeEigenvalue ε) (ε := ε) (create := create) (annihilate := annihilate)
      g
      (fun τ i => imaginaryTimeEvolve_create ε τ i)
      (fun τ i => imaginaryTimeEvolve_annihilate ε τ i)
      n t)

end
end Bosonic
end SecondQuantization
