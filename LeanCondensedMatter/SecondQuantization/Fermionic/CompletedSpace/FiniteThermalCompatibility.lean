import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Basic
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeBoltzmannCore
import LeanCondensedMatter.QuantumTheory.Gibbs.PurePoint

set_option linter.style.header false

/-!
# Finite-mode compatibility of the completed free Gibbs state

For finitely many fermionic modes, the completed occupation space and the finite Hilbert Fock
realization are canonically isometric by the statistics-independent compatibility equivalence in
`Common`. Both Gibbs states are finite specializations of the same generic pure-point construction
on the corresponding occupation bases, so that isometry intertwines them with the same pure-point
probabilities.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [Fintype Mode]

/-- Under the canonical finite-mode isometry, the two finite pure-point realizations of the free
Gibbs density operator are intertwined exactly. -/
theorem completedFiniteHilbertEquiv_intertwines_freeGibbsDensity
    (ε : Mode → ℝ) (β : ℝ) :
    (Common.completedFiniteHilbertContinuousEquiv
      (Config := Occupation Mode)).toContinuousLinearMap.comp
        (finitePurePointGibbsDensityOperator completedOccupationHilbertBasis
          (fermionEnergy ε) β).op =
      (finitePurePointGibbsDensityOperator
        (Common.finiteHilbertBasis (Config := Occupation Mode)) (fermionEnergy ε) β).op.comp
        (Common.completedFiniteHilbertContinuousEquiv
          (Config := Occupation Mode)).toContinuousLinearMap := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  simp only [ContinuousLinearMap.comp_apply]
  change
    (Common.completedFiniteHilbertContinuousEquiv (Config := Occupation Mode))
        ((finitePurePointGibbsDensityOperator completedOccupationHilbertBasis
          (fermionEnergy ε) β).op (completedBasisState n)) =
      (finitePurePointGibbsDensityOperator
        (Common.finiteHilbertBasis (Config := Occupation Mode)) (fermionEnergy ε) β).op
        (Common.completedFiniteHilbertContinuousEquiv (Config := Occupation Mode)
          (completedBasisState n))
  rw [← completedOccupationHilbertBasis_apply (Mode := Mode) n,
    finitePurePointGibbsDensityOperator_apply_basis, map_smul,
    completedOccupationHilbertBasis_apply]
  change (purePointGibbsProbability (fermionEnergy ε) β n : ℂ) •
      Common.completedFiniteHilbertEquiv (Config := Occupation Mode) (completedBasisState n) =
    (finitePurePointGibbsDensityOperator
      (Common.finiteHilbertBasis (Config := Occupation Mode)) (fermionEnergy ε) β).op
      (Common.completedFiniteHilbertEquiv (Config := Occupation Mode) (completedBasisState n))
  rw [Common.completedFiniteHilbertEquiv_basisState,
    ← Common.finiteHilbertBasis_apply (Config := Occupation Mode) n,
    finitePurePointGibbsDensityOperator_apply_basis,
    Common.finiteHilbertBasis_apply]

end
end Fermionic
end SecondQuantization
