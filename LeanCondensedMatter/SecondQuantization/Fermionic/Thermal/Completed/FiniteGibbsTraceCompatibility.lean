import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.Completed.Gibbs
import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.Thermal.FreeGibbsDensityOperator
import LeanCondensedMatter.SecondQuantization.Common.CompletedSpace.FiniteCompatibility
import LeanCondensedMatter.SecondQuantization.Common.Thermal.FiniteGibbsCoordinate

set_option linter.style.header false

/-!
# Finite-mode compatibility of completed fermionic grand-canonical Gibbs states

For finite fermionic mode types, the completed occupation Hilbert space is
canonically isometric to the finite Hilbert occupation realization. The common
grand-canonical density state on the completed side is intertwined with the
finite Gibbs density state evaluated at shifted one-mode energies `ε - μ`.

The finite density-state expectation then equals the common summable diagonal
trace ratio from the algebraic Fock theory. This does not identify arbitrary
bounded completed operators with algebraic-Fock endomorphisms in infinite modes.
-/

namespace SecondQuantization
namespace Fermionic

open QuantumTheory

noncomputable section

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

omit [LinearOrder Mode] in
/-- At finite mode number, the completed grand-canonical density operator and
the finite free-fermion Gibbs density operator at effective energy `ε - μ`
are intertwined by the canonical completed-to-finite Hilbert equivalence. -/
theorem completedGrandCanonicalGibbs_intertwines_finite
    (ε : Mode → ℝ) (β μ : ℝ) :
    (Common.completedFiniteHilbertEquiv (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode) ε β μ
        (eigenbasisGibbsSummable_of_finite
          (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)).op =
      (freeGibbsDensityOperator (fun i => ε i - μ) β).op.comp
        (Common.completedFiniteHilbertEquiv (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap := by
  have hE :
      Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ =
        fermionEnergy (fun i => ε i - μ) := by
    funext n
    exact Common.grandCanonicalEnergy_eq_shifted ε μ n
  have hbasis : ∀ n : Occupation Mode,
      (Common.completedFiniteHilbertEquiv
        (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap
          (Common.completedHilbertBasis (Config := Occupation Mode) n) =
        Common.finiteHilbertBasis (Config := Occupation Mode) n := by
    intro n
    simpa only [Common.completedHilbertBasis_apply, Common.finiteHilbertBasis_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      (Common.completedFiniteHilbertEquiv_basisState (Config := Occupation Mode) n)
  have htransport :=
    eigenbasisGibbsDensityOperator_intertwines
      (Common.completedHilbertBasis (Config := Occupation Mode))
      (Common.finiteHilbertBasis (Config := Occupation Mode))
      (fermionEnergy (fun i => ε i - μ)) β
      (eigenbasisGibbsSummable_of_finite
        (fermionEnergy (fun i => ε i - μ)) β)
      (Common.completedFiniteHilbertEquiv
        (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap
      hbasis
  simpa [Common.grandCanonicalGibbsDensityOperator,
    freeGibbsDensityOperator, hE] using htransport

omit [LinearOrder Mode] in
/-- A bounded completed operator extending an algebraic Fock endomorphism is intertwined
with its canonical finite-Hilbert realization. This is the reusable operator-level
bridge, with no Gibbs-state assumption. -/
private theorem completedFiniteHilbertIntertwines_of_algebraicCore
    (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
    (T : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)
    (hcore : T.toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp A) :
    (Common.completedFiniteHilbertEquiv
      (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap.comp T =
      (Common.finiteHilbertOperatorAlgEquiv A).comp
        (Common.completedFiniteHilbertEquiv
          (Config := Occupation Mode)).toContinuousLinearEquiv.toContinuousLinearMap := by
  apply Common.continuousLinearMap_ext_completedBasis
  intro n
  let e := Common.completedFiniteHilbertEquiv (Config := Occupation Mode)
  have hcore_n :
      T (Common.algebraicToCompleted (Common.basisState n)) =
        Common.algebraicToCompleted (A (Common.basisState n)) := by
    have h := congrArg
      (fun f : OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode =>
        f (Common.basisState n)) hcore
    simpa [algebraicToCompleted, ContinuousLinearMap.toLinearMap] using h
  change e (T (Common.completedBasisState n)) =
    Common.finiteHilbertOperatorAlgEquiv A (e (Common.completedBasisState n))
  calc
    e (T (Common.completedBasisState n)) =
        e (Common.algebraicToCompleted (A (Common.basisState n))) := by
      rw [← Common.algebraicToCompleted_basisState (Config := Occupation Mode)]
      exact congrArg e hcore_n
    _ = Common.finiteHilbertFockEquiv (A (Common.basisState n)) :=
      Common.completedFiniteHilbertEquiv_algebraicToCompleted _
    _ = Common.finiteHilbertOperatorAlgEquiv A
        (Common.finiteHilbertBasisState n) :=
      (Common.finiteHilbertOperator_basisState A n).symm
    _ = Common.finiteHilbertOperatorAlgEquiv A
        (e (Common.completedBasisState n)) := by
      rw [Common.completedFiniteHilbertEquiv_basisState]

omit [LinearOrder Mode] in
/-- Transport a finite free-fermion expectation to the completed normal grand-canonical
Gibbs state whenever the bounded completed operator extends the algebraic observable.
The chemical potential is explicit, and finite modes enter solely through this bridge. -/
theorem freeGibbsExpectation_eq_completed_of_algebraicCore
    (ε : Mode → ℝ) (β μ : ℝ)
    (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode)
    (T : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)
    (hcore : T.toLinearMap.comp algebraicToCompleted =
      algebraicToCompleted.comp A) :
    (freeGibbsDensityOperator (fun i => ε i - μ) β).expectation
      (Common.finiteHilbertOperatorAlgEquiv A) =
    (Common.grandCanonicalGibbsDensityOperator (Config := Occupation Mode)
      ε β μ (eigenbasisGibbsSummable_of_finite
        (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) β)).expectation T := by
  let e := Common.completedFiniteHilbertEquiv (Config := Occupation Mode)
  let F := e.toContinuousLinearEquiv.toContinuousLinearMap
  let G := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hinter := completedFiniteHilbertIntertwines_of_algebraicCore A T hcore
  have hconj :
      G.comp ((Common.finiteHilbertOperatorAlgEquiv A).comp F) = T := by
    apply ContinuousLinearMap.ext
    intro ψ
    have hψ := congrArg (fun L : CompletedFockSpace Mode →L[ℂ]
        Common.FiniteHilbertFock (Occupation Mode) => L ψ) hinter
    change F (T ψ) = Common.finiteHilbertOperatorAlgEquiv A (F ψ) at hψ
    change G (Common.finiteHilbertOperatorAlgEquiv A (F ψ)) = T ψ
    calc
      G (Common.finiteHilbertOperatorAlgEquiv A (F ψ)) = G (F (T ψ)) :=
        congrArg G hψ.symm
      _ = T ψ := by
        simpa only [F, G, ContinuousLinearEquiv.coe_coe,
          LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
          e.symm_apply_apply (T ψ)
  let ξ : Mode → ℝ := fun i => ε i - μ
  have henergy : Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ =
      fermionEnergy ξ := by
    funext n
    exact Common.grandCanonicalEnergy_eq_shifted ε μ n
  have hbasis : ∀ n : Occupation Mode,
      e (Common.completedHilbertBasis (Config := Occupation Mode) n) =
        Common.finiteHilbertBasis (Config := Occupation Mode) n := by
    intro n
    simpa only [Common.completedHilbertBasis_apply, Common.finiteHilbertBasis_apply] using
      (Common.completedFiniteHilbertEquiv_basisState (Config := Occupation Mode) n)
  have htransport :=
    eigenbasisGibbsDensityOperator_expectation_transport
      (Common.completedHilbertBasis (Config := Occupation Mode))
      (Common.finiteHilbertBasis (Config := Occupation Mode))
      (fermionEnergy ξ) β
      (eigenbasisGibbsSummable_of_finite (fermionEnergy ξ) β) e hbasis
      (Common.finiteHilbertOperatorAlgEquiv A)
  rw [hconj] at htransport
  simpa only [freeGibbsDensityOperator, Common.grandCanonicalGibbsDensityOperator,
    henergy, ξ] using htransport

omit [LinearOrder Mode] in
/-- The finite fermionic grand-canonical density-state expectation is the
summable diagonal trace ratio of #4074, with shifted one-mode energies.
Summability on the algebraic side is automatic only because the occupation
configuration type is finite. -/
theorem finiteGrandCanonicalGibbsExpectation_eq_diagonalTraceRatio
    (ε : Mode → ℝ) (β μ : ℝ)
    (A : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) :
    (freeGibbsDensityOperator (fun i => ε i - μ) β).expectation
        (Common.finiteHilbertOperatorAlgEquiv A) =
      Common.summableDiagonalTraceRatioLinear
        (Common.diagonalEvolution
          (Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ) (-β))
        ⟨A, Summable.of_finite⟩ := by
  have hE :
      Common.grandCanonicalEnergy (Config := Occupation Mode) ε μ =
        fermionEnergy (fun i => ε i - μ) := by
    funext n
    exact Common.grandCanonicalEnergy_eq_shifted ε μ n
  rw [hE]
  exact freeGibbsDensityOperator_expectation_eq_summableDiagonalTraceRatioLinear
    (fun i => ε i - μ) β A

end
end Fermionic
end SecondQuantization
