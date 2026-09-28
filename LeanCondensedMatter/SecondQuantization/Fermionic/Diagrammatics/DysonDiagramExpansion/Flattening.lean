import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg
import LeanCondensedMatter.SecondQuantization.Common.Interaction.Quartic.LocalLegExchange
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.ExchangeAlgebra
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.DysonDiagramExpansion.Core
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LegFamily
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Fermionic.Diagrammatics.Quartic.LocalLeg

set_option linter.style.header false

/-!
# Dyson diagram expansion: operator flattening
-/

namespace SecondQuantization
namespace Fermionic

open Combinatorics
open Common

variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]

/-! ## Flattening `Common.quarticVertexSequenceInteractionPicture` into a `4n`-atom `List.prod` -/

omit [Fintype Mode] in
/-- The ordered product of the flattened evolved quartic legs is exactly the Common
interaction-picture quartic-vertex sequence. The row-major `4n` list decomposition is owned by
`Common.listOfFn_orderedQuarticLegFamily_cons`; this theorem supplies only the fermionic
imaginary-time specialization. -/
theorem prod_ofFn_quarticLegOperatorForSequence_eq_quarticVertexSequenceInteractionPicture
    (ε : Mode → ℝ) :
    ∀ (n : ℕ) (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ),
      List.prod (List.ofFn (quarticLegOperatorForSequence ε q τ)) =
        Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate n q τ
  | 0, _, _ => by
      simp [quarticLegOperatorForSequence, List.ofFn, Module.End.one_eq_id]
  | n + 1, q, τ => by
      rw [Common.quarticVertexSequenceInteractionPicture_succ]
      change List.prod (List.ofFn (Common.orderedQuarticLegFamily
        (fun i : Fin (n + 1) => fun l : Fin 4 =>
          imaginaryTimeEvolve ε (τ i) (quarticLocalLegOperator (q i) l)))) = _
      have hfamily :
          (fun i : Fin (n + 1) => fun l : Fin 4 =>
            imaginaryTimeEvolve ε (τ i) (quarticLocalLegOperator (q i) l)) =
            Fin.cons
              (fun l : Fin 4 =>
                imaginaryTimeEvolve ε (τ 0) (quarticLocalLegOperator (q 0) l))
              (fun i : Fin n => fun l : Fin 4 =>
                imaginaryTimeEvolve ε (τ i.succ) (quarticLocalLegOperator (q i.succ) l)) := by
        funext i
        refine Fin.cases ?_ (fun i => ?_) i <;> rfl
      rw [hfamily, Common.listOfFn_orderedQuarticLegFamily_cons, List.prod_append]
      rw [show
          (List.ofFn (fun l : Fin 4 =>
            imaginaryTimeEvolve ε (τ 0) (quarticLocalLegOperator (q 0) l))).prod =
              interactionPicture ε (quarticVertexOperator (q 0)) (τ 0) by
        symm
        simpa [Common.interactionPicture, interactionPicture, quarticVertexOperator,
          imaginaryTimeEvolve, quarticLocalLegOperator] using
          (Common.heisenbergEvolve_quarticVertexOperator_eq_prod
            (fermionEnergy ε) create annihilate (q 0) (τ 0))]
      rw [show
          (List.ofFn (Common.orderedQuarticLegFamily
            (fun i : Fin n => fun l : Fin 4 =>
              imaginaryTimeEvolve ε (τ i.succ)
                (quarticLocalLegOperator (q i.succ) l)))).prod =
            Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate n
              (fun i => q i.succ) (fun i => τ i.succ) by
        change List.prod (List.ofFn
          (quarticLegOperatorForSequence ε (fun i => q i.succ) (fun i => τ i.succ))) =
            Common.quarticVertexSequenceInteractionPicture (fermionEnergy ε) create annihilate n
              (fun i => q i.succ) (fun i => τ i.succ)
        exact prod_ofFn_quarticLegOperatorForSequence_eq_quarticVertexSequenceInteractionPicture
          ε n (fun i => q i.succ) (fun i => τ i.succ)]
      simp only [Module.End.mul_eq_comp]

/-! ## The general theorem's zeta-commutator hypothesis, for the full evolved `4n`-leg family

The bare local-leg exchange coefficient and bracket theorem live in
`Common.Interaction.Quartic.LocalLegExchange`. -/

omit [Fintype Mode] in
/-- **The general theorem's `c i j` coefficient family**, for the evolved, flattened `4n`-leg
family — the product of both legs' `Complex.exp` eigenvalue-shift scalars and the Common bare
local-leg exchange coefficient. -/
noncomputable def flatVertexLegCommutatorCoeff {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p p' : Fin (2 * (2 * n))) : ℂ :=
  Complex.exp ((τ (flatVertexIndex n p) * quarticLegEnergyShiftForSequence ε q p : ℝ) : ℂ) *
    Complex.exp ((τ (flatVertexIndex n p') * quarticLegEnergyShiftForSequence ε q p' : ℝ) : ℂ) *
    Common.QuarticLocalLeg.exchangeCoeff Common.Statistics.fermion
      (Common.quarticLocalLeg (q (flatVertexIndex n p)) (flatLocalLeg n p))
      (Common.quarticLocalLeg (q (flatVertexIndex n p')) (flatLocalLeg n p'))

omit [Fintype Mode] in
/-- **The general theorem's zeta-commutator hypothesis, for two arbitrary evolved/flattened leg
positions** — pulls out both imaginary-time evolution scalars and uses the Common quartic local-leg
exchange theorem for the remaining bare operators. -/
theorem zetaCommutator_quarticLegOperatorForSequence {n : ℕ} (ε : Mode → ℝ)
    (q : Fin n → QuarticVertexLabel Mode) (τ : Fin n → ℝ) (p p' : Fin (2 * (2 * n))) :
    ScalarExchange.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (quarticLegOperatorForSequence ε q τ p) (quarticLegOperatorForSequence ε q τ p') =
      flatVertexLegCommutatorCoeff ε q τ p p' •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) := by
  rw [quarticLegOperatorForSequence_eq_smul, quarticLegOperatorForSequence_eq_smul,
    ScalarExchange.zetaCommutator_smul_smul]
  have hlocal := Common.QuarticLocalLeg.exchangeCommutator_operator
    (Mode := Mode) (Config := Occupation Mode) Common.Statistics.fermion
    (Common.quarticLocalLeg (q (flatVertexIndex n p)) (flatLocalLeg n p))
    (Common.quarticLocalLeg (q (flatVertexIndex n p')) (flatLocalLeg n p'))
  change
    ScalarExchange.zetaCommutator ((Common.Statistics.fermion.zetaInt : ℤ) : ℂ)
        (quarticLocalLegOperator (q (flatVertexIndex n p)) (flatLocalLeg n p))
        (quarticLocalLegOperator (q (flatVertexIndex n p')) (flatLocalLeg n p')) =
      Common.QuarticLocalLeg.exchangeCoeff Common.Statistics.fermion
          (Common.quarticLocalLeg (q (flatVertexIndex n p)) (flatLocalLeg n p))
          (Common.quarticLocalLeg (q (flatVertexIndex n p')) (flatLocalLeg n p')) •
        (LinearMap.id : OccupationFock Mode →ₗ[ℂ] OccupationFock Mode) at hlocal
  rw [hlocal, smul_smul, flatVertexLegCommutatorCoeff]

end Fermionic
end SecondQuantization
