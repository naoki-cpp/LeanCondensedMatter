import LeanCondensedMatter.SecondQuantization.Bosonic.Diagrammatics.Quartic.LocalLeg
import LeanCondensedMatter.SecondQuantization.Bosonic.ImaginaryTime.ImaginaryTimeEvolution
import LeanCondensedMatter.SecondQuantization.Common.ImaginaryTime.Quartic
import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.FreeExpectationRecursion
import LeanCondensedMatter.SecondQuantization.Common.Diagrammatics.Quartic.Core.Leg

set_option linter.style.header false

/-!
# Free-boson thermal fields for quartic vertex legs

This module connects the bosonic quartic diagrammatic leg convention to the free thermal-field
representation.  A finite list of quartic vertices is flattened to `4 n = 2 (2 n)` local thermal
fields using the Common quartic-leg equivalence, and their ordered algebraic product is exposed for
downstream thermal expectations.

The concrete Gibbs/Wick theorem is owned by the bosonic thermal layer and is consumed directly at
the diagram-amplitude boundary rather than being wrapped here.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

/-- Interpret one bosonic quartic local leg as the corresponding free thermal field label. -/
def quarticFreeThermalField (q : QuarticVertexLabel Mode) (l : Fin 4) : FreeThermalField Mode :=
  match Common.quarticLocalLeg q l with
  | .create i => .create i
  | .annihilate i => .annihilate i

/-- The thermal-field realization agrees with the existing quartic local-leg operator. -/
theorem FreeThermalField.operator_quarticFreeThermalField
    (q : QuarticVertexLabel Mode) (l : Fin 4) :
    FreeThermalField.operator (quarticFreeThermalField q l) = quarticLocalLegOperator q l := by
  cases h : Common.quarticLocalLeg q l <;>
    simp [quarticFreeThermalField, quarticLocalLegOperator, Common.quarticLocalLegOperator,
      FreeThermalField.operator, h]

/-- The interaction-picture bosonic quartic vertex is the ordered product of the evolved
operators represented by its four free-thermal-field labels. This is the bosonic thermal
specialization of the statistics-independent Common quartic operator-product identity. -/
theorem interactionPicture_quarticVertexOperator_eq_prod_quarticFreeThermalField
    (ε : Mode → ℝ) (q : QuarticVertexLabel Mode) (τ : ℝ) :
    interactionPicture ε (quarticVertexOperator q) τ =
      (List.ofFn (fun l : Fin 4 =>
        imaginaryTimeEvolve ε τ
          (FreeThermalField.operator (quarticFreeThermalField q l)))).prod := by
  change Common.interactionPicture (freeEigenvalue ε)
      (Common.quarticVertexOperator create annihilate q) τ = _
  rw [show Common.interactionPicture (freeEigenvalue ε)
      (Common.quarticVertexOperator create annihilate q) τ =
      Common.heisenbergEvolve (freeEigenvalue ε) τ
        (Common.quarticVertexOperator create annihilate q) by rfl]
  rw [Common.heisenbergEvolve_quarticVertexOperator_eq_prod]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext l
  rw [FreeThermalField.operator_quarticFreeThermalField]
  rfl

/-- Flatten `n` ordered quartic vertices into their `4 n` free thermal field labels. -/
noncomputable def quarticFreeThermalFieldFamily {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) : Fin (2 * (2 * n)) → FreeThermalField Mode :=
  Common.orderedQuarticLegFamily fun i l => quarticFreeThermalField (q i) l

/-- Ordered algebraic product of all local legs of a finite list of quartic vertices. -/
noncomputable def quarticFreeThermalOrderedProduct {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) : FockSpace Mode →ₗ[ℂ] FockSpace Mode :=
  FreeThermalField.orderedProduct (List.ofFn (quarticFreeThermalFieldFamily q))

/-- Prepending one quartic vertex prepends its four thermal-field operators to the flattened
ordered product. -/
@[simp]
theorem quarticFreeThermalOrderedProduct_cons {n : ℕ}
    (q0 : QuarticVertexLabel Mode) (q : Fin n → QuarticVertexLabel Mode) :
    quarticFreeThermalOrderedProduct (Fin.cons q0 q) =
      (quarticVertexOperator q0).comp (quarticFreeThermalOrderedProduct q) := by
  rw [quarticFreeThermalOrderedProduct, quarticFreeThermalFieldFamily]
  have hfamily :
      (fun i : Fin (n + 1) => fun l : Fin 4 =>
        quarticFreeThermalField
          ((Fin.cons q0 q : Fin (n + 1) → QuarticVertexLabel Mode) i) l) =
        (Fin.cons (fun l : Fin 4 => quarticFreeThermalField q0 l)
          (fun i : Fin n => fun l : Fin 4 => quarticFreeThermalField (q i) l) :
          Fin (n + 1) → Fin 4 → FreeThermalField Mode) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> rfl
  rw [hfamily, Common.listOfFn_orderedQuarticLegFamily_cons]
  simp [quarticFreeThermalOrderedProduct, quarticFreeThermalFieldFamily,
    FreeThermalField.orderedProduct, List.map_ofFn,
    FreeThermalField.operator_quarticFreeThermalField,
    quarticVertexOperator, Common.quarticVertexOperator, quarticLocalLegOperator,
    Common.quarticLocalLegOperator, List.ofFn_succ, Module.End.mul_eq_comp,
    LinearMap.comp_assoc]

/-- The flattened bosonic free-thermal-field product is exactly the Common bare quartic
vertex-sequence operator. This is the operator bridge from the quartic Dyson expansion to the
bosonic Gibbs/Wick layer. -/
theorem quarticFreeThermalOrderedProduct_eq_quarticVertexSequenceOperator {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) :
    quarticFreeThermalOrderedProduct q =
      Common.quarticVertexSequenceOperator create annihilate q := by
  induction n with
  | zero =>
      simp [quarticFreeThermalOrderedProduct, FreeThermalField.orderedProduct,
        Common.quarticVertexSequenceOperator, Module.End.one_eq_id]
  | succ n ih =>
      rw [← Fin.cons_self_tail q, quarticFreeThermalOrderedProduct_cons,
        Common.quarticVertexSequenceOperator_cons, ih]
      rfl

end
end Bosonic
end SecondQuantization
