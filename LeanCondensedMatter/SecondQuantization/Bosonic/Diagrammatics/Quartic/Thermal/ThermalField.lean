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
  fun leg =>
    let vl := Common.orderedQuarticLegEquiv n leg
    quarticFreeThermalField (q vl.1) vl.2

/-- At a row-major block coordinate, the flattened thermal-field family recovers the
corresponding local leg of the selected quartic vertex. -/
private theorem FreeThermalField.operator_quarticFreeThermalFieldFamily_cast_mul_add {n : ℕ}
    (q : Fin n → QuarticVertexLabel Mode) (i : Fin n) (j : Fin 4)
    (h : 2 * (2 * n) = n * 4) :
    FreeThermalField.operator
        (quarticFreeThermalFieldFamily q
          (Fin.cast h.symm ⟨(i : ℕ) * 4 + (j : ℕ), by omega⟩)) =
      quarticLocalLegOperator (q i) j := by
  have hcoord :
      Common.orderedQuarticLegEquiv n
          (Fin.cast h.symm ⟨(i : ℕ) * 4 + (j : ℕ), by omega⟩) = (i, j) := by
    simpa [Common.orderedQuarticLegEquiv] using
      (Combinatorics.FiniteIndex.blockEquiv_cast_mul_add h i j)
  rw [quarticFreeThermalFieldFamily, hcoord,
    FreeThermalField.operator_quarticFreeThermalField]

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
  have hcard : 2 * (2 * (n + 1)) = (n + 1) * 4 := by ring
  have hcard' : 2 * (2 * n) = n * 4 := by ring
  have h2 : 2 * (2 * (n + 1)) = 4 + 2 * (2 * n) := by ring
  have hvertex :
      (List.ofFn (fun j : Fin 4 =>
        FreeThermalField.operator (quarticFreeThermalField q0 j))).prod =
        quarticVertexOperator q0 := by
    simp [FreeThermalField.operator_quarticFreeThermalField,
      quarticVertexOperator, quarticLocalLegOperator, Common.quarticLocalLegOperator,
      List.ofFn_succ, Module.End.mul_eq_comp]
  simp only [quarticFreeThermalOrderedProduct, FreeThermalField.orderedProduct, List.map_ofFn]
  rw [← hvertex, ← Module.End.mul_eq_comp, ← List.prod_append,
    List.ofFn_congr h2, ← List.ofFn_fin_append]
  refine congrArg List.prod
    (congrArg List.ofFn (funext (Fin.addCases (fun j => ?_) fun k => ?_)))
  · have e1 : Fin.cast h2.symm (Fin.castAdd (2 * (2 * n)) j) =
        Fin.cast hcard.symm ⟨((0 : Fin (n + 1)) : ℕ) * 4 + (j : ℕ), by omega⟩ := by
      apply Fin.ext
      simp
    change FreeThermalField.operator
        (quarticFreeThermalFieldFamily (Fin.cons q0 q)
          (Fin.cast h2.symm (Fin.castAdd _ j))) =
      Fin.append
        (fun j : Fin 4 => FreeThermalField.operator (quarticFreeThermalField q0 j))
        (fun k => FreeThermalField.operator (quarticFreeThermalFieldFamily q k))
        (Fin.castAdd _ j)
    rw [Fin.append_left, e1,
      FreeThermalField.operator_quarticFreeThermalFieldFamily_cast_mul_add
        (Fin.cons q0 q) 0 j hcard, Fin.cons_zero]
    exact (FreeThermalField.operator_quarticFreeThermalField q0 j).symm
  · have hk : k = Fin.cast hcard'.symm
        ⟨(Common.orderedQuarticLegEquiv n k).1 * 4 +
            (Common.orderedQuarticLegEquiv n k).2, by
          have := (Common.orderedQuarticLegEquiv n k).2.isLt
          omega⟩ :=
      Combinatorics.FiniteIndex.eq_cast_mul_add_blockEquiv hcard' k
    have e2 : Fin.cast h2.symm (Fin.natAdd 4 k) = Fin.cast hcard.symm
        ⟨((Common.orderedQuarticLegEquiv n k).1.succ : ℕ) * 4 +
            ((Common.orderedQuarticLegEquiv n k).2 : ℕ),
          by
            have := (Common.orderedQuarticLegEquiv n k).2.isLt
            omega⟩ := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_succ]
      have hkval : (k : ℕ) =
          (Common.orderedQuarticLegEquiv n k).1 * 4 +
            (Common.orderedQuarticLegEquiv n k).2 := by
        have := congrArg Fin.val hk
        simpa using this
      omega
    change FreeThermalField.operator
        (quarticFreeThermalFieldFamily (Fin.cons q0 q)
          (Fin.cast h2.symm (Fin.natAdd 4 k))) =
      Fin.append
        (fun j : Fin 4 => FreeThermalField.operator (quarticFreeThermalField q0 j))
        (fun k => FreeThermalField.operator (quarticFreeThermalFieldFamily q k))
        (Fin.natAdd 4 k)
    rw [Fin.append_right, e2,
      FreeThermalField.operator_quarticFreeThermalFieldFamily_cast_mul_add
        (Fin.cons q0 q) (Common.orderedQuarticLegEquiv n k).1.succ
          (Common.orderedQuarticLegEquiv n k).2 hcard]
    have hrest := FreeThermalField.operator_quarticFreeThermalFieldFamily_cast_mul_add q
      (Common.orderedQuarticLegEquiv n k).1
      (Common.orderedQuarticLegEquiv n k).2 hcard'
    rw [← hk] at hrest
    exact hrest.symm

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
