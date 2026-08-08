import LeanCondensedMatter.SecondQuantization.Bosonic.Thermal.BlochDeDominicis.OperatorPeel
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option linter.style.header false
set_option linter.unusedFintypeInType false

/-!
# Free-boson Gibbs KMS rotation

For a single bosonic ladder operator, diagonal `tsumTrace` cyclicity can be proved directly on the
infinite occupation basis: creation gives a bijection from all occupations to the subtype with a
positive occupation in the chosen mode, while the complementary zero-occupation diagonal terms
vanish. No finite occupation-basis shortcut and no blanket trace-class assertion is used.

Combining this reindexing with the algebraic relation moving a ladder operator through
`e^{-βH₀}` gives the free-Gibbs KMS rotation needed by the multi-point Bloch–de Dominicis
first-pair recurrence.
-/

namespace SecondQuantization
namespace Bosonic

open Common

noncomputable section

variable {Mode : Type*}

/-- File-local classical decidable equality for occupation reindexing. -/
local instance instDecidableEqFreeKMSRotation : DecidableEq Mode := Classical.decEq Mode

/-- Occupations with a particle available in mode `i`. -/
private def positiveOccupationSet (i : Mode) : Set (Occupation Mode) :=
  {n | n i ≠ 0}

/-- Adding one particle in mode `i` identifies all occupations with the positive-`i` subtype. -/
private noncomputable def createOccupationEquivPositive (i : Mode) :
    Occupation Mode ≃ positiveOccupationSet i where
  toFun n := ⟨createOccupation i n, by simp [positiveOccupationSet]⟩
  invFun n := removeOccupation i n.1
  left_inv n := removeOccupation_createOccupation i n
  right_inv n := by
    apply Subtype.ext
    exact createOccupation_removeOccupation_of_pos n.2

/-- Coordinate action of annihilation on an arbitrary algebraic-Fock vector. -/
theorem annihilate_apply_coord (i : Mode) (x : FockSpace Mode) (n : Occupation Mode) :
    annihilate i x n =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) * x (createOccupation i n) := by
  let evalN : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply n
  let evalC : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply (createOccupation i n)
  have hmap : evalN.comp (annihilate i) =
      (Real.sqrt (n i + 1 : ℝ) : ℂ) • evalC := by
    apply Finsupp.lhom_ext
    intro a b
    have hb : (Finsupp.single a b : FockSpace Mode) = b • basisState a :=
      (Finsupp.smul_single_one a b).symm
    rw [hb, LinearMap.comp_apply, map_smul, LinearMap.smul_apply]
    by_cases ha : a i = 0
    · rw [annihilate_basisState_of_zero ha]
      have hne : a ≠ createOccupation i n := by
        intro h
        have hi := congrArg (fun m : Occupation Mode => m i) h
        rw [ha, createOccupation_apply_same] at hi
        omega
      simp [evalN, evalC, basisState, Common.basisState, hne]
    · rw [annihilate_basisState_of_pos ha]
      by_cases hrem : removeOccupation i a = n
      · have hac : a = createOccupation i n := by
          calc
            a = createOccupation i (removeOccupation i a) :=
              (createOccupation_removeOccupation_of_pos ha).symm
            _ = createOccupation i n := by rw [hrem]
        subst a
        simp only [createOccupation_apply_same, Nat.cast_add, Nat.cast_one,
          Complex.coe_smul, map_smul, LinearMap.map_smul_of_tower,
          Complex.real_smul, smul_eq_mul]
        exact mul_comm _ _
      · have hne : a ≠ createOccupation i n := by
          intro h
          apply hrem
          rw [h, removeOccupation_createOccupation]
        simp [evalN, evalC, basisState, Common.basisState, hrem, hne]
  have hx := congrArg (fun L => L x) hmap
  simpa only [evalN, evalC, LinearMap.comp_apply, LinearMap.smul_apply,
    Finsupp.lapply_apply, smul_eq_mul] using hx

/-- Creation has zero coordinate on a zero-occupation target. -/
theorem create_apply_coord_of_zero (i : Mode) (x : FockSpace Mode) (n : Occupation Mode)
    (hi : n i = 0) : create i x n = 0 := by
  let evalN : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply n
  have hmap : evalN.comp (create i) = 0 := by
    apply Finsupp.lhom_ext
    intro a b
    have hb : (Finsupp.single a b : FockSpace Mode) = b • basisState a :=
      (Finsupp.smul_single_one a b).symm
    rw [hb, LinearMap.comp_apply, map_smul, create_basisState_eq]
    have hne : createOccupation i a ≠ n := by
      intro h
      have hcoord := congrArg (fun m : Occupation Mode => m i) h
      rw [createOccupation_apply_same, hi] at hcoord
      omega
    simp [evalN, basisState, Common.basisState, hne]
  have hx := congrArg (fun L => L x) hmap
  simpa only [evalN, LinearMap.comp_apply, Finsupp.lapply_apply, LinearMap.zero_apply] using hx

/-- Coordinate action of creation on a positive-occupation target. -/
theorem create_apply_coord_of_pos (i : Mode) (x : FockSpace Mode) (n : Occupation Mode)
    (hi : n i ≠ 0) :
    create i x n =
      (Real.sqrt (n i : ℝ) : ℂ) * x (removeOccupation i n) := by
  let evalN : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply n
  let evalR : FockSpace Mode →ₗ[ℂ] ℂ := Finsupp.lapply (removeOccupation i n)
  have hmap : evalN.comp (create i) =
      (Real.sqrt (n i : ℝ) : ℂ) • evalR := by
    apply Finsupp.lhom_ext
    intro a b
    have hb : (Finsupp.single a b : FockSpace Mode) = b • basisState a :=
      (Finsupp.smul_single_one a b).symm
    rw [hb, LinearMap.comp_apply, map_smul, create_basisState_eq,
      LinearMap.smul_apply]
    by_cases hca : createOccupation i a = n
    · have ha : a = removeOccupation i n := by
        calc
          a = removeOccupation i (createOccupation i a) :=
            (removeOccupation_createOccupation i a).symm
          _ = removeOccupation i n := by rw [hca]
      subst a
      have hni : 1 ≤ n i := Nat.one_le_iff_ne_zero.mpr hi
      have hcast : ((n i - 1 : ℕ) : ℝ) + 1 = (n i : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hni
      simp only [removeOccupation_apply_same, Complex.coe_smul, map_smul,
        LinearMap.map_smul_of_tower, Complex.real_smul, smul_eq_mul]
      rw [hcast]
      exact mul_comm _ _
    · have hane : a ≠ removeOccupation i n := by
        intro h
        apply hca
        rw [h, createOccupation_removeOccupation_of_pos hi]
      simp [evalN, evalR, basisState, Common.basisState, hca, hane]
  have hx := congrArg (fun L => L x) hmap
  simpa only [evalN, evalR, LinearMap.comp_apply, LinearMap.smul_apply,
    Finsupp.lapply_apply, smul_eq_mul] using hx

/-- Diagonal `tsumTrace` cyclicity for one annihilation operator, proved by occupation reindexing. -/
theorem tsumTrace_annihilate_comp (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.tsumTrace ((annihilate i).comp A) =
      Common.tsumTrace (A.comp (annihilate i)) := by
  let f : Occupation Mode → ℂ := fun n =>
    Common.matrixCoeff (A.comp (annihilate i)) n n
  have hpoint : ∀ n : Occupation Mode,
      Common.matrixCoeff ((annihilate i).comp A) n n = f (createOccupation i n) := by
    intro n
    unfold f Common.matrixCoeff
    change annihilate i (A (basisState n)) n =
      (A (annihilate i (basisState (createOccupation i n)))) (createOccupation i n)
    rw [annihilate_apply_coord, annihilate_basisState_of_pos]
    · rw [removeOccupation_createOccupation, createOccupation_apply_same]
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul,
        Nat.cast_add, Nat.cast_one]
    · simp [createOccupation_apply_same]
  have hsupport : Function.support f ⊆ positiveOccupationSet i := by
    intro n hn
    show n i ≠ 0
    intro hi
    apply hn
    unfold f Common.matrixCoeff
    change (A (annihilate i (basisState n))) n = 0
    rw [annihilate_basisState_of_zero hi, map_zero]
    rfl
  unfold Common.tsumTrace
  calc
    (∑' n, Common.matrixCoeff ((annihilate i).comp A) n n) =
        ∑' n, f (createOccupation i n) := tsum_congr hpoint
    _ = ∑' p : positiveOccupationSet i, f p.1 :=
      (createOccupationEquivPositive i).tsum_eq (fun p => f p.1)
    _ = ∑' n, f n := tsum_subtype_eq_of_support_subset hsupport
    _ = ∑' n, Common.matrixCoeff (A.comp (annihilate i)) n n := rfl

/-- Diagonal `tsumTrace` cyclicity for one creation operator, proved by occupation reindexing. -/
theorem tsumTrace_create_comp (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.tsumTrace ((create i).comp A) =
      Common.tsumTrace (A.comp (create i)) := by
  let f : Occupation Mode → ℂ := fun n =>
    Common.matrixCoeff ((create i).comp A) n n
  have hpoint : ∀ n : Occupation Mode,
      Common.matrixCoeff (A.comp (create i)) n n = f (createOccupation i n) := by
    intro n
    unfold f Common.matrixCoeff
    change (A (create i (basisState n))) n =
      create i (A (basisState (createOccupation i n))) (createOccupation i n)
    rw [create_basisState_eq, map_smul, Finsupp.smul_apply,
      create_apply_coord_of_pos]
    · rw [removeOccupation_createOccupation, createOccupation_apply_same]
      simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
    · simp [createOccupation_apply_same]
  have hsupport : Function.support f ⊆ positiveOccupationSet i := by
    intro n hn
    show n i ≠ 0
    intro hi
    apply hn
    unfold f Common.matrixCoeff
    change create i (A (basisState n)) n = 0
    exact create_apply_coord_of_zero i (A (basisState n)) n hi
  unfold Common.tsumTrace
  calc
    (∑' n, Common.matrixCoeff ((create i).comp A) n n) = ∑' n, f n := rfl
    _ = ∑' p : positiveOccupationSet i, f p.1 :=
      (tsum_subtype_eq_of_support_subset hsupport).symm
    _ = ∑' n, f (createOccupation i n) :=
      ((createOccupationEquivPositive i).tsum_eq (fun p => f p.1)).symm
    _ = ∑' n, Common.matrixCoeff (A.comp (create i)) n n :=
      tsum_congr fun n => (hpoint n).symm

/-- Unnormalized KMS rotation of an annihilation operator through the free Gibbs weight. -/
theorem freeGibbsTsum_annihilate_rotate (ε : Mode → ℝ) (β : ℝ) (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.tsumTrace
        ((imaginaryTimeEvolveFree ε (-β)).comp ((annihilate i).comp A)) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) *
        Common.tsumTrace
          ((imaginaryTimeEvolveFree ε (-β)).comp (A.comp (annihilate i))) := by
  let D := imaginaryTimeEvolveFree ε (-β)
  let q : ℂ := Complex.exp ((β : ℂ) * (ε i : ℂ))
  have hmove : D.comp (annihilate i) = q • ((annihilate i).comp D) := by
    dsimp [D, q]
    have h := imaginaryTimeEvolveFree_comp_annihilate ε (-β) i
    have hexp : -((-β : ℝ) : ℂ) * (ε i : ℂ) = (β : ℂ) * (ε i : ℂ) := by
      push_cast
      ring
    rwa [hexp] at h
  calc
    Common.tsumTrace (D.comp ((annihilate i).comp A)) =
        Common.tsumTrace ((D.comp (annihilate i)).comp A) := by
      rw [LinearMap.comp_assoc]
    _ = Common.tsumTrace ((q • ((annihilate i).comp D)).comp A) := by rw [hmove]
    _ = Common.tsumTrace (q • (((annihilate i).comp D).comp A)) := by
      rw [LinearMap.smul_comp]
    _ = q * Common.tsumTrace (((annihilate i).comp D).comp A) :=
      Common.tsumTrace_smul q (((annihilate i).comp D).comp A)
    _ = q * Common.tsumTrace ((annihilate i).comp (D.comp A)) := by
      rw [LinearMap.comp_assoc]
    _ = q * Common.tsumTrace ((D.comp A).comp (annihilate i)) := by
      rw [tsumTrace_annihilate_comp]
    _ = q * Common.tsumTrace (D.comp (A.comp (annihilate i))) := by
      rw [LinearMap.comp_assoc]

/-- Unnormalized KMS rotation of a creation operator through the free Gibbs weight. -/
theorem freeGibbsTsum_create_rotate (ε : Mode → ℝ) (β : ℝ) (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    Common.tsumTrace
        ((imaginaryTimeEvolveFree ε (-β)).comp ((create i).comp A)) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
        Common.tsumTrace
          ((imaginaryTimeEvolveFree ε (-β)).comp (A.comp (create i))) := by
  let D := imaginaryTimeEvolveFree ε (-β)
  let q : ℂ := Complex.exp (-(β : ℂ) * (ε i : ℂ))
  have hmove : D.comp (create i) = q • ((create i).comp D) := by
    dsimp [D, q]
    have h := imaginaryTimeEvolveFree_comp_create ε (-β) i
    have hexp : (((-β : ℝ) : ℂ) * (ε i : ℂ)) = -(β : ℂ) * (ε i : ℂ) := by
      push_cast
      ring
    rwa [hexp] at h
  calc
    Common.tsumTrace (D.comp ((create i).comp A)) =
        Common.tsumTrace ((D.comp (create i)).comp A) := by
      rw [LinearMap.comp_assoc]
    _ = Common.tsumTrace ((q • ((create i).comp D)).comp A) := by rw [hmove]
    _ = Common.tsumTrace (q • (((create i).comp D).comp A)) := by
      rw [LinearMap.smul_comp]
    _ = q * Common.tsumTrace (((create i).comp D).comp A) :=
      Common.tsumTrace_smul q (((create i).comp D).comp A)
    _ = q * Common.tsumTrace ((create i).comp (D.comp A)) := by
      rw [LinearMap.comp_assoc]
    _ = q * Common.tsumTrace ((D.comp A).comp (create i)) := by
      rw [tsumTrace_create_comp]
    _ = q * Common.tsumTrace (D.comp (A.comp (create i))) := by
      rw [LinearMap.comp_assoc]

/-- Normalized free-Gibbs KMS rotation for annihilation. -/
theorem freeGibbsExpectation_annihilate_rotate (ε : Mode → ℝ) (β : ℝ) (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β ((annihilate i).comp A) =
      Complex.exp ((β : ℂ) * (ε i : ℂ)) *
        freeGibbsExpectation ε β (A.comp (annihilate i)) := by
  unfold freeGibbsExpectation
  rw [freeGibbsTsum_annihilate_rotate, mul_div_assoc]

/-- Normalized free-Gibbs KMS rotation for creation. -/
theorem freeGibbsExpectation_create_rotate (ε : Mode → ℝ) (β : ℝ) (i : Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β ((create i).comp A) =
      Complex.exp (-(β : ℂ) * (ε i : ℂ)) *
        freeGibbsExpectation ε β (A.comp (create i)) := by
  unfold freeGibbsExpectation
  rw [freeGibbsTsum_create_rotate, mul_div_assoc]

/-- The KMS factor of a free thermal field. -/
noncomputable def FreeThermalField.kmsFactor (ε : Mode → ℝ) (β : ℝ) :
    FreeThermalField Mode → ℂ
  | .annihilate i => Complex.exp ((β : ℂ) * (ε i : ℂ))
  | .create i => Complex.exp (-(β : ℂ) * (ε i : ℂ))

/-- Uniform KMS rotation for either kind of free thermal field. -/
theorem FreeThermalField.freeGibbsExpectation_operator_comp_rotate
    (ε : Mode → ℝ) (β : ℝ) (C : FreeThermalField Mode)
    (A : FockSpace Mode →ₗ[ℂ] FockSpace Mode) :
    freeGibbsExpectation ε β (C.operator.comp A) =
      C.kmsFactor ε β * freeGibbsExpectation ε β (A.comp C.operator) := by
  cases C with
  | annihilate i =>
      exact freeGibbsExpectation_annihilate_rotate ε β i A
  | create i =>
      exact freeGibbsExpectation_create_rotate ε β i A

end
end Bosonic
end SecondQuantization
