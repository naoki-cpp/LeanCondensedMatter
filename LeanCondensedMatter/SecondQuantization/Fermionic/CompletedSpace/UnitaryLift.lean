import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.SmearedField
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.Annihilation
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option linter.style.header false

/-!
# Unitary one-particle maps on completed fermionic Fock space

The exterior algebra of the full one-particle ℓ² space acts by the bounded creation fields.
Evaluating this action on the vacuum gives a dense linear realization in completed occupation
Fock space. Its inner product is preserved by exterior transport along a one-particle isometry.
Mathlib's dense isometric extension then lifts a one-particle unitary without a finite-mode
restriction. No norm or inner-product instance is imposed on the algebraic exterior algebra.
-/

namespace SecondQuantization.Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

private def completedExteriorRepresentation :
    AlgebraicFock (Common.CompletedFock Mode) →ₐ[ℂ]
      (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) :=
  ExteriorAlgebra.lift ℂ ⟨completedCreateField.toLinearMap, fun v => by
    have h := completedAnticomm_createField_createField v v
    have htwo : (2 : ℂ) • (completedCreateField v * completedCreateField v) = 0 := by
      simpa only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add,
        two_smul] using h
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)⟩

/-- Realization of finite exterior expressions in arbitrary ℓ² one-particle vectors by
successive completed creation fields acting on the vacuum. -/
def completedExterior :
    AlgebraicFock (Common.CompletedFock Mode) →ₗ[ℂ] CompletedFockSpace Mode where
  toFun x := completedExteriorRepresentation x (completedBasisState vacuum)
  map_add' x y := by simp
  map_smul' a x := by simp

private theorem completedExterior_algebraMap (a : ℂ) :
    completedExterior (algebraMap ℂ (AlgebraicFock (Common.CompletedFock Mode)) a) =
      a • completedBasisState (vacuum : Occupation Mode) := by
  change completedExteriorRepresentation (algebraMap ℂ _ a) _ = _
  simp [Algebra.algebraMap_eq_smul_one]

/-- Exterior creation is represented by the bounded completed creation field. -/
theorem completedExterior_create (v : Common.CompletedFock Mode)
    (x : AlgebraicFock (Common.CompletedFock Mode)) :
    completedExterior (AlgebraicFock.create _ v x) =
      completedCreateField v (completedExterior x) := by
  change completedExteriorRepresentation (ExteriorAlgebra.ι ℂ v * x) _ = _
  rw [map_mul]
  change completedExteriorRepresentation (ExteriorAlgebra.ι ℂ v)
    (completedExterior x) = _
  rw [show completedExteriorRepresentation (ExteriorAlgebra.ι ℂ v) =
    completedCreateField v from ExteriorAlgebra.lift_ι_apply ℂ _ _ v]

omit [LinearOrder Mode] in
private theorem annihilate_scalar (v : Common.CompletedFock Mode) (a : ℂ) :
    AlgebraicFock.annihilate _ v
      (algebraMap ℂ (AlgebraicFock (Common.CompletedFock Mode)) a) = 0 := by
  change CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Common.CompletedFock Mode)))
    (AlgebraicFock.innerDual _ v) (algebraMap ℂ _ a) = 0
  rw [CliffordAlgebra.contractLeft_algebraMap]

private theorem completedExterior_annihilate (v : Common.CompletedFock Mode)
    (x : AlgebraicFock (Common.CompletedFock Mode)) :
    star (completedCreateField v) (completedExterior x) =
      completedExterior (AlgebraicFock.annihilate _ v x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap a =>
      rw [completedExterior_algebraMap, map_smul, adjoint_completedCreateField_vacuum,
        smul_zero, annihilate_scalar, map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x w hx =>
      change star (completedCreateField v)
        (completedExterior (AlgebraicFock.create _ w x)) =
          completedExterior (AlgebraicFock.annihilate _ v (AlgebraicFock.create _ w x))
      rw [completedExterior_create]
      have h := congrArg (fun T : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode =>
        T (completedExterior x)) (completedAnticomm_adjoint_createField v w)
      simp only [ScalarExchange.zetaCommutator, neg_one_smul, sub_neg_eq_add, add_apply,
        mul_apply_eq_comp, smul_apply, ContinuousLinearMap.id_apply, hx] at h
      have hc : AlgebraicFock.annihilate _ v (AlgebraicFock.create _ w x) =
          inner ℂ v w • x - AlgebraicFock.create _ w (AlgebraicFock.annihilate _ v x) :=
        AlgebraicFock.annihilateDual_create_apply _ (AlgebraicFock.innerDual _ v) w x
      rw [hc, map_sub, map_smul, completedExterior_create]
      exact eq_sub_of_add_eq h

private theorem inner_completedExterior_create (v : Common.CompletedFock Mode)
    (x y : AlgebraicFock (Common.CompletedFock Mode)) :
    inner ℂ (completedExterior (AlgebraicFock.create _ v x)) (completedExterior y) =
      inner ℂ (completedExterior x)
        (completedExterior (AlgebraicFock.annihilate _ v y)) := by
  rw [completedExterior_create, ← ContinuousLinearMap.adjoint_inner_right,
    ← ContinuousLinearMap.star_eq_adjoint, completedExterior_annihilate]

private theorem inner_completedExterior_scalar_create (a : ℂ) (v : Common.CompletedFock Mode)
    (x : AlgebraicFock (Common.CompletedFock Mode)) :
    inner ℂ (completedExterior (algebraMap ℂ _ a))
      (completedExterior (AlgebraicFock.create _ v x)) = 0 := by
  have h := congrArg (starRingEnd ℂ)
    (inner_completedExterior_create v x (algebraMap ℂ _ a))
  simpa only [annihilate_scalar, map_zero, inner_zero_right, inner_conj_symm] using h

/-- Exterior transport by a one-particle isometry preserves the realized Fock inner product. -/
theorem inner_completedExterior_map (e : Common.CompletedFock Mode →ₗᵢ[ℂ]
    Common.CompletedFock Mode) (x y : AlgebraicFock (Common.CompletedFock Mode)) :
    inner ℂ (completedExterior (ExteriorAlgebra.map e.toLinearMap x))
      (completedExterior (ExteriorAlgebra.map e.toLinearMap y)) =
        inner ℂ (completedExterior x) (completedExterior y) := by
  have hcreate (v : Common.CompletedFock Mode) (z : AlgebraicFock (Common.CompletedFock Mode)) :
      ExteriorAlgebra.map e.toLinearMap (AlgebraicFock.create _ v z) =
        AlgebraicFock.create _ (e v) (ExteriorAlgebra.map e.toLinearMap z) := by
    simp only [AlgebraicFock.create_apply, AlgebraicFock.oneParticle, map_mul,
      ExteriorAlgebra.map_apply_ι]
    rfl
  have hscalar (a : ℂ) (z : AlgebraicFock (Common.CompletedFock Mode)) :
      inner ℂ (completedExterior (ExteriorAlgebra.map e.toLinearMap (algebraMap ℂ _ a)))
        (completedExterior (ExteriorAlgebra.map e.toLinearMap z)) =
          inner ℂ (completedExterior (algebraMap ℂ _ a)) (completedExterior z) := by
    induction z using CliffordAlgebra.left_induction with
    | algebraMap d => simp only [AlgHom.commutes]
    | add z w hz hw => simp only [map_add, inner_add_right, hz, hw]
    | ι_mul z v _ =>
        change inner ℂ (completedExterior (ExteriorAlgebra.map e.toLinearMap (algebraMap ℂ _ a)))
          (completedExterior (ExteriorAlgebra.map e.toLinearMap (AlgebraicFock.create _ v z))) =
            inner ℂ (completedExterior (algebraMap ℂ _ a))
              (completedExterior (AlgebraicFock.create _ v z))
        rw [hcreate]
        simp only [AlgHom.commutes, inner_completedExterior_scalar_create]
  induction x using CliffordAlgebra.left_induction generalizing y with
  | algebraMap a => exact hscalar a y
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
  | ι_mul x v hx =>
      change inner ℂ
        (completedExterior (ExteriorAlgebra.map e.toLinearMap (AlgebraicFock.create _ v x)))
        (completedExterior (ExteriorAlgebra.map e.toLinearMap y)) =
          inner ℂ (completedExterior (AlgebraicFock.create _ v x)) (completedExterior y)
      rw [hcreate, inner_completedExterior_create, AlgebraicFock.annihilate_map, hx,
        inner_completedExterior_create]

private theorem completedExterior_denseRange :
    DenseRange (completedExterior (Mode := Mode)) := by
  classical
  have hbasis (n : Occupation Mode) :
      ∃ x, completedExterior x = completedBasisState n := by
    induction n using Finset.induction_on with
    | empty =>
        refine ⟨algebraMap ℂ _ 1, ?_⟩
        simp only [completedExterior_algebraMap, one_smul, vacuum]
    | @insert i n hi hn =>
        obtain ⟨x, hx⟩ := hn
        refine ⟨fermionPhase i n •
          AlgebraicFock.create _ (Common.completedBasisState i) x, ?_⟩
        rw [map_smul, completedExterior_create, hx, completedCreateField_basisState,
          completedCreate_basisState_of_not_mem hi, smul_smul]
        simp only [fermionPhase, fermionSign_sq_complex, one_smul, insertOccupation]
  choose p hp using hbasis
  let L := Finsupp.linearCombination ℂ p
  have heq : completedExterior.comp L =
      Common.algebraicToCompleted (Config := Occupation Mode) := by
    apply Common.linearMap_ext_basisState
    intro n
    change completedExterior (L (Common.basisState n)) =
      Common.algebraicToCompleted (Common.basisState n)
    rw [Common.algebraicToCompleted_basisState]
    simpa [L, Common.basisState, completedBasisState] using hp n
  have hsubset : Set.range (Common.algebraicToCompleted (Config := Occupation Mode)) ⊆
      Set.range (completedExterior (Mode := Mode)) := by
    rintro _ ⟨x, rfl⟩
    exact ⟨L x, congrArg (fun f : OccupationFock Mode →ₗ[ℂ] CompletedFockSpace Mode => f x) heq⟩
  intro x
  exact closure_mono hsubset (Common.algebraicToCompleted_denseRange x)

private def exteriorUnitary (e : Common.CompletedFock Mode ≃ₗᵢ[ℂ] Common.CompletedFock Mode) :
    AlgebraicFock (Common.CompletedFock Mode) ≃ₗ[ℂ]
      AlgebraicFock (Common.CompletedFock Mode) :=
  (CliffordAlgebra.equivOfIsometry
    (show (0 : QuadraticForm ℂ (Common.CompletedFock Mode)).IsometryEquiv 0 from
      { e.toLinearEquiv with map_app' := fun _ => rfl })).toLinearEquiv

private theorem norm_completedExterior_map
    (e : Common.CompletedFock Mode ≃ₗᵢ[ℂ] Common.CompletedFock Mode)
    (x : AlgebraicFock (Common.CompletedFock Mode)) :
    ‖completedExterior (exteriorUnitary e x)‖ = ‖completedExterior x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := inner_completedExterior_map e.toLinearIsometry x x
  change inner ℂ (completedExterior (exteriorUnitary e x))
    (completedExterior (exteriorUnitary e x)) = inner ℂ (completedExterior x)
      (completedExterior x) at h
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  convert! h using 1 <;> simp only [Complex.ofReal_pow] <;> with_unfolding_all rfl

/-- The fermionic Fock lift of a one-particle unitary on ℓ² modes, extended isometrically from
finite exterior expressions. The mode type need not be finite or countable. -/
def completedFockUnitary
    (e : Common.CompletedFock Mode ≃ₗᵢ[ℂ] Common.CompletedFock Mode) :
    CompletedFockSpace Mode ≃ₗᵢ[ℂ] CompletedFockSpace Mode :=
  (exteriorUnitary e).extendOfIsometry completedExterior completedExterior
    completedExterior_denseRange completedExterior_denseRange (norm_completedExterior_map e)

/-- The completed unitary agrees with exterior transport on its dense realization. -/
theorem completedFockUnitary_completedExterior
    (e : Common.CompletedFock Mode ≃ₗᵢ[ℂ] Common.CompletedFock Mode)
    (x : AlgebraicFock (Common.CompletedFock Mode)) :
    completedFockUnitary e (completedExterior x) =
      completedExterior (ExteriorAlgebra.map e.toLinearEquiv.toLinearMap x) := by
  exact LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ x

/-- The Fock lift fixes the vacuum. -/
theorem completedFockUnitary_vacuum
    (e : Common.CompletedFock Mode ≃ₗᵢ[ℂ] Common.CompletedFock Mode) :
    completedFockUnitary e (completedBasisState (vacuum : Occupation Mode)) =
      completedBasisState vacuum := by
  have h := completedFockUnitary_completedExterior e (algebraMap ℂ _ 1)
  simpa only [AlgHom.commutes, completedExterior_algebraMap, one_smul] using h

/-- A one-particle unitary intertwines arbitrary square-summable creation fields through its
Fock lift. -/
theorem completedFockUnitary_createField
    (e : Common.CompletedFock Mode ≃ₗᵢ[ℂ] Common.CompletedFock Mode)
    (v : Common.CompletedFock Mode) (x : CompletedFockSpace Mode) :
    completedFockUnitary e (completedCreateField v x) =
      completedCreateField (e v) (completedFockUnitary e x) := by
  refine completedExterior_denseRange.induction_on x ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro y
    rw [← completedExterior_create, completedFockUnitary_completedExterior,
      completedFockUnitary_completedExterior]
    simp only [AlgebraicFock.create_apply, AlgebraicFock.oneParticle, map_mul,
      ExteriorAlgebra.map_apply_ι]
    exact completedExterior_create (e v) (ExteriorAlgebra.map e.toLinearEquiv.toLinearMap y)

/-- The identity one-particle unitary lifts to the identity on completed Fock space. -/
theorem completedFockUnitary_refl (x : CompletedFockSpace Mode) :
    completedFockUnitary (LinearIsometryEquiv.refl ℂ (Common.CompletedFock Mode)) x = x := by
  refine completedExterior_denseRange.induction_on x ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro y
    rw [completedFockUnitary_completedExterior]
    change completedExterior (ExteriorAlgebra.map LinearMap.id y) = completedExterior y
    simp only [ExteriorAlgebra.map_id, AlgHom.id_apply]

/-- Composition of one-particle unitaries agrees with composition of their Fock lifts. -/
theorem completedFockUnitary_trans
    (e f : Common.CompletedFock Mode ≃ₗᵢ[ℂ] Common.CompletedFock Mode)
    (x : CompletedFockSpace Mode) :
    completedFockUnitary (e.trans f) x = completedFockUnitary f (completedFockUnitary e x) := by
  refine completedExterior_denseRange.induction_on x ?_ ?_
  · apply isClosed_eq <;> fun_prop
  · intro y
    rw [completedFockUnitary_completedExterior, completedFockUnitary_completedExterior,
      completedFockUnitary_completedExterior]
    exact (congrArg
      (fun F : AlgebraicFock (Common.CompletedFock Mode) →ₐ[ℂ]
          AlgebraicFock (Common.CompletedFock Mode) => completedExterior (F y))
      (ExteriorAlgebra.map_comp_map e.toLinearEquiv.toLinearMap
        f.toLinearEquiv.toLinearMap)).symm

/-- Strongly continuous one-particle unitary families act jointly continuously on completed
Fock space. No operator-norm continuity of the one-particle or Fock family is assumed. -/
theorem completedFockUnitary_joint_continuous {X : Type*} [TopologicalSpace X]
    (e : X → (Common.CompletedFock Mode ≃ₗᵢ[ℂ] Common.CompletedFock Mode))
    (he : ∀ v, Continuous (fun t => e t v)) :
    Continuous (fun p : CompletedFockSpace Mode × X => completedFockUnitary (e p.2) p.1) := by
  have hcore (y : AlgebraicFock (Common.CompletedFock Mode)) :
      Continuous (fun t => completedFockUnitary (e t) (completedExterior y)) := by
    induction y using CliffordAlgebra.left_induction with
    | algebraMap a =>
        simp only [completedExterior_algebraMap, map_smul, completedFockUnitary_vacuum]
        exact continuous_const
    | add x y hx hy => simpa only [map_add] using hx.add hy
    | ι_mul x v hx =>
        change Continuous (fun t =>
          completedFockUnitary (e t) (completedExterior (AlgebraicFock.create _ v x)))
        simp only [completedExterior_create, completedFockUnitary_createField]
        exact (completedCreateField.continuous.comp (he v)).clm_apply hx
  apply continuous_prod_of_dense_continuous_lipschitzWith _ 1 completedExterior_denseRange
  · rintro _ ⟨y, rfl⟩
    exact hcore y
  · intro t
    exact (completedFockUnitary (e t)).isometry.lipschitzWith

/-- The fermionic Fock lift of a supplied one-parameter unitary group, in the bounded-operator
unitary type used by the general linear-response API. -/
def completedFockUnitaryGroup
    (U : Multiplicative ℝ →* unitary (Common.CompletedFock Mode →L[ℂ] Common.CompletedFock Mode)) :
    Multiplicative ℝ →* unitary (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) where
  toFun t := Unitary.linearIsometryEquiv.symm
    (completedFockUnitary (Unitary.linearIsometryEquiv (U t)))
  map_one' := by
    apply Subtype.ext
    ext x
    change completedFockUnitary (Unitary.linearIsometryEquiv (U 1)) x = x
    simp only [map_one]
    exact completedFockUnitary_refl x
  map_mul' t s := by
    apply Subtype.ext
    ext x
    change completedFockUnitary (Unitary.linearIsometryEquiv (U (t * s))) x =
      completedFockUnitary (Unitary.linearIsometryEquiv (U t))
        (completedFockUnitary (Unitary.linearIsometryEquiv (U s)) x)
    simp only [map_mul]
    exact completedFockUnitary_trans (Unitary.linearIsometryEquiv (U s))
      (Unitary.linearIsometryEquiv (U t)) x

/-- Strong continuity of the one-particle group supplies the strong-continuity hypothesis
required by the general density linear-response theorems on completed Fock space. -/
theorem completedFockUnitaryGroup_apply_continuous
    (U : Multiplicative ℝ →* unitary (Common.CompletedFock Mode →L[ℂ] Common.CompletedFock Mode))
    (hU : ∀ v, Continuous (fun t : ℝ =>
      (U (Multiplicative.ofAdd t) : Common.CompletedFock Mode →L[ℂ] Common.CompletedFock Mode) v))
    (x : CompletedFockSpace Mode) :
    Continuous (fun t : ℝ =>
      (completedFockUnitaryGroup U (Multiplicative.ofAdd t) :
        CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) x) := by
  have he : ∀ v, Continuous (fun t : ℝ =>
      Unitary.linearIsometryEquiv (U (Multiplicative.ofAdd t)) v) := hU
  exact (completedFockUnitary_joint_continuous
    (fun t : ℝ => Unitary.linearIsometryEquiv (U (Multiplicative.ofAdd t))) he).comp
      (continuous_const.prodMk continuous_id)

end
end SecondQuantization.Fermionic
