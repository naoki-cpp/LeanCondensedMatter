import LeanCondensedMatter.SecondQuantization.Fermionic.CompletedSpace.UnitaryLift
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantization
import LeanCondensedMatter.Analysis.Operator.Unbounded.ResolventEvolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option linter.style.header false

/-!
# Infinitesimal Fock evolution on invariant one-particle subspaces

If the one-particle orbit of `j v` has derivative `-i j(T v)` at zero, the lifted orbit of a
finite exterior expression has derivative given by the existing algebraic `-i dΓ(T)` under the
same realization. The Stone specialization makes the one-particle domain and its invariance
explicit. This identifies the infinitesimal action on these vectors, not the maximal domain,
essential self-adjointness, or closure of the resulting Fock generator.
-/

namespace SecondQuantization.Fermionic

noncomputable section

variable {Mode : Type*} [LinearOrder Mode]

/-- On a realized algebraic exterior space, one-particle infinitesimal evolution lifts to the
existing `dGamma`. The source vector space can be an invariant domain of an unbounded operator. -/
theorem completedFockUnitary_completedExterior_hasDerivAt_zero
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (j : V →ₗ[ℂ] Common.CompletedFock Mode) (T : V →ₗ[ℂ] V)
    (e : ℝ → (Common.CompletedFock Mode ≃ₗᵢ[ℂ] Common.CompletedFock Mode))
    (hzero : e 0 = LinearIsometryEquiv.refl ℂ (Common.CompletedFock Mode))
    (he : ∀ v, HasDerivAt (fun t : ℝ => e t (j v)) ((-Complex.I) • j (T v)) 0)
    (x : AlgebraicFock V) :
    HasDerivAt (fun t : ℝ =>
      completedFockUnitary (e t) (completedExterior (ExteriorAlgebra.map j x)))
      ((-Complex.I) • completedExterior (ExteriorAlgebra.map j (AlgebraicFock.dGamma V T x)))
      0 := by
  have hcreate (v : V) (y : AlgebraicFock V) :
      completedExterior (ExteriorAlgebra.map j (AlgebraicFock.create V v y)) =
        completedCreateField (j v) (completedExterior (ExteriorAlgebra.map j y)) := by
    simp only [AlgebraicFock.create_apply, AlgebraicFock.oneParticle, map_mul,
      ExteriorAlgebra.map_apply_ι]
    exact completedExterior_create (j v) (ExteriorAlgebra.map j y)
  have hscalar (a : ℂ) :
      AlgebraicFock.dGamma V T (algebraMap ℂ (AlgebraicFock V) a) = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul]
    change a • AlgebraicFock.dGamma V T (AlgebraicFock.vacuum V) = 0
    rw [AlgebraicFock.dGamma_vacuum, smul_zero]
  induction x using CliffordAlgebra.left_induction with
  | algebraMap a =>
      simp only [AlgHom.commutes, completedExterior_algebraMap, map_smul,
        completedFockUnitary_vacuum, hscalar, map_zero, smul_zero]
      exact hasDerivAt_const 0 _
  | add x y hx hy =>
      simp only [map_add, smul_add]
      convert! hx.add hy using 1
  | ι_mul x v hx =>
      change HasDerivAt (fun t : ℝ => completedFockUnitary (e t)
        (completedExterior (ExteriorAlgebra.map j (AlgebraicFock.create V v x))))
        ((-Complex.I) • completedExterior
          (ExteriorAlgebra.map j (AlgebraicFock.dGamma V T (AlgebraicFock.create V v x)))) 0
      have hc := ((completedCreateField (Mode := Mode)).restrictScalars ℝ).hasFDerivAt
        |>.comp_hasDerivAt 0 (he v)
      let B : CompletedFockSpace Mode →L[ℝ]
          (CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode) →L[ℝ] CompletedFockSpace Mode :=
        (ContinuousLinearMap.apply ℂ (CompletedFockSpace Mode)).bilinearRestrictScalars ℝ
      have hd := ContinuousLinearMap.hasDerivAt_of_bilinear (B := B)
        (fun _ => hx) (fun _ => hc)
      change HasDerivAt (fun t : ℝ => completedCreateField (e t (j v))
        (completedFockUnitary (e t) (completedExterior (ExteriorAlgebra.map j x))))
        (completedCreateField ((-Complex.I) • j (T v))
            (completedFockUnitary (e 0) (completedExterior (ExteriorAlgebra.map j x))) +
          completedCreateField (e 0 (j v))
            ((-Complex.I) • completedExterior
              (ExteriorAlgebra.map j (AlgebraicFock.dGamma V T x)))) 0 at hd
      have hstep : AlgebraicFock.dGamma V T (AlgebraicFock.create V v x) =
          AlgebraicFock.create V (T v) x +
            AlgebraicFock.create V v (AlgebraicFock.dGamma V T x) :=
        AlgebraicFock.dGamma_oneParticle_mul V T v x
      rw [hstep]
      simp only [map_add, smul_add, hcreate, completedFockUnitary_createField]
      have hid : LinearIsometryEquiv.refl ℂ (Common.CompletedFock Mode) (j v) = j v := rfl
      simpa only [hzero, hid, completedFockUnitary_refl,
        map_smul, smul_apply] using hd

/-- For a self-adjoint one-particle Hamiltonian, the lifted Stone orbit has infinitesimal action
`-i dGamma(T)` on finite exterior expressions from any explicitly invariant subspace `D`.
No assertion that this subspace is an operator core is made. -/
theorem completedFock_stoneEvolution_hasDerivAt_zero
    (A : Common.CompletedFock Mode →ₗ.[ℂ] Common.CompletedFock Mode)
    (hA : IsSelfAdjoint A) (D : Submodule ℂ (Common.CompletedFock Mode))
    (T : D →ₗ[ℂ] D) (hdom : ∀ v : D, (v : Common.CompletedFock Mode) ∈ A.domain)
    (hT : ∀ v : D, A ⟨v, hdom v⟩ = (T v : Common.CompletedFock Mode))
    (x : AlgebraicFock D) :
    HasDerivAt (fun t : ℝ =>
      (completedFockUnitaryGroup (LinearPMap.stoneEvolutionUnitaryGroup A hA)
        (Multiplicative.ofAdd t) : CompletedFockSpace Mode →L[ℂ] CompletedFockSpace Mode)
          (completedExterior (ExteriorAlgebra.map D.subtype x)))
      ((-Complex.I) • completedExterior
        (ExteriorAlgebra.map D.subtype (AlgebraicFock.dGamma D T x))) 0 := by
  change HasDerivAt (fun t : ℝ => completedFockUnitary
    (Unitary.linearIsometryEquiv (LinearPMap.stoneEvolutionUnitaryGroup A hA
      (Multiplicative.ofAdd t))) (completedExterior (ExteriorAlgebra.map D.subtype x)))
    ((-Complex.I) • completedExterior
      (ExteriorAlgebra.map D.subtype (AlgebraicFock.dGamma D T x))) 0
  apply completedFockUnitary_completedExterior_hasDerivAt_zero D.subtype T
    (fun t : ℝ => Unitary.linearIsometryEquiv
      (LinearPMap.stoneEvolutionUnitaryGroup A hA (Multiplicative.ofAdd t))) ?_ ?_ x
  · apply LinearIsometryEquiv.ext
    intro v
    change LinearPMap.stoneEvolution A hA 0 v = v
    simp only [LinearPMap.stoneEvolution_zero, one_apply_eq_self]
  · intro v
    have h := LinearPMap.stoneEvolution_apply_hasDerivAt_zero A hA ⟨v, hdom v⟩
    rw [hT v] at h
    exact h

end
end SecondQuantization.Fermionic
