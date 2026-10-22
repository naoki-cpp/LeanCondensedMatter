import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.RankOne
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.DiscreteLattice
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.OccupationFieldEquivalence
import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.NumberOperator

set_option linter.style.header false

/-!
# Lattice rank-one second-quantization adapter

This module specializes the basis-independent algebraic rank-one theorem to lattice matrix units.
The generic `dGamma_dualRankOne` theorem is owned upstream by `Fermionic.AlgebraicFock`, with the
rank-one one-particle map represented directly by Mathlib's `LinearMap.smulRight`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

noncomputable section

open scoped BigOperators

variable {Site : Type*}

/-- The second quantization of a lattice matrix unit factors into creation and annihilation fields. -/
theorem dGamma_matrixUnit (x y : Site) :
    AlgebraicFock.dGamma ((Site →₀ ℂ)) (matrixUnit x y) =
      (AlgebraicFock.create ((Site →₀ ℂ)) (latticeKet x)).comp
        (AlgebraicFock.annihilateDual ((Site →₀ ℂ)) (Finsupp.lapply y)) := by
  change AlgebraicFock.dGamma ((Site →₀ ℂ))
      ((Finsupp.lapply y : Module.Dual ℂ (Site →₀ ℂ)).smulRight (latticeKet x)) = _
  exact AlgebraicFock.dGamma_dualRankOne
    ((Site →₀ ℂ)) (latticeKet x) (Finsupp.lapply y)

variable [LinearOrder Site]

/-- Lattice matrix units become occupation-basis creation-annihilation bilinears for
arbitrary site sets, before any finite-dimensional bounded transport. -/
theorem occupationConjugate_dGamma_matrixUnit (x y : Site) :
    AlgebraicFock.occupationConjugate
        (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ))
        (AlgebraicFock.dGamma ((Site →₀ ℂ)) (matrixUnit x y)) =
      (create x).comp (annihilate y) := by
  rw [dGamma_matrixUnit]
  have hConj := map_mul
    (AlgebraicFock.occupationConjugate
      (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ)))
    (AlgebraicFock.create ((Site →₀ ℂ)) (latticeKet x))
    (AlgebraicFock.annihilateDual ((Site →₀ ℂ)) (Finsupp.lapply y))
  simp only [Module.End.mul_eq_comp] at hConj
  rw [hConj]
  have hx :
      (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ)) x =
        latticeKet x := rfl
  have hy :
      (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ)).coord y =
        (Finsupp.lapply y : Module.Dual ℂ (Site →₀ ℂ)) := by
    ext ψ
    rfl
  rw [← hx, ← hy, AlgebraicFock.occupationConjugate_create,
    AlgebraicFock.occupationConjugate_annihilateDual]

/-- Second quantization of a diagonal one-particle operator sums its coefficients over the
occupied modes. Real coefficients give the occupation-energy free Hamiltonian. -/
theorem occupationConjugate_dGamma_diagonalOperator [Finite Site] (a : Site → ℂ) :
    AlgebraicFock.occupationConjugate
        (Finsupp.basisSingleOne : Module.Basis Site ℂ (Site →₀ ℂ))
        (AlgebraicFock.dGamma ((Site →₀ ℂ)) (Common.diagonalOperator a)) =
      Common.diagonalOperator (fun n : Occupation Site => ∑ i ∈ n, a i) := by
  classical
  letI : Fintype Site := Fintype.ofFinite Site
  have hdiag : Common.diagonalOperator a = ∑ i, a i • matrixUnit i i := by
    apply Common.linearMap_ext_basisState
    intro j
    ext i
    by_cases hij : i = j
    · subst i
      simp [Common.diagonalOperator_apply, Common.basisState, LinearMap.sum_apply,
        Finsupp.finsetSum_apply, matrixUnit_apply, Finsupp.single_apply]
    · simp [Common.diagonalOperator_apply, Common.basisState, LinearMap.sum_apply,
        Finsupp.finsetSum_apply, matrixUnit_apply, Finsupp.single_apply, hij, Ne.symm hij]
  rw [hdiag]
  change AlgebraicFock.occupationConjugate _
    (AlgebraicFock.dGammaLinear ((Site →₀ ℂ)) (∑ i, a i • matrixUnit i i)) = _
  simp only [map_sum, map_smul, AlgebraicFock.dGammaLinear_apply,
    occupationConjugate_dGamma_matrixUnit]
  apply Common.linearMap_ext_basisState
  intro n
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Common.diagonalOperator_basisState]
  change (∑ i, a i • numberOperator i (Common.basisState n)) =
    (∑ i ∈ n, a i) • Common.basisState n
  have hnumber : (∑ i, a i • numberOperator i (Common.basisState n)) =
      ∑ i, if i ∈ n then a i • Common.basisState n else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [smul_ite, smul_zero] using
      congrArg (fun v => a i • v) (numberOperator_basisState i n)
  rw [hnumber]
  have hfilter : (Finset.univ : Finset Site).filter (fun i => i ∈ n) = n := by
    ext i
    simp
  rw [← Finset.sum_filter, hfilter, Finset.sum_smul]

end
end Lattice
end Fermionic
end SecondQuantization
