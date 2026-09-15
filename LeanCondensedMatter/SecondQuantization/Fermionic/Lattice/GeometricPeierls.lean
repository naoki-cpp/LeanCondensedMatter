import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent

set_option linter.style.header false

/-!
# Geometric Peierls families on a finite lattice

The geometric current and contact operators are not merely weighted sums. They arise by coupling a
single uniform source parameter to every oriented bond through its geometric coordinate

```text
A_xy = w_xy A.
```

The chain rule then gives

```text
-∂_A H_direction(0) = J_direction,
 ∂_A J_direction(0) = C_direction.
```

This module proves those identities for the bounded finite-lattice Hilbert realization. The
parameter is complexified for the algebraic derivative, while the geometric bond coordinates are
real and embedded into `ℂ`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

open scoped BigOperators

noncomputable section

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Uniform-direction Peierls Hamiltonian. Each bond sees the scaled source
`A_xy = w_xy A`; the factor `1/2` removes duplicate orientations. -/
noncomputable def boundedDirectionalPeierlsHamiltonian
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (A : ℂ) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  (2 : ℂ)⁻¹ •
    ∑ x : Site, ∑ y : Site,
      boundedPeierlsBondHamiltonian K ℏ q x y
        ((geometry.bondCoordinate direction x y : ℂ) * A)

/-- Uniform-direction source-dependent current. The measured current carries one explicit geometric
factor, while its bond Peierls parameter is also `w_xy A`. -/
noncomputable def boundedDirectionalPeierlsCurrent
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (A : ℂ) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  (2 : ℂ)⁻¹ •
    ∑ x : Site, ∑ y : Site,
      (geometry.bondCoordinate direction x y : ℂ) •
        boundedPeierlsBondCurrent K ℏ q x y
          ((geometry.bondCoordinate direction x y : ℂ) * A)

/-- At zero source, the geometric Peierls current is the continuity-derived directional current. -/
@[simp]
theorem boundedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedDirectionalPeierlsCurrent geometry direction ℏ q K 0 =
      boundedDirectionalCurrent geometry direction ℏ q K := by
  simp [boundedDirectionalPeierlsCurrent, boundedDirectionalCurrent]

/-- The global geometric Peierls Hamiltonian differentiates to minus the directional current. -/
theorem hasAlgebraicDerivAt_boundedDirectionalPeierlsHamiltonian_zero
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    HasAlgebraicDerivAt
      (boundedDirectionalPeierlsHamiltonian geometry direction ℏ q K)
      (-boundedDirectionalCurrent geometry direction ℏ q K) 0 := by
  have hxy : ∀ x y : Site,
      HasAlgebraicDerivAt
        (fun A => boundedPeierlsBondHamiltonian K ℏ q x y
          ((geometry.bondCoordinate direction x y : ℂ) * A))
        ((geometry.bondCoordinate direction x y : ℂ) •
          (-boundedBondCurrent ℏ q K x y)) 0 := by
    intro x y
    have hbond :
        HasAlgebraicDerivAt
          (boundedPeierlsBondHamiltonian K ℏ q x y)
          (-boundedBondCurrent ℏ q K x y)
          ((geometry.bondCoordinate direction x y : ℂ) * 0) := by
      simpa using hasAlgebraicDerivAt_boundedPeierlsBondHamiltonian_zero K ℏ q x y
    exact hbond.comp
      (hasDerivAt_const_mul (x := (0 : ℂ))
        (geometry.bondCoordinate direction x y : ℂ))
  have hy : ∀ x : Site,
      HasAlgebraicDerivAt
        (fun A => ∑ y : Site,
          boundedPeierlsBondHamiltonian K ℏ q x y
            ((geometry.bondCoordinate direction x y : ℂ) * A))
        (∑ y : Site, (geometry.bondCoordinate direction x y : ℂ) •
          (-boundedBondCurrent ℏ q K x y)) 0 := by
    intro x
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      HasAlgebraicDerivAt.sum (Finset.univ : Finset Site)
        (fun y _ => hxy x y)
  have hsum :
      HasAlgebraicDerivAt
        (fun A => ∑ x : Site, ∑ y : Site,
          boundedPeierlsBondHamiltonian K ℏ q x y
            ((geometry.bondCoordinate direction x y : ℂ) * A))
        (∑ x : Site, ∑ y : Site,
          (geometry.bondCoordinate direction x y : ℂ) •
            (-boundedBondCurrent ℏ q K x y)) 0 := by
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      HasAlgebraicDerivAt.sum (Finset.univ : Finset Site)
        (fun x _ => hy x)
  have hscaled := hsum.const_smul ((2 : ℂ)⁻¹)
  unfold boundedDirectionalPeierlsHamiltonian boundedDirectionalCurrent
  simpa [smul_neg, Finset.sum_neg_distrib] using hscaled

/-- Differentiating the geometric Peierls current gives the squared-coordinate contact operator. -/
theorem hasAlgebraicDerivAt_boundedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    HasAlgebraicDerivAt
      (boundedDirectionalPeierlsCurrent geometry direction ℏ q K)
      (boundedDirectionalContact geometry direction ℏ q K) 0 := by
  have hxy : ∀ x y : Site,
      HasAlgebraicDerivAt
        (fun A => (geometry.bondCoordinate direction x y : ℂ) •
          boundedPeierlsBondCurrent K ℏ q x y
            ((geometry.bondCoordinate direction x y : ℂ) * A))
        ((geometry.bondCoordinate direction x y : ℂ) •
          ((geometry.bondCoordinate direction x y : ℂ) •
            boundedBondContact K ℏ q x y)) 0 := by
    intro x y
    have hbond :
        HasAlgebraicDerivAt
          (boundedPeierlsBondCurrent K ℏ q x y)
          (boundedBondContact K ℏ q x y)
          ((geometry.bondCoordinate direction x y : ℂ) * 0) := by
      simpa using hasAlgebraicDerivAt_boundedPeierlsBondCurrent_zero K ℏ q x y
    exact
      (hbond.comp
        (hasDerivAt_const_mul (x := (0 : ℂ))
          (geometry.bondCoordinate direction x y : ℂ))).const_smul
          (geometry.bondCoordinate direction x y : ℂ)
  have hy : ∀ x : Site,
      HasAlgebraicDerivAt
        (fun A => ∑ y : Site,
          (geometry.bondCoordinate direction x y : ℂ) •
            boundedPeierlsBondCurrent K ℏ q x y
              ((geometry.bondCoordinate direction x y : ℂ) * A))
        (∑ y : Site,
          (geometry.bondCoordinate direction x y : ℂ) •
            ((geometry.bondCoordinate direction x y : ℂ) •
              boundedBondContact K ℏ q x y)) 0 := by
    intro x
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      HasAlgebraicDerivAt.sum (Finset.univ : Finset Site)
        (fun y _ => hxy x y)
  have hsum :
      HasAlgebraicDerivAt
        (fun A => ∑ x : Site, ∑ y : Site,
          (geometry.bondCoordinate direction x y : ℂ) •
            boundedPeierlsBondCurrent K ℏ q x y
              ((geometry.bondCoordinate direction x y : ℂ) * A))
        (∑ x : Site, ∑ y : Site,
          (geometry.bondCoordinate direction x y : ℂ) •
            ((geometry.bondCoordinate direction x y : ℂ) •
              boundedBondContact K ℏ q x y)) 0 := by
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      HasAlgebraicDerivAt.sum (Finset.univ : Finset Site)
        (fun x _ => hy x)
  have hscaled := hsum.const_smul ((2 : ℂ)⁻¹)
  have hderiv :
      (2 : ℂ)⁻¹ •
          ∑ x : Site, ∑ y : Site,
            (geometry.bondCoordinate direction x y : ℂ) •
              ((geometry.bondCoordinate direction x y : ℂ) •
                boundedBondContact K ℏ q x y) =
        (2 : ℂ)⁻¹ •
          ∑ x : Site, ∑ y : Site,
            ((geometry.bondCoordinate direction x y) ^ 2 : ℂ) •
              boundedBondContact K ℏ q x y := by
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    rw [smul_smul]
    congr 1
    norm_num [pow_two]
  unfold boundedDirectionalPeierlsCurrent boundedDirectionalContact
  rw [← hderiv]
  exact hscaled

end
end Lattice
end Fermionic
end SecondQuantization
