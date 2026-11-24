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

/-- Source-dependent current measured in one direction while the uniform Peierls
source couples along another direction. -/
noncomputable def boundedMixedDirectionalPeierlsCurrent
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (A : ℂ) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  (2 : ℂ)⁻¹ •
    ∑ x : Site, ∑ y : Site,
      (geometry.bondCoordinate measured x y : ℂ) •
        boundedPeierlsBondCurrent K ℏ q x y
          ((geometry.bondCoordinate source x y : ℂ) * A)

/-- The original same-direction Peierls current is the diagonal mixed current. -/
noncomputable def boundedDirectionalPeierlsCurrent
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (A : ℂ) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedMixedDirectionalPeierlsCurrent geometry direction direction ℏ q K A

/-- At zero source the measured current is independent of the source direction. -/
@[simp]
theorem boundedMixedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedMixedDirectionalPeierlsCurrent geometry measured source ℏ q K 0 =
      boundedDirectionalCurrent geometry measured ℏ q K := by
  simp [boundedMixedDirectionalPeierlsCurrent, boundedDirectionalCurrent]

/-- At zero source the diagonal Peierls current is the directional current. -/
@[simp]
theorem boundedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedDirectionalPeierlsCurrent geometry direction ℏ q K 0 =
      boundedDirectionalCurrent geometry direction ℏ q K :=
  boundedMixedDirectionalPeierlsCurrent_zero geometry direction direction ℏ q K

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

/-- Differentiating a measured current along an independent Peierls source gives the mixed contact. -/
theorem hasAlgebraicDerivAt_boundedMixedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    HasAlgebraicDerivAt
      (boundedMixedDirectionalPeierlsCurrent geometry measured source ℏ q K)
      (boundedMixedDirectionalContact geometry measured source ℏ q K) 0 := by
  have hxy : ∀ x y : Site,
      HasAlgebraicDerivAt
        (fun A => (geometry.bondCoordinate measured x y : ℂ) •
          boundedPeierlsBondCurrent K ℏ q x y
            ((geometry.bondCoordinate source x y : ℂ) * A))
        ((geometry.bondCoordinate source x y : ℂ) •
          ((geometry.bondCoordinate source x y : ℂ) •
            boundedBondContact K ℏ q x y)) 0 := by
    intro x y
    have hbond :
        HasAlgebraicDerivAt
          (boundedPeierlsBondCurrent K ℏ q x y)
          (boundedBondContact K ℏ q x y)
          ((geometry.bondCoordinate source x y : ℂ) * 0) := by
      simpa using hasAlgebraicDerivAt_boundedPeierlsBondCurrent_zero K ℏ q x y
    exact
      (hbond.comp
        (hasDerivAt_const_mul (x := (0 : ℂ))
          (geometry.bondCoordinate source x y : ℂ))).const_smul
          (geometry.bondCoordinate measured x y : ℂ)
  have hy : ∀ x : Site,
      HasAlgebraicDerivAt
        (fun A => ∑ y : Site,
          (geometry.bondCoordinate measured x y : ℂ) •
            boundedPeierlsBondCurrent K ℏ q x y
              ((geometry.bondCoordinate source x y : ℂ) * A))
        (∑ y : Site,
          (geometry.bondCoordinate measured x y : ℂ) •
            ((geometry.bondCoordinate source x y : ℂ) •
              boundedBondContact K ℏ q x y)) 0 := by
    intro x
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      HasAlgebraicDerivAt.sum (Finset.univ : Finset Site)
        (fun y _ => hxy x y)
  have hsum :
      HasAlgebraicDerivAt
        (fun A => ∑ x : Site, ∑ y : Site,
          (geometry.bondCoordinate measured x y : ℂ) •
            boundedPeierlsBondCurrent K ℏ q x y
              ((geometry.bondCoordinate source x y : ℂ) * A))
        (∑ x : Site, ∑ y : Site,
          (geometry.bondCoordinate measured x y : ℂ) •
            ((geometry.bondCoordinate source x y : ℂ) •
              boundedBondContact K ℏ q x y)) 0 := by
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      HasAlgebraicDerivAt.sum (Finset.univ : Finset Site)
        (fun x _ => hy x)
  have hscaled := hsum.const_smul ((2 : ℂ)⁻¹)
  unfold boundedMixedDirectionalPeierlsCurrent boundedMixedDirectionalContact
  simpa only [smul_smul] using hscaled

/-- The same-direction derivative is the diagonal specialization of the mixed derivative. -/
theorem hasAlgebraicDerivAt_boundedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    HasAlgebraicDerivAt
      (boundedDirectionalPeierlsCurrent geometry direction ℏ q K)
      (boundedDirectionalContact geometry direction ℏ q K) 0 :=
  hasAlgebraicDerivAt_boundedMixedDirectionalPeierlsCurrent_zero
    geometry direction direction ℏ q K

end
end Lattice
end Fermionic
end SecondQuantization
