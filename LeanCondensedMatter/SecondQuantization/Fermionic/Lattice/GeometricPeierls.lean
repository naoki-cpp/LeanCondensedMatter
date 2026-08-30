import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.GeometricCurrent

set_option linter.style.header false

/-!
# Geometric Peierls families on a finite lattice

The geometric current and contact operators are not merely weighted sums. They arise by coupling a
single uniform source parameter to every oriented bond through its geometric coordinate

```text
A_xy = w_xy A.
```

For a current measured by coordinate functional `i` and a source applied through coordinate
functional `j`, the chain rule gives

```text
J_i(0) = J_i,
∂_{A_j} J_i(0) = C_ij.
```

The historical one-direction identities are the diagonal specialization `i = j`. This module proves
these identities for the bounded finite-lattice Hilbert realization. The parameter is complexified
for the algebraic derivative, while the geometric bond coordinates are real and embedded into `ℂ`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

open scoped BigOperators

noncomputable section

namespace HasAlgebraicDerivAt

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Multiplying an algebraic-vector-valued family by a constant scalar multiplies its derivative. -/
theorem const_smul {F : ℂ → V} {F' : V} {A : ℂ}
    (hF : HasAlgebraicDerivAt F F' A) (c : ℂ) :
    HasAlgebraicDerivAt (fun z => c • F z) (c • F') A := by
  intro ℓ
  simpa only [map_smul, smul_eq_mul] using (hF ℓ).const_mul c

/-- Reparametrizing a family by `z ↦ c z` multiplies its derivative at zero by `c`. -/
theorem comp_const_mul_zero {F : ℂ → V} {F' : V}
    (hF : HasAlgebraicDerivAt F F' 0) (c : ℂ) :
    HasAlgebraicDerivAt (fun z => F (c * z)) (c • F') 0 := by
  intro ℓ
  have hinner : HasDerivAt (fun z : ℂ => c * z) c 0 :=
    hasDerivAt_const_mul (x := (0 : ℂ)) c
  have houter : HasDerivAt (fun z => ℓ (F z)) (ℓ F') (c * 0) := by
    simpa using hF ℓ
  have hcomp := HasDerivAt.comp 0 houter hinner
  have hcomp' : HasDerivAt (fun z => ℓ (F (c * z))) (ℓ F' * c) 0 := by
    apply hcomp.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun _ => rfl)
  simpa only [map_smul, smul_eq_mul, mul_comm] using hcomp'

/-- Finite sums preserve algebraic derivatives. -/
theorem sum {ι : Type*} (s : Finset ι) {F : ι → ℂ → V} {F' : ι → V} {A : ℂ}
    (hF : ∀ i ∈ s, HasAlgebraicDerivAt (F i) (F' i) A) :
    HasAlgebraicDerivAt (fun z => ∑ i ∈ s, F i z) (∑ i ∈ s, F' i) A := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ℓ
      simpa using (hasDerivAt_const (x := A) (c := (0 : ℂ)))
  | @insert a s ha ih =>
      have ha' := hF a (Finset.mem_insert_self a s)
      have hs' := ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))
      simpa only [Finset.sum_insert ha] using ha'.add hs'

end HasAlgebraicDerivAt

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

/-- Current measured along `measuredDirection` while the Peierls source is applied along
`sourceDirection`. The measured-current weight and source-phase weight are kept independent. -/
noncomputable def boundedMixedDirectionalPeierlsCurrent
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (A : ℂ) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  (2 : ℂ)⁻¹ •
    ∑ x : Site, ∑ y : Site,
      (geometry.bondCoordinate measuredDirection x y : ℂ) •
        boundedPeierlsBondCurrent K ℏ q x y
          ((geometry.bondCoordinate sourceDirection x y : ℂ) * A)

/-- The mixed current family reduces to the historical directional family on the diagonal. -/
@[simp]
theorem boundedMixedDirectionalPeierlsCurrent_self
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedMixedDirectionalPeierlsCurrent geometry direction direction ℏ q K =
      boundedDirectionalPeierlsCurrent geometry direction ℏ q K := by
  rfl

/-- At zero source, the geometric Peierls current is the continuity-derived directional current. -/
@[simp]
theorem boundedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedDirectionalPeierlsCurrent geometry direction ℏ q K 0 =
      boundedDirectionalCurrent geometry direction ℏ q K := by
  simp [boundedDirectionalPeierlsCurrent, boundedDirectionalCurrent]

/-- At zero source, the mixed family is the measured current independently of the source direction. -/
@[simp]
theorem boundedMixedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedMixedDirectionalPeierlsCurrent
        geometry measuredDirection sourceDirection ℏ q K 0 =
      boundedDirectionalCurrent geometry measuredDirection ℏ q K := by
  simp [boundedMixedDirectionalPeierlsCurrent, boundedDirectionalCurrent]

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
    exact
      (hasAlgebraicDerivAt_boundedPeierlsBondHamiltonian_zero K ℏ q x y).comp_const_mul_zero
        (geometry.bondCoordinate direction x y : ℂ)
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

/-- Differentiating `J_i(A_j)` at zero source gives the mixed Peierls contact `C_ij`. -/
theorem hasAlgebraicDerivAt_boundedMixedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    HasAlgebraicDerivAt
      (boundedMixedDirectionalPeierlsCurrent
        geometry measuredDirection sourceDirection ℏ q K)
      (boundedMixedDirectionalContact
        geometry measuredDirection sourceDirection ℏ q K) 0 := by
  have hxy : ∀ x y : Site,
      HasAlgebraicDerivAt
        (fun A => (geometry.bondCoordinate measuredDirection x y : ℂ) •
          boundedPeierlsBondCurrent K ℏ q x y
            ((geometry.bondCoordinate sourceDirection x y : ℂ) * A))
        ((geometry.bondCoordinate measuredDirection x y : ℂ) •
          ((geometry.bondCoordinate sourceDirection x y : ℂ) •
            boundedBondContact K ℏ q x y)) 0 := by
    intro x y
    exact
      ((hasAlgebraicDerivAt_boundedPeierlsBondCurrent_zero K ℏ q x y).comp_const_mul_zero
        (geometry.bondCoordinate sourceDirection x y : ℂ)).const_smul
          (geometry.bondCoordinate measuredDirection x y : ℂ)
  have hy : ∀ x : Site,
      HasAlgebraicDerivAt
        (fun A => ∑ y : Site,
          (geometry.bondCoordinate measuredDirection x y : ℂ) •
            boundedPeierlsBondCurrent K ℏ q x y
              ((geometry.bondCoordinate sourceDirection x y : ℂ) * A))
        (∑ y : Site,
          (geometry.bondCoordinate measuredDirection x y : ℂ) •
            ((geometry.bondCoordinate sourceDirection x y : ℂ) •
              boundedBondContact K ℏ q x y)) 0 := by
    intro x
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      HasAlgebraicDerivAt.sum (Finset.univ : Finset Site)
        (fun y _ => hxy x y)
  have hsum :
      HasAlgebraicDerivAt
        (fun A => ∑ x : Site, ∑ y : Site,
          (geometry.bondCoordinate measuredDirection x y : ℂ) •
            boundedPeierlsBondCurrent K ℏ q x y
              ((geometry.bondCoordinate sourceDirection x y : ℂ) * A))
        (∑ x : Site, ∑ y : Site,
          (geometry.bondCoordinate measuredDirection x y : ℂ) •
            ((geometry.bondCoordinate sourceDirection x y : ℂ) •
              boundedBondContact K ℏ q x y)) 0 := by
    simpa only [Finset.sum_filter, Finset.mem_univ, ↓reduceIte] using
      HasAlgebraicDerivAt.sum (Finset.univ : Finset Site)
        (fun x _ => hy x)
  have hscaled := hsum.const_smul ((2 : ℂ)⁻¹)
  simpa [boundedMixedDirectionalPeierlsCurrent,
    boundedMixedDirectionalContact, smul_smul] using hscaled

/-- Differentiating the geometric Peierls current gives the squared-coordinate contact operator. -/
theorem hasAlgebraicDerivAt_boundedDirectionalPeierlsCurrent_zero
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    HasAlgebraicDerivAt
      (boundedDirectionalPeierlsCurrent geometry direction ℏ q K)
      (boundedDirectionalContact geometry direction ℏ q K) 0 := by
  simpa only [boundedMixedDirectionalPeierlsCurrent_self,
    boundedMixedDirectionalContact_self] using
    hasAlgebraicDerivAt_boundedMixedDirectionalPeierlsCurrent_zero
      geometry direction direction ℏ q K

end
end Lattice
end Fermionic
end SecondQuantization
