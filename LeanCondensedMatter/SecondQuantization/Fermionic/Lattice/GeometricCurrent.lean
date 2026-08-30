import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.HermitianBondCurrent

set_option linter.style.header false

/-!
# Geometric aggregation of finite-lattice currents

A bond current becomes a spatial current component only after assigning positions to lattice sites
and selecting a measurement direction. For a real vector space `E`, site positions `rₓ : E`, and a
real linear functional `direction : E →ₗ[ℝ] ℝ`, the oriented bond coordinate is

```text
w_xy = direction (r_y - r_x).
```

It is antisymmetric under orientation reversal. The finite-lattice current component is the
half-sum over directed site pairs

```text
J_direction = 1/2 ∑ₓ ∑ᵧ w_xy J_xy.
```

For a measured current direction `i` and a uniform source direction `j`, the chain rule gives the
mixed geometric contact operator

```text
C_ij = 1/2 ∑ₓ ∑ᵧ w_i,xy w_j,xy C_xy.
```

The historical one-direction contact is the diagonal specialization `C_ii`. The construction
remains at finite volume and does not take frequency, adiabatic, thermodynamic, or DC limits.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

open scoped BigOperators

noncomputable section

/-- Positions of lattice sites in a real vector space. -/
structure LatticeGeometry (Site E : Type*) where
  /-- Position of each site. -/
  position : Site → E

namespace LatticeGeometry

variable {Site E : Type*} [AddCommGroup E]

/-- Oriented displacement from `x` to `y`. -/
def bondDisplacement (geometry : LatticeGeometry Site E) (x y : Site) : E :=
  geometry.position y - geometry.position x

/-- Reversing a bond reverses its displacement. -/
theorem bondDisplacement_swap (geometry : LatticeGeometry Site E) (x y : Site) :
    geometry.bondDisplacement y x = -geometry.bondDisplacement x y := by
  unfold bondDisplacement
  abel

variable [Module ℝ E]

/-- Scalar bond coordinate measured by a real linear functional. -/
def bondCoordinate (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x y : Site) : ℝ :=
  direction (geometry.bondDisplacement x y)

/-- Reversing a bond negates its scalar coordinate. -/
theorem bondCoordinate_swap (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x y : Site) :
    geometry.bondCoordinate direction y x =
      -geometry.bondCoordinate direction x y := by
  unfold bondCoordinate
  rw [bondDisplacement_swap, map_neg]

@[simp]
theorem bondCoordinate_self (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x : Site) :
    geometry.bondCoordinate direction x x = 0 := by
  unfold bondCoordinate bondDisplacement
  simp

end LatticeGeometry

variable {Site E : Type*}
variable [LinearOrder Site] [Fintype Site]
variable [AddCommGroup E] [Module ℝ E]

/-- Spatial current component obtained by summing all directed bond currents with their oriented
geometric coordinates. The factor `1/2` removes the duplicate orientation in the all-pairs sum. -/
noncomputable def boundedDirectionalCurrent
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  (2 : ℂ)⁻¹ •
    ∑ x : Site, ∑ y : Site,
      (geometry.bondCoordinate direction x y : ℂ) •
        boundedBondCurrent ℏ q K x y

/-- Mixed geometric contact operator for a current measured along `measuredDirection` under a
uniform Peierls source along `sourceDirection`. Each bond carries one coordinate factor from the
measured current and one from differentiating the Peierls phase with respect to the source. -/
noncomputable def boundedMixedDirectionalContact
    (geometry : LatticeGeometry Site E)
    (measuredDirection sourceDirection : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  (2 : ℂ)⁻¹ •
    ∑ x : Site, ∑ y : Site,
      ((geometry.bondCoordinate measuredDirection x y *
        geometry.bondCoordinate sourceDirection x y : ℝ) : ℂ) •
        boundedBondContact K ℏ q x y

/-- Geometric contact operator for a uniform source in the selected direction. This is the
diagonal specialization of `boundedMixedDirectionalContact`. -/
noncomputable def boundedDirectionalContact
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  (2 : ℂ)⁻¹ •
    ∑ x : Site, ∑ y : Site,
      ((geometry.bondCoordinate direction x y) ^ 2 : ℂ) •
        boundedBondContact K ℏ q x y

/-- The mixed contact reduces to the historical directional contact when the measured and source
directions coincide. -/
@[simp]
theorem boundedMixedDirectionalContact_self
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedMixedDirectionalContact geometry direction direction ℏ q K =
      boundedDirectionalContact geometry direction ℏ q K := by
  simp [boundedMixedDirectionalContact, boundedDirectionalContact, pow_two]

/-- Hermitian hopping and real physical parameters make every geometric current component
self-adjoint. -/
theorem isSelfAdjoint_boundedDirectionalCurrent
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (hK : K.HasHermitianAmplitudes)
    (ℏ q : ℝ) :
    IsSelfAdjoint
      (boundedDirectionalCurrent geometry direction (ℏ : ℂ) (q : ℂ) K) := by
  have hJ : ∀ x y : Site,
      star (boundedBondCurrent (ℏ : ℂ) (q : ℂ) K x y) =
        boundedBondCurrent (ℏ : ℂ) (q : ℂ) K x y :=
    fun x y => (isSelfAdjoint_boundedBondCurrent_ofReal K hK ℏ q x y).star_eq
  rw [isSelfAdjoint_iff]
  unfold boundedDirectionalCurrent
  rw [star_smul]
  have hhalf : star ((2 : ℂ)⁻¹) = (2 : ℂ)⁻¹ := by norm_num
  rw [hhalf]
  congr 1
  change
    star (Finset.univ.sum (fun x => Finset.univ.sum (fun y =>
      (geometry.bondCoordinate direction x y : ℂ) •
        boundedBondCurrent (ℏ : ℂ) (q : ℂ) K x y))) =
      Finset.univ.sum (fun x => Finset.univ.sum (fun y =>
        (geometry.bondCoordinate direction x y : ℂ) •
          boundedBondCurrent (ℏ : ℂ) (q : ℂ) K x y))
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [star_smul, hJ x y]
  have hw :
      star (geometry.bondCoordinate direction x y : ℂ) =
        (geometry.bondCoordinate direction x y : ℂ) := by
    simp
  rw [hw]

end
end Lattice
end Fermionic
end SecondQuantization
