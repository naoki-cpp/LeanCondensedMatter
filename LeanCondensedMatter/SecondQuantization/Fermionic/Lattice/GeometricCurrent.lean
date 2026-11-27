import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.HermitianBondCurrent
import LeanCondensedMatter.Analysis.DiscreteLattice

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

For a uniform source in that direction, the chain rule gives one additional factor of `w_xy` in
the explicit current derivative, so the geometric contact operator is

```text
C_direction = 1/2 ∑ₓ ∑ᵧ w_xy² C_xy.
```

The final theorem combines the retarded response of the aggregated current with this geometric
contact term. The construction remains at finite volume and does not take frequency, adiabatic,
thermodynamic, or DC limits.
-/

namespace SecondQuantization
namespace Fermionic
namespace Lattice

open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

noncomputable section



variable {Site E : Type*}
variable [AddCommGroup E] [Module ℝ E]

/-- Under affine site relabeling the translation cancels from each displacement.
The transformed directional functional is a pullback by the linear part. -/
private theorem bondCoordinate_comp_sitePermutation
    (geometry : LatticeGeometry Site E) (e : Equiv.Perm Site)
    (L : E →ₗ[ℝ] E) (a : E)
    (hposition : ∀ x, geometry.position (e x) = L (geometry.position x) + a)
    (direction : E →ₗ[ℝ] ℝ) (x y : Site) :
    geometry.bondCoordinate (direction.comp L) x y =
      geometry.bondCoordinate direction (e x) (e y) := by
  simp [LatticeGeometry.bondCoordinate, LatticeGeometry.bondDisplacement,
    LinearMap.comp_apply, hposition, map_sub]

variable [LinearOrder Site] [Fintype Site]

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

/-- The existing geometric charge-current observable is precisely the bounded
second quantization of the position commutator with Peierls normalization.
This identifies the bond-sum and position-derived currents without assuming
translation symmetry or an identification with a momentum derivative. -/
theorem boundedDirectionalCurrent_eq_positionCommutator
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedDirectionalCurrent geometry direction ℏ q K =
      QuantumTheory.PeierlsPhase.peierlsCoupling ℏ q •
        boundedOneBodyOperator ⁅K.operator, geometry.directionalPosition direction⁆ := by
  rw [geometry.lie_directionalPosition_eq_bondSum direction K]
  let D := (boundedOneBodyOperator (Site := Site)).toLinearMap
  change (2 : ℂ)⁻¹ •
      (∑ x : Site, ∑ y : Site,
        (geometry.bondCoordinate direction x y : ℂ) • boundedBondCurrent ℏ q K x y) =
    QuantumTheory.PeierlsPhase.peierlsCoupling ℏ q •
      D ((2 : ℂ)⁻¹ • ∑ x : Site, ∑ y : Site,
        (geometry.bondCoordinate direction x y : ℂ) • K.bondOperator x y)
  rw [map_smul, smul_comm (QuantumTheory.PeierlsPhase.peierlsCoupling ℏ q)]
  congr 1
  simp only [map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [smul_comm (QuantumTheory.PeierlsPhase.peierlsCoupling ℏ q)]
  congr 1
  change boundedBondCurrent ℏ q K x y =
    QuantumTheory.PeierlsPhase.peierlsCoupling ℏ q •
      boundedOneBodyOperator (K.bondOperator x y)
  rw [← boundedOneBodyOperator_oneParticleBondCurrent K ℏ q x y]
  change D (QuantumTheory.PeierlsPhase.peierlsCoupling ℏ q • K.bondOperator x y) = _
  exact D.map_smul _ _

/-- Mixed geometric contact operator: one bond coordinate comes from the measured
current, the other from differentiation with respect to the source direction. -/
noncomputable def boundedMixedDirectionalContact
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  (2 : ℂ)⁻¹ •
    ∑ x : Site, ∑ y : Site,
      ((geometry.bondCoordinate measured x y : ℂ) *
        (geometry.bondCoordinate source x y : ℂ)) • boundedBondContact K ℏ q x y

/-- The original same-direction contact is the diagonal mixed contact. -/
noncomputable def boundedDirectionalContact
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  boundedMixedDirectionalContact geometry direction direction ℏ q K

/-- Mixed Peierls contacts are symmetric in their geometric directions. -/
theorem boundedMixedDirectionalContact_swap
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedMixedDirectionalContact geometry measured source ℏ q K =
      boundedMixedDirectionalContact geometry source measured ℏ q K := by
  unfold boundedMixedDirectionalContact
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_comm]


/-- A weighted geometric bond sum is linear in its real direction. -/
private def directionalBondSumLinearMap
    (geometry : LatticeGeometry Site E)
    (weight : Site → Site → (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site)) :
    (E →ₗ[ℝ] ℝ) →ₗ[ℝ] (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) :=
  (2 : ℂ)⁻¹ • ∑ x : Site, ∑ y : Site,
    { toFun := fun d => (geometry.bondCoordinate d x y : ℂ) • weight x y
      map_add' := by
        intro d e
        simp only [LatticeGeometry.bondCoordinate, LinearMap.add_apply, Complex.ofReal_add, add_smul]
      map_smul' := by
        intro r d
        simp only [LatticeGeometry.bondCoordinate, LinearMap.smul_apply, smul_eq_mul,
          Complex.ofReal_mul, mul_smul, RingHom.id_apply,
          RCLike.real_smul_eq_coe_smul (K := ℂ)]
        rfl }

omit [LinearOrder Site] in
private theorem directionalBondSumLinearMap_apply
    (geometry : LatticeGeometry Site E)
    (weight : Site → Site → (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site))
    (d : E →ₗ[ℝ] ℝ) :
    directionalBondSumLinearMap geometry weight d =
      (2 : ℂ)⁻¹ • ∑ x : Site, ∑ y : Site,
        (geometry.bondCoordinate d x y : ℂ) • weight x y := by
  simp only [directionalBondSumLinearMap, LinearMap.smul_apply, LinearMap.sum_apply]
  rfl

/-- The spatial current transforms linearly under finite real direction mixing. -/
theorem boundedDirectionalCurrent_sum
    {I : Type*} [Fintype I]
    (geometry : LatticeGeometry Site E) (direction : I → E →ₗ[ℝ] ℝ) (r : I → ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedDirectionalCurrent geometry (∑ i, r i • direction i) ℏ q K =
      ∑ i, (r i : ℂ) • boundedDirectionalCurrent geometry (direction i) ℏ q K := by
  let D := directionalBondSumLinearMap geometry (boundedBondCurrent ℏ q K)
  have hD (d : E →ₗ[ℝ] ℝ) :
      D d = boundedDirectionalCurrent geometry d ℏ q K :=
    directionalBondSumLinearMap_apply geometry (boundedBondCurrent ℏ q K) d
  simp_rw [← hD]
  rw [map_sum D]
  apply Finset.sum_congr rfl
  intro i _
  calc
    D (r i • direction i) = r i • D (direction i) := map_smul D _ _
    _ = (r i : ℂ) • D (direction i) :=
      RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

/-- The mixed contact is linear in its measured direction. -/
theorem boundedMixedDirectionalContact_sum_left
    {I : Type*} [Fintype I]
    (geometry : LatticeGeometry Site E) (direction : I → E →ₗ[ℝ] ℝ) (r : I → ℝ)
    (source : E →ₗ[ℝ] ℝ) (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedMixedDirectionalContact geometry (∑ i, r i • direction i) source ℏ q K =
      ∑ i, (r i : ℂ) • boundedMixedDirectionalContact geometry (direction i) source ℏ q K := by
  let D := directionalBondSumLinearMap geometry (fun x y =>
    (geometry.bondCoordinate source x y : ℂ) • boundedBondContact K ℏ q x y)
  have hD (d : E →ₗ[ℝ] ℝ) :
      D d = boundedMixedDirectionalContact geometry d source ℏ q K := by
    dsimp only [D]
    rw [directionalBondSumLinearMap_apply]
    simp only [boundedMixedDirectionalContact, mul_smul]
  simp_rw [← hD]
  rw [map_sum D]
  apply Finset.sum_congr rfl
  intro i _
  calc
    D (r i • direction i) = r i • D (direction i) := map_smul D _ _
    _ = (r i : ℂ) • D (direction i) :=
      RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

/-- Both directions of the contact mix independently, with the product of the coefficients. -/
theorem boundedMixedDirectionalContact_sum
    {I J : Type*} [Fintype I] [Fintype J]
    (geometry : LatticeGeometry Site E) (measured : I → E →ₗ[ℝ] ℝ)
    (source : J → E →ₗ[ℝ] ℝ) (r : I → ℝ) (s : J → ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    boundedMixedDirectionalContact geometry (∑ i, r i • measured i)
        (∑ j, s j • source j) ℏ q K =
      ∑ i, ∑ j, ((r i : ℂ) * (s j : ℂ)) •
        boundedMixedDirectionalContact geometry (measured i) (source j) ℏ q K := by
  rw [boundedMixedDirectionalContact_sum_left]
  apply Finset.sum_congr rfl
  intro i _
  rw [boundedMixedDirectionalContact_swap geometry (measured i),
    boundedMixedDirectionalContact_sum_left]
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [boundedMixedDirectionalContact_swap geometry (source j) (measured i)]

/-- A hopping-preserving affine permutation transports the physical directional
current by the pullback of the measurement direction. The only operator-level
assumption is the implementation of site relabeling on bounded matrix units. -/
theorem boundedDirectionalCurrent_siteCovariance
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (e : Equiv.Perm Site)
    (L : E →ₗ[ℝ] E) (a : E)
    (hposition : ∀ x, geometry.position (e x) = L (geometry.position x) + a)
    (Φ : (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site))
    (hK : ∀ x y, K.amplitude (e x) (e y) = K.amplitude x y)
    (hUnit : ∀ x y, Φ (boundedOneBodyOperator (matrixUnit x y)) =
      boundedOneBodyOperator (matrixUnit (e x) (e y))) :
    Φ (boundedDirectionalCurrent geometry (direction.comp L) ℏ q K) =
      boundedDirectionalCurrent geometry direction ℏ q K := by
  unfold boundedDirectionalCurrent
  simp only [map_smul, map_sum, boundedBondCurrent_siteCovariance K ℏ q e Φ hK hUnit]
  congr 1
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  refine Fintype.sum_equiv e _ _ ?_
  intro y
  rw [bondCoordinate_comp_sitePermutation geometry e L a hposition direction x y]

/-- The mixed Peierls contact transforms by the pullback in both directions.
Both geometric weights are transported by the same site permutation, while
the bond contact covariance follows from the hopping amplitudes and matrix units. -/
theorem boundedMixedDirectionalContact_siteCovariance
    (geometry : LatticeGeometry Site E) (measured source : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (e : Equiv.Perm Site)
    (L : E →ₗ[ℝ] E) (a : E)
    (hposition : ∀ x, geometry.position (e x) = L (geometry.position x) + a)
    (Φ : (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site) →ₗ[ℂ]
      (FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site))
    (hK : ∀ x y, K.amplitude (e x) (e y) = K.amplitude x y)
    (hUnit : ∀ x y, Φ (boundedOneBodyOperator (matrixUnit x y)) =
      boundedOneBodyOperator (matrixUnit (e x) (e y))) :
    Φ (boundedMixedDirectionalContact geometry (measured.comp L) (source.comp L) ℏ q K) =
      boundedMixedDirectionalContact geometry measured source ℏ q K := by
  unfold boundedMixedDirectionalContact
  simp only [map_smul, map_sum, boundedBondContact_siteCovariance K ℏ q e Φ hK hUnit]
  congr 1
  refine Fintype.sum_equiv e _ _ ?_
  intro x
  refine Fintype.sum_equiv e _ _ ?_
  intro y
  rw [bondCoordinate_comp_sitePermutation geometry e L a hposition measured x y,
    bondCoordinate_comp_sitePermutation geometry e L a hposition source x y]

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
