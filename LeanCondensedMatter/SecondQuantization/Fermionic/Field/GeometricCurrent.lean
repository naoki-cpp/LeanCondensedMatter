import LeanCondensedMatter.SecondQuantization.Fermionic.Field.HermitianBondCurrent

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
namespace Field

open scoped BigOperators

noncomputable section

/-- Positions of lattice sites in a real vector space. -/
structure LatticeGeometry (Site E : Type*) where
  /-- Position of each site. -/
  position : Site → E

namespace LatticeGeometry

variable {Site E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Oriented displacement from `x` to `y`. -/
def bondDisplacement (geometry : LatticeGeometry Site E) (x y : Site) : E :=
  geometry.position y - geometry.position x

/-- Scalar bond coordinate measured by a real linear functional. -/
def bondCoordinate (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x y : Site) : ℝ :=
  direction (geometry.bondDisplacement x y)

@[simp]
theorem bondDisplacement_swap (geometry : LatticeGeometry Site E) (x y : Site) :
    geometry.bondDisplacement y x = -geometry.bondDisplacement x y := by
  simp [bondDisplacement, sub_eq_add_neg, add_comm]

@[simp]
theorem bondCoordinate_swap (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x y : Site) :
    geometry.bondCoordinate direction y x =
      -geometry.bondCoordinate direction x y := by
  simp [bondCoordinate]

@[simp]
theorem bondCoordinate_self (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x : Site) :
    geometry.bondCoordinate direction x x = 0 := by
  simp [bondCoordinate, bondDisplacement]

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

/-- Geometric contact operator for a uniform source in the selected direction. The squared bond
coordinate is the chain-rule factor from differentiating the measured current after the Peierls
phase has already been differentiated once. -/
noncomputable def boundedDirectionalContact
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (ℏ q : ℂ) (K : LocallyFiniteHopping Site) :
    FiniteLatticeHilbertFock Site →L[ℂ] FiniteLatticeHilbertFock Site :=
  (2 : ℂ)⁻¹ •
    ∑ x : Site, ∑ y : Site,
      ((geometry.bondCoordinate direction x y) ^ 2 : ℂ) •
        boundedBondContact K ℏ q x y

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
  simp [boundedDirectionalCurrent, hJ]

/-- Retarded response of a geometric current component with the source-dependent geometric contact
term retained. Current self-adjointness is derived from Hermitian hopping and the real physical
charge rather than supplied externally. -/
theorem hasDerivAt_boundedDirectionalCurrentExpectation_zero_of_bound_retarded
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock Site))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock Site))
    (f : ℝ → ℝ)
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (hK : K.HasHermitianAmplitudes) (q : ℝ)
    {β M t : ℝ} (hM : 0 ≤ M)
    (hV : ∀ s ∈ Set.Icc (0 : ℝ) β,
      ‖QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)) s‖ ≤ M)
    (ht : t ∈ Set.Icc (0 : ℝ) β)
    (hInt : IntervalIntegrable
      (QuantumTheory.LinearResponse.timeDependentInteractionPerturbation system
        (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)))
      MeasureTheory.volume 0 t) :
    HasDerivAt
      (fun lam : ℝ =>
        QuantumTheory.LinearResponse.affinePerturbedExpectation system expectation
          (QuantumTheory.LinearResponse.sourceCoupledPerturbation f
            (boundedDirectionalCurrent geometry direction
              (system.hbar : ℂ) (q : ℂ) K))
          (boundedDirectionalCurrent geometry direction
            (system.hbar : ℂ) (q : ℂ) K)
          ((f t : ℂ) •
            boundedDirectionalContact geometry direction
              (system.hbar : ℂ) (q : ℂ) K) lam t)
      ((∫ s in (0 : ℝ)..t,
          (f s : ℂ) *
            QuantumTheory.LinearResponse.retardedSusceptibility system expectation
              (boundedDirectionalCurrent geometry direction
                (system.hbar : ℂ) (q : ℂ) K)
              (boundedDirectionalCurrent geometry direction
                (system.hbar : ℂ) (q : ℂ) K) t s) +
        expectation
          (QuantumTheory.LinearResponse.heisenbergEvolution system
            ((f t : ℂ) •
              boundedDirectionalContact geometry direction
                (system.hbar : ℂ) (q : ℂ) K) t))
      0 := by
  exact
    QuantumTheory.LinearResponse.hasDerivAt_affineSourceCoupledExpectation_zero_of_bound_retarded
      system expectation f
      (isSelfAdjoint_boundedDirectionalCurrent geometry direction K hK system.hbar q)
      (boundedDirectionalCurrent geometry direction
        (system.hbar : ℂ) (q : ℂ) K)
      ((f t : ℂ) •
        boundedDirectionalContact geometry direction
          (system.hbar : ℂ) (q : ℂ) K)
      hM hV ht hInt

end
end Field
end Fermionic
end SecondQuantization
