import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Algebraic lattice geometry and locally finite operators

The free complex vector space on a discrete site type, its matrix units, locally finite hopping
model, bond operators, and local commutator identity do not depend on particle statistics.
The fermionic Fock-space `dGamma` implementation is a downstream specialization.
Site positions and real bond coordinates are likewise statistics-independent, and keep
their generic `LatticeGeometry` namespace and signatures below.
-/

open scoped BigOperators
attribute [local instance 100] LieRing.ofAssociativeRing

variable {Site : Type*}

/-- The canonical one-particle ket localized at a lattice site. -/
noncomputable def latticeKet (x : Site) : (Site →₀ ℂ) :=
  Finsupp.single x 1

/-- The matrix unit `|x⟩⟨y|` on the algebraic lattice one-particle space. -/
noncomputable def matrixUnit (x y : Site) :
    (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
  (Finsupp.lapply y : Module.Dual ℂ (Site →₀ ℂ)).smulRight (latticeKet x)

@[simp]
theorem matrixUnit_apply (x y : Site) (ψ : (Site →₀ ℂ)) :
    matrixUnit x y ψ = Finsupp.single x (ψ y) := by
  change (ψ y) • (Finsupp.single x 1 : Site →₀ ℂ) = Finsupp.single x (ψ y)
  exact Finsupp.smul_single_one x (ψ y)

/-- The one-particle projector `|x⟩⟨x|` onto a lattice site. -/
noncomputable def siteProjector (x : Site) :
    (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
  matrixUnit x x

@[simp]
theorem siteProjector_apply (x : Site) (ψ : (Site →₀ ℂ)) :
    siteProjector x ψ = Finsupp.single x (ψ x) := by
  exact matrixUnit_apply x x ψ

variable [DecidableEq Site]

/-- A row-and-column locally finite hopping model on an arbitrary discrete site type.

`column y` is the finitely supported vector `h |y⟩`. The finite set `incident x` contains `x` and
all sites `y` for which either matrix element `⟨x|h|y⟩` or `⟨y|h|x⟩` can be nonzero. -/
structure LocallyFiniteHopping (Site : Type*) [DecidableEq Site] where
  /-- The finitely supported image `h |y⟩` of every site ket. -/
  column : Site → (Site →₀ ℂ)
  /-- A finite set containing every site coupled to a given site in either orientation. -/
  incident : Site → Finset Site
  /-- Every site belongs to its own incident set. -/
  self_mem : ∀ x, x ∈ incident x
  /-- Both oriented matrix elements vanish outside the finite incident set. -/
  outside_incident : ∀ {x y}, y ∉ incident x → column y x = 0 ∧ column x y = 0

namespace LocallyFiniteHopping

/-- Finitely supported maps are determined by their values on all site kets. -/
private theorem linearMap_ext_latticeKet
    {Site W : Type*} [AddCommGroup W] [Module ℂ W]
    {f g : (Site →₀ ℂ) →ₗ[ℂ] W}
    (h : ∀ x, f (latticeKet x) = g (latticeKet x)) : f = g := by
  apply Finsupp.lhom_ext
  intro x c
  have hc : (Finsupp.single x c : (Site →₀ ℂ)) = c • latticeKet x :=
    (Finsupp.smul_single_one x c).symm
  rw [hc, map_smul, map_smul, h]


/-- The algebraic one-particle hopping operator determined by its finitely supported columns. -/
noncomputable def operator (K : LocallyFiniteHopping Site) :
    (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
  (Finsupp.lift ((Site →₀ ℂ)) ℂ Site) K.column

@[simp]
theorem operator_single (K : LocallyFiniteHopping Site) (x : Site) (c : ℂ) :
    K.operator (Finsupp.single x c) = c • K.column x := by
  simp [operator, Finsupp.lift_apply]

@[simp]
theorem operator_latticeKet (K : LocallyFiniteHopping Site) (x : Site) :
    K.operator (latticeKet x) = K.column x := by
  simp [latticeKet]

/-- Matrix element `⟨x|h|y⟩`, with `x` the target site and `y` the source site. -/
noncomputable def amplitude (K : LocallyFiniteHopping Site) (x y : Site) : ℂ :=
  K.column y x

@[simp]
theorem amplitude_eq (K : LocallyFiniteHopping Site) (x y : Site) :
    K.amplitude x y = K.column y x :=
  rfl

/-- A finite table of hopping amplitudes determines a locally finite hopping
operator. Its incident set contains the site and precisely the pairs with a
nonzero amplitude in at least one orientation. -/
noncomputable def ofFiniteAmplitudes [Fintype Site] (A : Site → Site → ℂ) :
    LocallyFiniteHopping Site := by
  classical
  exact {
    column := fun y => Finsupp.equivFunOnFinite.symm (fun x => A x y)
    incident := fun x => insert x (Finset.univ.filter (fun y => A x y ≠ 0 ∨ A y x ≠ 0))
    self_mem := by intro x; simp
    outside_incident := by
      intro x y hy
      have hxy : A x y = 0 := by
        by_contra h
        exact hy (by simp [h])
      have hyx : A y x = 0 := by
        by_contra h
        exact hy (by simp [h])
      simpa using And.intro hxy hyx }

@[simp]
theorem ofFiniteAmplitudes_amplitude [Fintype Site] (A : Site → Site → ℂ)
    (x y : Site) :
    (ofFiniteAmplitudes A).amplitude x y = A x y := by
  classical
  simp [ofFiniteAmplitudes, amplitude]

/-- A finite one-body operator is reconstructed by its canonical site-basis
matrix coefficients. -/
theorem operator_eq_sum_matrixUnit [Fintype Site] (K : LocallyFiniteHopping Site) :
    K.operator = ∑ x : Site, ∑ y : Site, K.amplitude x y • matrixUnit x y := by
  classical
  apply linearMap_ext_latticeKet
  intro y
  ext x
  simp [LinearMap.sum_apply, Finsupp.finsetSum_apply, matrixUnit_apply, latticeKet,
    Finsupp.single_apply]

/-- Coefficient-level Hermiticity of a lattice hopping model. -/
def HasHermitianAmplitudes (K : LocallyFiniteHopping Site) : Prop :=
  ∀ x y : Site, star (K.amplitude x y) = K.amplitude y x

/-- Outside the finite incident set, the incoming matrix element vanishes. -/
theorem amplitude_eq_zero_of_not_mem (K : LocallyFiniteHopping Site)
    {x y : Site} (hy : y ∉ K.incident x) :
    K.amplitude x y = 0 :=
  (K.outside_incident hy).1

/-- Outside the finite incident set, the outgoing matrix element also vanishes. -/
theorem amplitude_swap_eq_zero_of_not_mem (K : LocallyFiniteHopping Site)
    {x y : Site} (hy : y ∉ K.incident x) :
    K.amplitude y x = 0 :=
  (K.outside_incident hy).2

/-- The one-particle operator entering the oriented bond current from `x` to `y`:

`h_xy |x⟩⟨y| - h_yx |y⟩⟨x|`.
-/
noncomputable def bondOperator (K : LocallyFiniteHopping Site) (x y : Site) :
    (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
  K.amplitude x y • matrixUnit x y - K.amplitude y x • matrixUnit y x

/-- Reversing the bond orientation negates the one-particle bond operator. -/
theorem bondOperator_swap (K : LocallyFiniteHopping Site) (x y : Site) :
    K.bondOperator y x = -K.bondOperator x y := by
  simp [bondOperator]

/-- The local one-particle commutator is the negative finite sum of oriented bond operators. -/
theorem lie_siteProjector (K : LocallyFiniteHopping Site) (x : Site) :
    ⁅K.operator, siteProjector x⁆ =
      -∑ y ∈ K.incident x, K.bondOperator x y := by
  classical
  have hcolumn (source : Site) :
      K.column source =
        ∑ target ∈ K.incident source,
          Finsupp.single target (K.amplitude target source) := by
    ext z
    rw [Finsupp.finsetSum_apply]
    by_cases hz : z ∈ K.incident source
    · rw [Finset.sum_eq_single z]
      · simp [amplitude]
      · intro y _ hyz
        simp [hyz]
      · intro hnot
        exact (hnot hz).elim
    · have hzero : K.column source z = 0 := (K.outside_incident hz).2
      rw [Finset.sum_eq_zero]
      · exact hzero
      · intro y hy
        have hyz : y ≠ z := by
          intro h
          subst y
          exact hz hy
        simp [hyz]
  have hopP :
      K.operator.comp (siteProjector x) =
        ∑ y ∈ K.incident x, K.amplitude y x • matrixUnit y x := by
    apply linearMap_ext_latticeKet
    intro z
    change K.operator.comp (siteProjector x) (Finsupp.single z 1) =
      (∑ y ∈ K.incident x, K.amplitude y x • matrixUnit y x) (Finsupp.single z 1)
    by_cases hzx : z = x
    · subst z
      simp only [LinearMap.comp_apply, siteProjector_apply, Finsupp.single_eq_same]
      rw [LinearMap.sum_apply]
      change K.operator (Finsupp.single x 1) =
        ∑ y ∈ K.incident x,
          (K.amplitude y x • matrixUnit y x) (Finsupp.single x 1)
      rw [K.operator_single, hcolumn x]
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro y _
      simp [mul_comm]
    · have hxz : x ≠ z := Ne.symm hzx
      simp [LinearMap.comp_apply, hxz, LinearMap.sum_apply]
  have hPop :
      (siteProjector x).comp K.operator =
        ∑ y ∈ K.incident x, K.amplitude x y • matrixUnit x y := by
    apply linearMap_ext_latticeKet
    intro z
    change (siteProjector x).comp K.operator (Finsupp.single z 1) =
      (∑ y ∈ K.incident x, K.amplitude x y • matrixUnit x y) (Finsupp.single z 1)
    simp only [LinearMap.comp_apply, operator_single, siteProjector_apply, Finsupp.smul_apply]
    rw [LinearMap.sum_apply]
    change Finsupp.single x ((1 : ℂ) • K.column z x) =
      ∑ y ∈ K.incident x,
        (K.amplitude x y • matrixUnit x y) (Finsupp.single z 1)
    by_cases hz : z ∈ K.incident x
    · rw [Finset.sum_eq_single z]
      · simp [amplitude, smul_eq_mul, mul_comm]
      · intro y _ hyz
        simp [hyz]
      · intro hnot
        exact (hnot hz).elim
    · have hzero : K.column z x = 0 := (K.outside_incident hz).1
      rw [Finset.sum_eq_zero]
      · simp [hzero]
      · intro y hy
        have hyz : y ≠ z := by
          intro h
          subst y
          exact hz hy
        simp [hyz]
  simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp,
    hopP, hPop, bondOperator, Finset.sum_sub_distrib]
  abel

end LocallyFiniteHopping

/-! ## Site geometry and bond coordinates -/

/-- Positions of lattice sites in a real vector space. -/
structure LatticeGeometry (Site E : Type*) where
  /-- Position of each site. -/
  position : Site → E

namespace LatticeGeometry

variable {Site E : Type*} [AddCommGroup E]

/-- Oriented displacement from `x` to `y`. -/
def bondDisplacement (geometry : LatticeGeometry Site E) (x y : Site) : E :=
  geometry.position y - geometry.position x

variable [Module ℝ E]

/-- Scalar bond coordinate measured by a real linear functional. -/
def bondCoordinate (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (x y : Site) : ℝ :=
  direction (geometry.bondDisplacement x y)

variable [Fintype Site]

/-- The finite real-space position component acts diagonally in the site basis.
The coordinate is supplied by the existing lattice geometry, not by a momentum label. -/
noncomputable def directionalPosition (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) :
    (Site →₀ ℂ) →ₗ[ℂ] (Site →₀ ℂ) :=
  ∑ x : Site, (direction (geometry.position x) : ℂ) • siteProjector x

/-- Position multiplies each site amplitude by its real spatial coordinate. -/
@[simp]
theorem directionalPosition_apply (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (ψ : Site →₀ ℂ) (x : Site) :
    geometry.directionalPosition direction ψ x =
      (direction (geometry.position x) : ℂ) * ψ x := by
  classical
  rw [directionalPosition, LinearMap.sum_apply, Finsupp.finsetSum_apply,
    Finset.sum_eq_single x]
  · rw [LinearMap.smul_apply, Finsupp.smul_apply, siteProjector_apply,
      Finsupp.single_eq_same, smul_eq_mul]
  · intro y _ hy
    have hz : siteProjector y ψ x = 0 := by
      rw [siteProjector_apply]
      exact Finsupp.single_eq_of_ne (Ne.symm hy)
    rw [LinearMap.smul_apply, Finsupp.smul_apply, hz, smul_zero]
  · simp

/-- Every localized site ket is an eigenvector of the finite position operator. -/
theorem directionalPosition_latticeKet (geometry : LatticeGeometry Site E)
    (direction : E →ₗ[ℝ] ℝ) (y : Site) :
    geometry.directionalPosition direction (latticeKet y) =
      (direction (geometry.position y) : ℂ) • latticeKet y := by
  ext x
  rw [directionalPosition_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  by_cases h : x = y
  · subst x
    rfl
  · have hz : latticeKet y x = 0 := Finsupp.single_eq_of_ne h
    rw [hz, mul_zero, mul_zero]

/-- The position commutator of the actual hopping operator has the oriented
bond displacement as its matrix-element multiplier:
`[H,X]_{xy} = (X_y - X_x) H_{xy}`.
Multiplying by `i/ℏ` gives the real-space Heisenberg velocity without
postulating a momentum-derivative/position identity. -/
theorem lie_directionalPosition_latticeKet [DecidableEq Site]
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) (x y : Site) :
    ⁅K.operator, geometry.directionalPosition direction⁆ (latticeKet y) x =
      (geometry.bondCoordinate direction x y : ℂ) * K.amplitude x y := by
  change (K.operator (geometry.directionalPosition direction (latticeKet y)) -
    geometry.directionalPosition direction (K.operator (latticeKet y))) x = _
  rw [Finsupp.sub_apply, directionalPosition_latticeKet, map_smul,
    Finsupp.smul_apply, directionalPosition_apply, K.operator_latticeKet]
  change (direction (geometry.position y) : ℂ) * K.amplitude x y -
      (direction (geometry.position x) : ℂ) * K.amplitude x y = _
  rw [bondCoordinate, bondDisplacement, map_sub, Complex.ofReal_sub, sub_mul]

/-- The position commutator equals the displacement-weighted sum of oriented
bond operators. The half removes the double counting of opposite orientations. -/
theorem lie_directionalPosition_eq_bondSum [DecidableEq Site]
    (geometry : LatticeGeometry Site E) (direction : E →ₗ[ℝ] ℝ)
    (K : LocallyFiniteHopping Site) :
    ⁅K.operator, geometry.directionalPosition direction⁆ =
      (2 : ℂ)⁻¹ • ∑ x : Site, ∑ y : Site,
        (geometry.bondCoordinate direction x y : ℂ) • K.bondOperator x y := by
  let r : Site → ℂ := fun x => (direction (geometry.position x) : ℂ)
  let A := ∑ x : Site, ∑ y : Site, r x • K.bondOperator x y
  have hlocal (x : Site) :
      ⁅K.operator, siteProjector x⁆ = -∑ y : Site, K.bondOperator x y := by
    rw [K.lie_siteProjector]
    congr 1
    apply Finset.sum_subset (Finset.subset_univ _)
    intro y _ hy
    rw [LocallyFiniteHopping.bondOperator,
      K.amplitude_eq_zero_of_not_mem hy, K.amplitude_swap_eq_zero_of_not_mem hy]
    simp
  have hcomm : ⁅K.operator, geometry.directionalPosition direction⁆ = -A := by
    change (LieAlgebra.ad ℂ (Module.End ℂ (Site →₀ ℂ)) K.operator)
      (∑ x : Site, r x • siteProjector x) = -A
    rw [map_sum]
    simp only [map_smul]
    change (∑ x : Site, r x • ⁅K.operator, siteProjector x⁆) = -A
    simp only [hlocal, smul_neg, Finset.smul_sum, Finset.sum_neg_distrib, A]
  have hswap : (∑ x : Site, ∑ y : Site, r y • K.bondOperator x y) = -A := by
    calc
      _ = ∑ x : Site, ∑ y : Site, r x • K.bondOperator y x := Finset.sum_comm
      _ = ∑ x : Site, ∑ y : Site, -(r x • K.bondOperator x y) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        rw [K.bondOperator_swap x y, smul_neg]
      _ = -A := by simp only [Finset.sum_neg_distrib, A]
  have hweight (x y : Site) :
      (geometry.bondCoordinate direction x y : ℂ) = r y - r x := by
    simp only [bondCoordinate, bondDisplacement, map_sub, Complex.ofReal_sub, r]
  rw [hcomm]
  simp only [hweight, sub_smul, Finset.sum_sub_distrib, hswap]
  change -A = (2 : ℂ)⁻¹ • (-A - A)
  rw [sub_eq_add_neg, ← two_smul ℂ (-A), smul_smul]
  norm_num

end LatticeGeometry
