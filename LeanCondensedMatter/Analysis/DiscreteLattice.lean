import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Tactic.Abel

set_option linter.style.header false

/-!
# Algebraic locally finite lattice operators

The free complex vector space on a discrete site type, its matrix units, locally finite hopping
model, bond operators, and local commutator identity do not depend on particle statistics.
The fermionic Fock-space `dGamma` implementation is a downstream specialization.
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

