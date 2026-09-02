import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock.SecondQuantizationCommutator
import Mathlib.LinearAlgebra.Finsupp.LSum

set_option linter.style.header false

/-!
# Locally finite discrete-lattice fermionic currents

For an arbitrary site type `Site`, the algebraic one-particle space is the free complex vector space
`Site →₀ ℂ`. A hopping model is specified by the finitely supported image of every site ket together
with a finite incident set at every site that contains all incoming and outgoing nonzero matrix
elements.

Thus the lattice may be infinite (for example `ℤ`, `ℤ × ℤ`, or the vertices of an arbitrary locally
finite graph). Only the hopping neighborhood of each individual site is finite. This layer remains
algebraic; an `ℓ²` completion and boundedness or domain statements are separate analytic concerns.
-/

open scoped BigOperators

namespace SecondQuantization
namespace Fermionic
namespace Lattice

/-- Algebraic one-particle states on an arbitrary discrete lattice. Every vector has finite support,
but the site type itself need not be finite. -/
abbrev LatticeState (Site : Type*) := Common.AlgebraicFock Site

private theorem linearMap_finsetSum_apply
    {ι V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module ℂ V] [Module ℂ W]
    (s : Finset ι) (F : ι → V →ₗ[ℂ] W) (v : V) :
    (∑ i ∈ s, F i) v = ∑ i ∈ s, F i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih]

variable {Site : Type*}

/-- The canonical one-particle ket localized at a lattice site. -/
noncomputable def latticeKet (x : Site) : LatticeState Site :=
  Finsupp.single x 1

/-- The matrix unit `|x⟩⟨y|` on the algebraic lattice one-particle space. -/
noncomputable def matrixUnit (x y : Site) :
    LatticeState Site →ₗ[ℂ] LatticeState Site :=
  (Finsupp.lsingle x : ℂ →ₗ[ℂ] LatticeState Site).comp
    (Finsupp.lapply y : LatticeState Site →ₗ[ℂ] ℂ)

@[simp]
theorem matrixUnit_apply (x y : Site) (ψ : LatticeState Site) :
    matrixUnit x y ψ = Finsupp.single x (ψ y) := by
  rfl

/-- A matrix unit sends its source-site ket to its target-site ket. -/
theorem matrixUnit_single_same (x y : Site) (c : ℂ) :
    matrixUnit x y (Finsupp.single y c) = Finsupp.single x c := by
  classical
  simp [matrixUnit]

/-- A matrix unit kills a ket localized away from its source site. -/
theorem matrixUnit_single_of_ne (x y z : Site) (c : ℂ) (h : y ≠ z) :
    matrixUnit x y (Finsupp.single z c) = 0 := by
  classical
  simp [matrixUnit, h]

/-- The one-particle projector `|x⟩⟨x|` onto a lattice site. -/
noncomputable def siteProjector (x : Site) :
    LatticeState Site →ₗ[ℂ] LatticeState Site :=
  matrixUnit x x

@[simp]
theorem siteProjector_apply (x : Site) (ψ : LatticeState Site) :
    siteProjector x ψ = Finsupp.single x (ψ x) := by
  rfl

variable [DecidableEq Site]

/-- A row-and-column locally finite hopping model on an arbitrary discrete site type.

`column y` is the finitely supported vector `h |y⟩`. The finite set `incident x` contains `x` and
all sites `y` for which either matrix element `⟨x|h|y⟩` or `⟨y|h|x⟩` can be nonzero. -/
structure LocallyFiniteHopping (Site : Type*) [DecidableEq Site] where
  /-- The finitely supported image `h |y⟩` of every site ket. -/
  column : Site → LatticeState Site
  /-- A finite set containing every site coupled to a given site in either orientation. -/
  incident : Site → Finset Site
  /-- Every site belongs to its own incident set. -/
  self_mem : ∀ x, x ∈ incident x
  /-- Both oriented matrix elements vanish outside the finite incident set. -/
  outside_incident : ∀ {x y}, y ∉ incident x → column y x = 0 ∧ column x y = 0

namespace LocallyFiniteHopping

/-- The algebraic one-particle hopping operator determined by its finitely supported columns. -/
noncomputable def operator (K : LocallyFiniteHopping Site) :
    LatticeState Site →ₗ[ℂ] LatticeState Site :=
  (Finsupp.lift (LatticeState Site) ℂ Site) K.column

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

/-- Reconstruct one hopping column from the finite incident set at its source site. -/
theorem column_eq_sum_single (K : LocallyFiniteHopping Site) (x : Site) :
    K.column x =
      ∑ y ∈ K.incident x, Finsupp.single y (K.amplitude y x) := by
  classical
  ext z
  rw [Finsupp.finsetSum_apply]
  by_cases hz : z ∈ K.incident x
  · rw [Finset.sum_eq_single z]
    · simp [amplitude]
    · intro y _ hyz
      simp [hyz]
    · intro hnot
      exact (hnot hz).elim
  · have hzero : K.column x z = 0 := (K.outside_incident hz).2
    rw [Finset.sum_eq_zero]
    · exact hzero
    · intro y hy
      have hyz : y ≠ z := by
        intro h
        subst y
        exact hz hy
      simp [hyz]

/-- The one-particle operator entering the oriented bond current from `x` to `y`:

`h_xy |x⟩⟨y| - h_yx |y⟩⟨x|`.
-/
noncomputable def bondOperator (K : LocallyFiniteHopping Site) (x y : Site) :
    LatticeState Site →ₗ[ℂ] LatticeState Site :=
  K.amplitude x y • matrixUnit x y - K.amplitude y x • matrixUnit y x

/-- Reversing the bond orientation negates the one-particle bond operator. -/
theorem bondOperator_swap (K : LocallyFiniteHopping Site) (x y : Site) :
    K.bondOperator y x = -K.bondOperator x y := by
  simp [bondOperator]

/-- `h Pₓ` is a finite sum over the incident sites of `x`. -/
theorem operator_comp_siteProjector (K : LocallyFiniteHopping Site) (x : Site) :
    K.operator.comp (siteProjector x) =
      ∑ y ∈ K.incident x, K.amplitude y x • matrixUnit y x := by
  classical
  apply Finsupp.lhom_ext
  intro z c
  by_cases hzx : z = x
  · subst z
    simp only [LinearMap.comp_apply, siteProjector_apply, Finsupp.single_eq_same]
    rw [linearMap_finsetSum_apply]
    change K.operator (Finsupp.single x c) =
      ∑ y ∈ K.incident x,
        (K.amplitude y x • matrixUnit y x) (Finsupp.single x c)
    rw [K.operator_single, K.column_eq_sum_single]
    simp only [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro y _
    simp [mul_comm]
  · have hxz : x ≠ z := Ne.symm hzx
    simp [LinearMap.comp_apply, hxz, linearMap_finsetSum_apply]

/-- `Pₓ h` is a finite sum over the incident sites of `x`. -/
theorem siteProjector_comp_operator (K : LocallyFiniteHopping Site) (x : Site) :
    (siteProjector x).comp K.operator =
      ∑ y ∈ K.incident x, K.amplitude x y • matrixUnit x y := by
  classical
  apply Finsupp.lhom_ext
  intro z c
  simp only [LinearMap.comp_apply, operator_single, siteProjector_apply, Finsupp.smul_apply]
  rw [linearMap_finsetSum_apply]
  change Finsupp.single x (c • K.column z x) =
    ∑ y ∈ K.incident x,
      (K.amplitude x y • matrixUnit x y) (Finsupp.single z c)
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

/-- The local one-particle commutator is the negative finite sum of oriented bond operators. -/
theorem linearCommutator_siteProjector (K : LocallyFiniteHopping Site) (x : Site) :
    ConservationLaw.linearCommutator K.operator (siteProjector x) =
      -∑ y ∈ K.incident x, K.bondOperator x y := by
  simp only [ConservationLaw.linearCommutator, K.operator_comp_siteProjector,
    K.siteProjector_comp_operator, bondOperator, Finset.sum_sub_distrib]
  abel

end LocallyFiniteHopping

/-- The many-particle hopping Hamiltonian obtained by second-quantizing the one-particle hopping
operator. -/
noncomputable def hoppingHamiltonian (K : LocallyFiniteHopping Site) :
    AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site) :=
  AlgebraicFock.dGamma (LatticeState Site) K.operator

/-- Many-particle charge localized at one lattice site. -/
noncomputable def siteChargeDensity (q : ℂ) (x : Site) :
    AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site) :=
  q • AlgebraicFock.dGamma (LatticeState Site) (siteProjector x)

/-- The oriented many-particle bond current. The convention is

`J_(x→y) = (i q / ℏ) dΓ(h_xy |x⟩⟨y| - h_yx |y⟩⟨x|)`.
-/
noncomputable def bondCurrent (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (x y : Site) :
    AlgebraicFock (LatticeState Site) →ₗ[ℂ]
      AlgebraicFock (LatticeState Site) :=
  ((Complex.I * q) / ℏ) • AlgebraicFock.dGamma (LatticeState Site) (K.bondOperator x y)

/-- Bond current is antisymmetric under orientation reversal. -/
theorem bondCurrent_swap (ℏ q : ℂ) (K : LocallyFiniteHopping Site) (x y : Site) :
    bondCurrent ℏ q K y x = -bondCurrent ℏ q K x y := by
  unfold bondCurrent
  rw [K.bondOperator_swap]
  have hneg :
      AlgebraicFock.dGamma (LatticeState Site) (-K.bondOperator x y) =
        -AlgebraicFock.dGamma (LatticeState Site) (K.bondOperator x y) := by
    change
      AlgebraicFock.dGammaLinear (LatticeState Site) (-K.bondOperator x y) =
        -AlgebraicFock.dGammaLinear (LatticeState Site) (K.bondOperator x y)
    exact map_neg (AlgebraicFock.dGammaLinear (LatticeState Site)) (K.bondOperator x y)
  rw [hneg]
  exact smul_neg _ _

/-- Heisenberg time derivative of local charge equals minus the finite outgoing-current sum. -/
theorem heisenberg_siteChargeDensity (ℏ q : ℂ)
    (K : LocallyFiniteHopping Site) (x : Site) :
    (Complex.I / ℏ) •
        ConservationLaw.linearCommutator (hoppingHamiltonian K) (siteChargeDensity q x) =
      -∑ y ∈ K.incident x, bondCurrent ℏ q K x y := by
  unfold hoppingHamiltonian siteChargeDensity
  rw [ConservationLaw.linearCommutator_smul_right]
  rw [AlgebraicFock.dGamma_linearCommutator]
  rw [K.linearCommutator_siteProjector]
  have hdGamma :
      AlgebraicFock.dGamma (LatticeState Site) (-∑ y ∈ K.incident x, K.bondOperator x y) =
        -∑ y ∈ K.incident x,
          AlgebraicFock.dGamma (LatticeState Site) (K.bondOperator x y) := by
    change
      AlgebraicFock.dGammaLinear (LatticeState Site) (-∑ y ∈ K.incident x, K.bondOperator x y) =
        -∑ y ∈ K.incident x,
          AlgebraicFock.dGammaLinear (LatticeState Site) (K.bondOperator x y)
    rw [map_neg, map_sum]
  rw [hdGamma]
  unfold bondCurrent
  simp only [smul_smul, smul_neg, Finset.smul_sum]
  apply congrArg Neg.neg
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  ring

/-- The algebraic discrete continuity equation on an arbitrary locally finite lattice. -/
theorem discrete_continuity (ℏ q : ℂ)
    (K : LocallyFiniteHopping Site) (x : Site) :
    (Complex.I / ℏ) •
          ConservationLaw.linearCommutator (hoppingHamiltonian K) (siteChargeDensity q x) +
        ∑ y ∈ K.incident x, bondCurrent ℏ q K x y = 0 := by
  rw [heisenberg_siteChargeDensity]
  abel

end Lattice
end Fermionic
end SecondQuantization
