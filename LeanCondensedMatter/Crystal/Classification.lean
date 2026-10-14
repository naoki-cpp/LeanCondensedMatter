/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Periodicity
import LeanCondensedMatter.Crystal.PointGroup
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import LeanCondensedMatter.Analysis.Matrix.FinTwoCharpoly
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Classification-facing crystal symmetry

The crystallographic point group acts on the translation lattice by integral linear
automorphisms. For a full periodic configuration this representation is faithful, giving the
basis-free form of the usual embedding of a crystallographic point group into `GL(n, ℤ)`.
-/

namespace LeanCondensedMatter.Crystal

namespace latticePointGroup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable section

/-- Changing a finite family of vectors by real matrix coefficients transforms its
Gram matrix by congruence. This helper stays private to the lattice-metric proof. -/
private theorem gram_matrix_congruence
    {ι : Type*} [Fintype ι]
    (v : ι → V) (A : Matrix ι ι ℝ) :
    Matrix.gram ℝ (fun j => ∑ i, A i j • v i) =
      A.transpose * Matrix.gram ℝ v * A := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply]
  calc
    inner ℝ (∑ k, A k i • v k) (∑ l, A l j • v l) =
        ∑ k, ∑ l, A k i * inner ℝ (v k) (v l) * A l j := by
      suffices h :
          (∑ l, A l j * ∑ k, A k i * inner ℝ (v k) (v l)) =
            ∑ k, ∑ l, A k i * (A l j * inner ℝ (v k) (v l)) by
        simpa [inner_sum, sum_inner, inner_smul_left, inner_smul_right,
          mul_comm, mul_left_comm] using h
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum, mul_left_comm]
    _ = ∑ l, (∑ k, A k i * inner ℝ (v k) (v l)) * A l j := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]

/-- A full-rank integral lattice's intrinsic point group preserves the Gram metric
in every integral lattice basis. Each column of the integral matrix contains
the basis coordinates of an image basis vector. The result is rank-generic and
independent of any atomic motif. -/
theorem gram_congruence [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (g : latticePointGroup L) (b : Module.Basis ι ℤ L) :
    let A : Matrix ι ι ℤ :=
      Matrix.of fun i j => (b.repr (latticePointGroup.restrict L g (b j))) i
    let G : Matrix ι ι ℝ := Matrix.gram ℝ (fun i => ((b i : L) : V))
    (A.map (Int.cast : ℤ → ℝ)).transpose * G * (A.map (Int.cast : ℤ → ℝ)) = G := by
  classical
  let rb : Module.Basis ι ℝ V := b.ofZLatticeBasis ℝ L
  let T : V →ₗ[ℝ] V := (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap
  let A : Matrix ι ι ℤ :=
    Matrix.of fun i j => (b.repr (latticePointGroup.restrict L g (b j))) i
  let Ar : Matrix ι ι ℝ := A.map (Int.cast : ℤ → ℝ)
  have hmap (j : ι) :
      T (rb j) = ((latticePointGroup.restrict L g (b j) : L) : V) := by
    change (g : V ≃ₗᵢ[ℝ] V) (rb j) = _
    rw [show rb j = ((b j : L) : V) from b.ofZLatticeBasis_apply ℝ L j]
    rfl
  have hAr : Ar = LinearMap.toMatrix rb rb T := by
    ext i j
    change ((b.repr (latticePointGroup.restrict L g (b j)) i : ℤ) : ℝ) =
      (LinearMap.toMatrix rb rb T) i j
    rw [LinearMap.toMatrix_apply, hmap]
    exact (b.ofZLatticeBasis_repr_apply ℝ L
      (latticePointGroup.restrict L g (b j)) i).symm
  have hcomb (j : ι) :
      T (rb j) = ∑ i, Ar i j • rb i := by
    simpa only [hAr, LinearMap.toMatrix_apply] using
      (rb.sum_repr (T (rb j))).symm
  have hGram : Matrix.gram ℝ (fun i => T (rb i)) =
      Matrix.gram ℝ (fun i => rb i) := by
    ext i j
    change inner ℝ ((g : V ≃ₗᵢ[ℝ] V) (rb i))
      ((g : V ≃ₗᵢ[ℝ] V) (rb j)) = inner ℝ (rb i) (rb j)
    exact LinearIsometryEquiv.inner_map_map (g : V ≃ₗᵢ[ℝ] V) (rb i) (rb j)
  have hb : (fun i : ι => ((b i : L) : V)) = (fun i => rb i) := by
    funext i
    exact (b.ofZLatticeBasis_apply ℝ L i).symm
  change Ar.transpose * Matrix.gram ℝ (fun i => ((b i : L) : V)) * Ar =
    Matrix.gram ℝ (fun i => ((b i : L) : V))
  rw [hb]
  calc
    Ar.transpose * Matrix.gram ℝ (fun i => rb i) * Ar =
        Matrix.gram ℝ (fun j => ∑ i, Ar i j • rb i) :=
      (gram_matrix_congruence (V := V) (fun i => rb i) Ar).symm
    _ = Matrix.gram ℝ (fun j => T (rb j)) := by
      congr 1
      funext j
      exact (hcomb j).symm
    _ = Matrix.gram ℝ (fun i => rb i) := hGram

/-- A real-linear automorphism that preserves a full basis Gram matrix is
an isometry. If it also preserves lattice membership, it belongs to the
intrinsic lattice point group. This separates the metric and arithmetic
parts of constructing Bravais-lattice symmetries. -/
def ofBasisGramPreservingLinearEquiv
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ V) (b : Module.Basis ι ℝ V)
    (f : V ≃ₗ[ℝ] V)
    (hL : ∀ x : V, f x ∈ L ↔ x ∈ L)
    (hGram : Matrix.gram ℝ (fun i => f (b i)) =
      Matrix.gram ℝ (fun i => b i)) :
    latticePointGroup L := by
  classical
  have hBasis (i j : ι) :
      inner ℝ (f (b i)) (f (b j)) = inner ℝ (b i) (b j) := by
    have h := congrArg (fun G : Matrix ι ι ℝ => G i j) hGram
    simpa [Matrix.gram_apply] using h
  have hInner (x y : V) :
      inner ℝ (f x) (f y) = inner ℝ x y := by
    have hx := b.sum_repr x
    have hy := b.sum_repr y
    calc
      inner ℝ (f x) (f y) =
          inner ℝ (f (∑ i, b.repr x i • b i))
            (f (∑ j, b.repr y j • b j)) := by rw [hx, hy]
      _ = inner ℝ (∑ i, b.repr x i • f (b i))
            (∑ j, b.repr y j • f (b j)) := by simp
      _ = inner ℝ (∑ i, b.repr x i • b i)
            (∑ j, b.repr y j • b j) := by
          simp [sum_inner, inner_sum, inner_smul_left, inner_smul_right, hBasis]
      _ = inner ℝ x y := by rw [hx, hy]
  refine ⟨f.isometryOfInner hInner, ?_⟩
  intro x
  simpa only [LinearEquiv.coe_isometryOfInner] using hL x

/-- A reflection across one integral basis axis makes the two basis vectors
orthogonal. This is the rectangular Gram-metric constraint. -/
theorem gram_offDiagonal_eq_zero_of_axisReflection
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hInv :
      let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
      A.transpose * G * A = G) :
    G 0 1 = 0 := by
  dsimp at hInv
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
  linarith

/-- In a symmetric planar metric, invariance under the quarter-turn basis
transformation forces equal squared lengths and orthogonal basis vectors. -/
theorem gram_square_constraints_of_quarterTurn
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0)
    (hInv :
      let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]
      A.transpose * G * A = G) :
    G 0 0 = G 1 1 ∧ G 0 1 = 0 := by
  dsimp at hInv
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hInv
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  constructor <;> linarith

/-- In a symmetric planar metric, invariance under the order-six integral
rotation forces an equilateral primitive basis: equal squared lengths and
twice the off-diagonal inner product equal to their common squared length. -/
theorem gram_hexagonal_constraints_of_sixthTurn
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0)
    (hInv :
      let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 1]
      A.transpose * G * A = G) :
    G 0 0 = G 1 1 ∧ 2 * G 0 1 = G 0 0 := by
  dsimp at hInv
  have h00 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hInv
  have h01 := congrArg
    (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hInv
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  constructor <;> linarith


/-- For a symmetric planar Gram matrix, an integral basis-axis reflection
preserves the metric exactly when that basis is orthogonal. -/
theorem gram_axisReflection_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1];
      A.transpose * G * A = G) ↔ G 0 1 = 0 := by
  constructor
  · exact gram_offDiagonal_eq_zero_of_axisReflection G
  · intro h
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- For a symmetric planar metric, the quarter-turn acts isometrically exactly
when the two primitive vectors are orthogonal and have equal squared lengths. -/
theorem gram_quarterTurn_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0];
      A.transpose * G * A = G) ↔
      G 0 0 = G 1 1 ∧ G 0 1 = 0 := by
  constructor
  · exact gram_square_constraints_of_quarterTurn G hSymm
  · rintro ⟨hDiag, hOff⟩
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- For a symmetric planar metric, the order-six integral rotation acts
isometrically exactly when the primitive basis has the hexagonal Gram form. -/
theorem gram_sixthTurn_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 1];
      A.transpose * G * A = G) ↔
      G 0 0 = G 1 1 ∧ 2 * G 0 1 = G 0 0 := by
  constructor
  · exact gram_hexagonal_constraints_of_sixthTurn G hSymm
  · rintro ⟨hDiag, hOff⟩
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

/-- Swapping two primitive basis vectors preserves a symmetric Gram matrix
exactly when they have equal squared lengths. This is the rhombic primitive-basis
condition relevant to the centered-rectangular Bravais class. It is not by
itself an exhaustive characterization of that class. -/
theorem gram_basisSwap_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0];
      A.transpose * G * A = G) ↔ G 0 0 = G 1 1 := by
  constructor
  · intro hInv
    dsimp at hInv
    have h00 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) hInv
    have heq : G 1 1 = G 0 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00
    exact heq.symm
  · intro hDiag
    dsimp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> linarith

end

end latticePointGroup


namespace AtomicConfiguration

variable {V E Species : Type*}

section Generic
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [MetricSpace E] [NormedAddTorsor V E]

noncomputable section

private theorem conjugate_constVAdd_eq_constVAdd_linearPart
    (g : E ≃ᵢ E) (v : V) :
    g * (IsometryEquiv.constVAdd v : E ≃ᵢ E) * g⁻¹ =
      IsometryEquiv.constVAdd (g.toRealAffineIsometryEquiv.linearIsometryEquiv v) := by
  ext x
  change g (v +ᵥ g⁻¹ x) = g.toRealAffineIsometryEquiv.linearIsometryEquiv v +ᵥ x
  calc
    g (v +ᵥ g⁻¹ x) =
        g.toRealAffineIsometryEquiv.linearIsometryEquiv v +ᵥ g (g⁻¹ x) := by
      exact g.toRealAffineIsometryEquiv.map_vadd (g⁻¹ x) v
    _ = g.toRealAffineIsometryEquiv.linearIsometryEquiv v +ᵥ x := by simp

/-- The linear part of a configuration symmetry preserves every translation symmetry. -/
theorem symmetryLinearPart_mem_translationSubgroup (X : AtomicConfiguration E Species)
    (g : X.symmetryGroup) {v : V} (hv : v ∈ X.translationSubgroup (V := V)) :
    X.symmetryLinearPartHom (V := V) g v ∈ X.translationSubgroup (V := V) := by
  rw [mem_translationSubgroup]
  change (IsometryEquiv.constVAdd
      (((g : E ≃ᵢ E).toRealAffineIsometryEquiv.linearIsometryEquiv) v) : E ≃ᵢ E) ∈
    X.symmetryGroup
  rw [← conjugate_constVAdd_eq_constVAdd_linearPart (V := V) (g := (g : E ≃ᵢ E)) v]
  exact X.symmetryGroup.mul_mem
    (X.symmetryGroup.mul_mem g.property (mem_translationSubgroup.mp hv))
    (X.symmetryGroup.inv_mem g.property)

/-- A symmetry linear part preserves the translation subgroup in both directions. -/
theorem symmetryLinearPart_mem_translationSubgroup_iff (X : AtomicConfiguration E Species)
    (g : X.symmetryGroup) (v : V) :
    X.symmetryLinearPartHom (V := V) g v ∈ X.translationSubgroup (V := V) ↔
      v ∈ X.translationSubgroup (V := V) := by
  constructor
  · intro hv
    have h := X.symmetryLinearPart_mem_translationSubgroup (V := V) (g := g⁻¹) hv
    simpa using h
  · exact X.symmetryLinearPart_mem_translationSubgroup (V := V) g

/-- Every crystallographic point-group element preserves the translation lattice. -/
theorem pointGroup_mem_translationSubgroup_iff (X : AtomicConfiguration E Species)
    (g : X.pointGroup (V := V)) (v : V) :
    (g : V ≃ₗᵢ[ℝ] V) v ∈ X.translationSubgroup (V := V) ↔
      v ∈ X.translationSubgroup (V := V) := by
  rcases g.property with ⟨s, hs⟩
  have h := X.symmetryLinearPart_mem_translationSubgroup_iff (V := V) s v
  simpa [hs] using h

/-- A configuration point group is a subgroup of the intrinsic symmetry group of
its derived translation lattice. The reverse inclusion need not hold: a species-labeled
motif can break lattice rotations or reflections. -/
theorem pointGroup_le_latticePointGroup (X : AtomicConfiguration E Species) :
    X.pointGroup (V := V) ≤
      latticePointGroup (V := V)
        (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) := by
  intro g hg
  change ∀ v : V, g v ∈ X.translationSubgroup (V := V) ↔
    v ∈ X.translationSubgroup (V := V)
  intro v
  exact X.pointGroup_mem_translationSubgroup_iff (V := V) ⟨g, hg⟩ v

/-- The configuration point-group action is the restriction of the intrinsic lattice
point-group action. -/
def pointGroupLatticeEquiv (X : AtomicConfiguration E Species)
    (g : X.pointGroup (V := V)) :
    AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) ≃ₗ[ℤ]
      AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) :=
  latticePointGroup.restrict
    (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)))
    ⟨(g : V ≃ₗᵢ[ℝ] V), X.pointGroup_le_latticePointGroup (V := V) g.property⟩

/-- The integral representation of the point group on the translation lattice. -/
def pointGroupLatticeRepresentation (X : AtomicConfiguration E Species) :
    X.pointGroup (V := V) →*
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) ≃ₗ[ℤ]
        AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) where
  toFun := X.pointGroupLatticeEquiv (V := V)
  map_one' := by
    ext v
    rfl
  map_mul' g h := by
    ext v
    rfl

/-- For a full periodic configuration, the point-group action on the translation lattice is
faithful. -/
theorem pointGroupLatticeRepresentation_injective (X : AtomicConfiguration E Species)
    (hX : X.Periodic (V := V)) :
    Function.Injective (X.pointGroupLatticeRepresentation (V := V)) := by
  intro g h hgh
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  have hxspan : x ∈ Submodule.span ℝ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) : Set V) := by
    rw [hX.isZLattice.span_top]
    exact Submodule.mem_top
  induction hxspan using Submodule.span_induction with
  | mem x hx =>
      have heq := DFunLike.congr_fun hgh
        (⟨x, hx⟩ : AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)))
      exact congrArg Subtype.val heq
  | zero => simp
  | add x y _ _ hx hy => simpa using congrArg₂ (· + ·) hx hy
  | smul a x _ hx => simpa using congrArg (a • ·) hx


/-- After choosing an integral basis of the translation lattice, the point group acts by
invertible integer matrices. Coordinates are selected here, not stored in the configuration.

The index type may later be specialized to `Fin n`; no finite-dimensional assumption or
chosen basis is needed for the preceding basis-free representation. -/
def pointGroupMatrixRepresentation (X : AtomicConfiguration E Species)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)))) :
    X.pointGroup (V := V) →* Matrix.GeneralLinearGroup ι ℤ :=
  (((Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ _)).symm.toMonoidHom).comp
      (X.pointGroupLatticeRepresentation (V := V))

/-- For a periodic configuration, the matrix representation is faithful in any chosen
integral lattice basis. -/
theorem pointGroupMatrixRepresentation_injective (X : AtomicConfiguration E Species)
    (hX : X.Periodic (V := V))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)))) :
    Function.Injective (X.pointGroupMatrixRepresentation (V := V) b) := by
  intro g h hgh
  let e : Matrix.GeneralLinearGroup ι ℤ ≃*
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)) ≃ₗ[ℤ]
        AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ _)
  change e.symm (X.pointGroupLatticeRepresentation (V := V) g) =
    e.symm (X.pointGroupLatticeRepresentation (V := V) h) at hgh
  exact (X.pointGroupLatticeRepresentation_injective (V := V) hX)
    (e.symm.injective hgh)


/-- The trace of a crystallographic point-group action is integral.

A basis of the discrete translation lattice extends to a real basis of the ambient vector
space. In this basis every diagonal coefficient of the point-group linear part is an integer.
This basis-free trace integrality is the arithmetic input to the crystallographic restriction. -/
theorem exists_int_trace_pointGroup [FiniteDimensional ℝ V]
    (X : AtomicConfiguration E Species)
    (hX : X.Periodic (V := V)) (g : X.pointGroup (V := V))
    (b : Module.Basis (Fin 2) ℤ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)))) :
    ∃ z : ℤ, LinearMap.trace ℝ V
      (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap = (z : ℝ) := by
  let L : Submodule ℤ V :=
    AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))
  letI : DiscreteTopology L := hX.discreteTranslations
  letI : IsZLattice ℝ L := hX.isZLattice
  let rb : Module.Basis (Fin 2) ℝ V := b.ofZLatticeBasis ℝ L
  let T : V →ₗ[ℝ] V := (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap
  let z : ℤ := ∑ i : Fin 2, (b.repr (X.pointGroupLatticeEquiv (V := V) g (b i))) i
  refine ⟨z, ?_⟩
  change LinearMap.trace ℝ V T = (z : ℝ)
  rw [LinearMap.trace_eq_matrix_trace ℝ rb T]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  rw [show (z : ℝ) =
    ∑ i : Fin 2, ((b.repr (X.pointGroupLatticeEquiv (V := V) g (b i))) i : ℝ) by
      simp [z]]
  apply Finset.sum_congr rfl
  intro i _
  have hi : T (rb i) =
      ((X.pointGroupLatticeEquiv (V := V) g (b i) : L) : V) := by
    change T (rb i) = (g : V ≃ₗᵢ[ℝ] V) (b i)
    simp only [T, rb, Module.Basis.ofZLatticeBasis_apply,
      LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [hi]
  exact b.ofZLatticeBasis_repr_apply ℝ L
    (X.pointGroupLatticeEquiv (V := V) g (b i)) i


end

end Generic

section Planar

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MetricSpace E] [NormedAddTorsor V E]

noncomputable section

/-- In two Euclidean dimensions the trace of a point-group isometry lies in `[-2, 2]`.

The bound is independent of a translation-lattice basis. It follows by summing the
Cauchy–Schwarz bounds of the two diagonal coefficients in any orthonormal basis. -/
theorem pointGroup_trace_bounds
    (X : AtomicConfiguration E Species) (g : X.pointGroup (V := V))
    (o : OrthonormalBasis (Fin 2) ℝ V) :
    -2 ≤ LinearMap.trace ℝ V (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap ∧
      LinearMap.trace ℝ V (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap ≤ 2 := by
  let T : V →ₗ[ℝ] V := (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap
  have hcoord (i : Fin 2) :
      -1 ≤ inner ℝ (o i) ((g : V ≃ₗᵢ[ℝ] V) (o i)) ∧
        inner ℝ (o i) ((g : V ≃ₗᵢ[ℝ] V) (o i)) ≤ 1 := by
    have h := abs_real_inner_le_norm (o i) ((g : V ≃ₗᵢ[ℝ] V) (o i))
    have hle : |inner ℝ (o i) ((g : V ≃ₗᵢ[ℝ] V) (o i))| ≤ 1 := by
      simpa using h
    exact abs_le.mp hle
  have h0 := hcoord 0
  have h1 := hcoord 1
  change -2 ≤ LinearMap.trace ℝ V T ∧ LinearMap.trace ℝ V T ≤ 2
  rw [LinearMap.trace_eq_sum_inner T o, Fin.sum_univ_two]
  simp only [T, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2]

/-- The planar crystallographic trace is one of the five integers from `-2` to `2`.
This is the arithmetic/geometric bridge used to restrict the allowed planar rotations. -/
theorem exists_int_trace_pointGroup_bounded
    [FiniteDimensional ℝ V]
    (X : AtomicConfiguration E Species)
    (hX : X.Periodic (V := V)) (g : X.pointGroup (V := V))
    (b : Module.Basis (Fin 2) ℤ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))))
    (o : OrthonormalBasis (Fin 2) ℝ V) :
    ∃ z : ℤ, -2 ≤ z ∧ z ≤ 2 ∧
      LinearMap.trace ℝ V (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap = (z : ℝ) := by
  obtain ⟨z, hz⟩ := X.exists_int_trace_pointGroup hX g b
  obtain ⟨hlo, hhi⟩ := X.pointGroup_trace_bounds g o
  rw [hz] at hlo hhi
  exact ⟨z, by exact_mod_cast hlo, by exact_mod_cast hhi, hz⟩


/-- In a two-dimensional inner-product space, a point-group isometry with trace two
must be the identity. This rules out nontrivial unipotent/shear matrices at the endpoint
of the crystallographic trace interval. -/
theorem pointGroup_eq_one_of_trace_eq_two
    (X : AtomicConfiguration E Species) (g : X.pointGroup (V := V))
    (o : OrthonormalBasis (Fin 2) ℝ V)
    (htrace : LinearMap.trace ℝ V
      (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap = 2) :
    g = 1 := by
  let f : V ≃ₗᵢ[ℝ] V := g
  have hupper (i : Fin 2) : inner ℝ (o i) (f (o i)) ≤ 1 := by
    have h := abs_real_inner_le_norm (o i) (f (o i))
    have hle : |inner ℝ (o i) (f (o i))| ≤ 1 := by
      simpa [f] using h
    exact (le_abs_self _).trans hle
  have hsum : inner ℝ (o 0) (f (o 0)) +
      inner ℝ (o 1) (f (o 1)) = 2 := by
    rw [LinearMap.trace_eq_sum_inner _ o, Fin.sum_univ_two] at htrace
    simpa only [f, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
      using htrace
  have hzero : inner ℝ (o 0) (f (o 0)) = 1 := by
    linarith [hupper 0, hupper 1]
  have hone : inner ℝ (o 1) (f (o 1)) = 1 := by
    linarith [hupper 0, hupper 1]
  have heq (i : Fin 2) : inner ℝ (o i) (f (o i)) = 1 := by
    fin_cases i
    · simpa using hzero
    · simpa using hone
  have hfixed (i : Fin 2) : f (o i) = o i := by
    have heq' : o i = f (o i) :=
      (inner_eq_one_iff_of_norm_eq_one (o.norm_eq_one i)
        (by simpa [f] using f.norm_map (o i))).mp (heq i)
    exact heq'.symm
  have hlinear : f.toLinearEquiv.toLinearMap = LinearMap.id := by
    apply o.toBasis.ext
    intro i
    simpa only [OrthonormalBasis.coe_toBasis, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearMap.id_apply] using hfixed i
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  have hx := LinearMap.congr_fun hlinear x
  simpa [f] using hx


/-- A planar point-group isometry with trace `-2` is the half-turn: it squares to the
identity. Equality in the lower Cauchy–Schwarz bound forces it to negate every basis
vector, hence every vector. -/
theorem pointGroup_sq_eq_one_of_trace_eq_neg_two
    (X : AtomicConfiguration E Species) (g : X.pointGroup (V := V))
    (o : OrthonormalBasis (Fin 2) ℝ V)
    (htrace : LinearMap.trace ℝ V
      (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap = -2) :
    g ^ 2 = 1 := by
  let f : V ≃ₗᵢ[ℝ] V := g
  have hlower (i : Fin 2) : -1 ≤ inner ℝ (o i) (f (o i)) := by
    have h := abs_real_inner_le_norm (o i) (f (o i))
    have hbound : |inner ℝ (o i) (f (o i))| ≤ 1 := by
      simpa [f] using h
    exact (abs_le.mp hbound).1
  have hsum : inner ℝ (o 0) (f (o 0)) +
      inner ℝ (o 1) (f (o 1)) = -2 := by
    rw [LinearMap.trace_eq_sum_inner _ o, Fin.sum_univ_two] at htrace
    simpa only [f, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
      using htrace
  have hzero : inner ℝ (o 0) (f (o 0)) = -1 := by
    linarith [hlower 0, hlower 1]
  have hone : inner ℝ (o 1) (f (o 1)) = -1 := by
    linarith [hlower 0, hlower 1]
  have heq (i : Fin 2) : inner ℝ (o i) (f (o i)) = -1 := by
    fin_cases i
    · simpa using hzero
    · simpa using hone
  have hfixed (i : Fin 2) : f (o i) = -(o i) := by
    have hi : o i = -(f (o i)) :=
      (inner_eq_neg_one_iff_of_norm_eq_one (o.norm_eq_one i)
        (by simpa [f] using f.norm_map (o i))).mp (heq i)
    simpa using congrArg Neg.neg hi.symm
  have hlinear : f.toLinearEquiv.toLinearMap = -(LinearMap.id : V →ₗ[ℝ] V) := by
    apply o.toBasis.ext
    intro i
    simpa only [OrthonormalBasis.coe_toBasis, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearMap.neg_apply,
      LinearMap.id_apply] using hfixed i
  have hneg (x : V) : f x = -x := by
    have hx := LinearMap.congr_fun hlinear x
    simpa [f] using hx
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  change f (f x) = x
  rw [hneg (f x), hneg x, neg_neg]


/-- A power identity for the matrix of a point-group linear part transfers to the
point-group element itself. This is independent of crystallographic periodicity. -/
theorem pointGroup_pow_eq_one_of_toMatrix_pow_eq_one
    (X : AtomicConfiguration E Species) (g : X.pointGroup (V := V))
    (b : Module.Basis (Fin 2) ℝ V) (n : ℕ)
    (h : (LinearMap.toMatrix b b
      (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap) ^ n = 1) :
    g ^ n = 1 := by
  let f : V ≃ₗᵢ[ℝ] V := g
  let T : V →ₗ[ℝ] V := f.toLinearEquiv.toLinearMap
  have hT : T ^ n = 1 := by
    apply (LinearMap.toMatrix b b).injective
    rw [← LinearMap.toMatrix_pow, LinearMap.toMatrix_one]
    exact h
  have hpow_map (k : ℕ) : ∀ x : V, (T ^ k) x = (f ^ k) x := by
    induction k with
    | zero =>
        intro x
        simp
    | succ k ih =>
        intro x
        rw [pow_succ, pow_succ, Module.End.mul_apply]
        change (T ^ k) (T x) = (f ^ k) (f x)
        exact ih (f x)
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  change (f ^ n) x = x
  rw [← hpow_map n x]
  exact LinearMap.congr_fun hT x


/-- For a rank-two periodic crystal, every orientation-preserving point-group element
has an allowed crystallographic rotation power: one, two, three, four, or six.

The determinant-one assumption is stated explicitly in terms of the real linear part;
reflection/determinant-minus-one elements are handled separately. -/
theorem pointGroup_rotation_power_of_det_one
    [FiniteDimensional ℝ V]
    (X : AtomicConfiguration E Species) (hX : X.Periodic (V := V))
    (g : X.pointGroup (V := V))
    (b : Module.Basis (Fin 2) ℤ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))))
    (o : OrthonormalBasis (Fin 2) ℝ V)
    (hdet : LinearMap.det (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap = 1) :
    g = 1 ∨ g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 4 = 1 ∨ g ^ 6 = 1 := by
  let T : V →ₗ[ℝ] V := (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap
  let M : Matrix (Fin 2) (Fin 2) ℝ := LinearMap.toMatrix o.toBasis o.toBasis T
  have hdetM : M.det = 1 := by
    rw [show M.det = LinearMap.det T from LinearMap.det_toMatrix o.toBasis T]
    exact hdet
  obtain ⟨z, hlo, hhi, htrace⟩ := X.exists_int_trace_pointGroup_bounded hX g b o
  change LinearMap.trace ℝ V T = (z : ℝ) at htrace
  have htraceM : M.trace = (z : ℝ) := by
    rw [show M.trace = LinearMap.trace ℝ V T from
      (LinearMap.trace_eq_matrix_trace ℝ o.toBasis T).symm]
    exact htrace
  have hcases : z = -2 ∨ z = -1 ∨ z = 0 ∨ z = 1 ∨ z = 2 := by omega
  rcases hcases with hz | hz | hz | hz | hz
  · right; left
    exact X.pointGroup_sq_eq_one_of_trace_eq_neg_two g o (by simpa [hz] using htrace)
  · right; right; left
    have hM : M ^ 3 = 1 :=
      M.pow_three_eq_one_of_trace_neg_one_det_one
        (by simpa [hz] using htraceM) hdetM
    exact X.pointGroup_pow_eq_one_of_toMatrix_pow_eq_one g o.toBasis 3 hM
  · right; right; right; left
    have hM : M ^ 4 = 1 :=
      M.pow_four_eq_one_of_trace_zero_det_one
        (by simpa [hz] using htraceM) hdetM
    exact X.pointGroup_pow_eq_one_of_toMatrix_pow_eq_one g o.toBasis 4 hM
  · right; right; right; right
    have hM : M ^ 6 = 1 :=
      M.pow_six_eq_one_of_trace_one_det_one
        (by simpa [hz] using htraceM) hdetM
    exact X.pointGroup_pow_eq_one_of_toMatrix_pow_eq_one g o.toBasis 6 hM
  · left
    exact X.pointGroup_eq_one_of_trace_eq_two g o (by simpa [hz] using htrace)


/-- The planar crystallographic restriction: every point-group element of a rank-two
periodic configuration has order dividing one of `1`, `2`, `3`, `4`, or `6`.

The determinant-one branch gives the crystallographic rotations; the determinant-minus-one
branch is an orientation-reversing orthogonal map and hence a reflection of order two. -/
theorem pointGroup_crystallographic_restriction
    [FiniteDimensional ℝ V]
    (X : AtomicConfiguration E Species) (hX : X.Periodic (V := V))
    (g : X.pointGroup (V := V))
    (b : Module.Basis (Fin 2) ℤ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))))
    (o : OrthonormalBasis (Fin 2) ℝ V) :
    g = 1 ∨ g ^ 2 = 1 ∨ g ^ 3 = 1 ∨ g ^ 4 = 1 ∨ g ^ 6 = 1 := by
  let T : V →ₗ[ℝ] V := (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap
  let M : Matrix (Fin 2) (Fin 2) ℝ := LinearMap.toMatrix o.toBasis o.toBasis T
  have hunit : M ∈ Matrix.unitaryGroup (Fin 2) ℝ := by
    exact LinearIsometryEquiv.toMatrix_mem_unitaryGroup (g : V ≃ₗᵢ[ℝ] V) o o
  have horth : M * M.transpose = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp hunit
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hdetSq : M.det ^ 2 = 1 := by
    have h := congrArg Matrix.det horth
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one, pow_two] using h
  have hdetM : M.det = LinearMap.det T := LinearMap.det_toMatrix o.toBasis T
  rcases (sq_eq_one_iff.mp hdetSq) with hplus | hminus
  · apply X.pointGroup_rotation_power_of_det_one hX g b o
    change LinearMap.det T = 1
    exact hdetM.symm.trans hplus
  · right; left
    exact X.pointGroup_pow_eq_one_of_toMatrix_pow_eq_one g o.toBasis 2
      (M.sq_eq_one_of_mul_transpose_eq_one_det_neg_one horth hminus)


/-- The Gram matrix of a basis of a rank-two periodic translation lattice is positive
definite. This is the metric input for classifying Bravais lattice shapes. -/
theorem translation_lattice_gram_posDef
    [FiniteDimensional ℝ V]
    (X : AtomicConfiguration E Species) (hX : X.Periodic (V := V))
    (b : Module.Basis (Fin 2) ℤ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)))) :
    (Matrix.gram ℝ (fun i => ((b i :
      AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) : V))).PosDef := by
  let L : Submodule ℤ V :=
    AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))
  letI : DiscreteTopology L := hX.discreteTranslations
  letI : IsZLattice ℝ L := hX.isZLattice
  let rb : Module.Basis (Fin 2) ℝ V := b.ofZLatticeBasis ℝ L
  have hfun : (fun i : Fin 2 => ((b i : L) : V)) =
      fun i => (b.ofZLatticeBasis ℝ L) i := by
    funext i
    exact (b.ofZLatticeBasis_apply ℝ L i).symm
  rw [hfun]
  exact Matrix.posDef_gram_of_linearIndependent rb.linearIndependent

/-- Every crystallographic point-group action preserves the Gram matrix of an integral
translation-lattice basis. This relates lattice symmetries directly to metric data, without
choosing an orthonormal coordinate system or introducing another lattice structure. -/
theorem pointGroup_lattice_gram_invariant
    (X : AtomicConfiguration E Species)
    (g : X.pointGroup (V := V))
    (b : Module.Basis (Fin 2) ℤ
      (AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V)))) :
    Matrix.gram ℝ (fun i => ((X.pointGroupLatticeEquiv (V := V) g (b i) :
      AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) : V)) =
      Matrix.gram ℝ (fun i => ((b i :
        AddSubgroup.toIntSubmodule (X.translationSubgroup (V := V))) : V)) := by
  ext i j
  change inner ℝ ((g : V ≃ₗᵢ[ℝ] V) (b i : V))
    ((g : V ≃ₗᵢ[ℝ] V) (b j : V)) = inner ℝ (b i : V) (b j : V)
  exact LinearIsometryEquiv.inner_map_map (g : V ≃ₗᵢ[ℝ] V) (b i : V) (b j : V)


end

end Planar

end AtomicConfiguration

end LeanCondensedMatter.Crystal
