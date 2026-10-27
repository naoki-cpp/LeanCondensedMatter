/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.PointGroup
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Gram matrices and lattice point-group automorphisms

Lattice point-group elements are characterized by Gram-preserving integral automorphisms.
The constructions extend integral lattice maps to the ambient real space and relate basis changes
to Gram congruence.
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
            (∑ j, b.repr y j • f (b j)) := by
          simp only [map_sum, map_smul]
      _ = inner ℝ (∑ i, b.repr x i • b i)
            (∑ j, b.repr y j • b j) := by
          simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
          simp only [hBasis]
      _ = inner ℝ x y := by rw [hx, hy]
  refine ⟨f.isometryOfInner hInner, ?_⟩
  intro x
  simpa only [LinearEquiv.coe_isometryOfInner] using hL x

/-- Extend an integral-linear automorphism of a full lattice to an ambient
real-linear automorphism by using the real bases induced by its source and image
integer bases. No independent lattice or matrix representation is needed. -/
noncomputable def extendIntegralLinearEquiv [FiniteDimensional ℝ V]
    {ι : Type*}
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (e : L ≃ₗ[ℤ] L) : V ≃ₗ[ℝ] V :=
  (b.ofZLatticeBasis ℝ L).repr.trans
    (((b.map e).ofZLatticeBasis ℝ L).repr.symm)

/-- The ambient extension agrees with the integral-linear automorphism on
every integer basis vector. -/
@[simp]
theorem extendIntegralLinearEquiv_apply_basis [FiniteDimensional ℝ V]
    {ι : Type*}
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (e : L ≃ₗ[ℤ] L) (i : ι) :
    extendIntegralLinearEquiv L b e ((b i : L) : V) = ((e (b i) : L) : V) := by
  let rb : Module.Basis ι ℝ V := b.ofZLatticeBasis ℝ L
  let rb' : Module.Basis ι ℝ V := (b.map e).ofZLatticeBasis ℝ L
  have hSource : rb i = ((b i : L) : V) :=
    b.ofZLatticeBasis_apply ℝ L i
  have hTarget : rb' i = ((e (b i) : L) : V) := by
    simp only [rb', Module.Basis.ofZLatticeBasis_apply, Module.Basis.map_apply]
  rw [← hSource, ← hTarget]
  change (rb.repr.trans rb'.repr.symm) (rb i) = rb' i
  simp

/-- An integral-linear lattice automorphism extends to an ambient real-linear
automorphism that preserves lattice membership in both directions. -/
theorem extendIntegralLinearEquiv_mem_iff [FiniteDimensional ℝ V]
    {ι : Type*}
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (e : L ≃ₗ[ℤ] L) (x : V) :
    extendIntegralLinearEquiv L b e x ∈ L ↔ x ∈ L := by
  classical
  let rb : Module.Basis ι ℝ V := b.ofZLatticeBasis ℝ L
  let rb' : Module.Basis ι ℝ V := (b.map e).ofZLatticeBasis ℝ L
  let f : V ≃ₗ[ℝ] V := extendIntegralLinearEquiv L b e
  have hb : Submodule.span ℤ (Set.range rb) = L :=
    b.ofZLatticeBasis_span ℝ
  have hb' : Submodule.span ℤ (Set.range rb') = L :=
    (b.map e).ofZLatticeBasis_span ℝ
  have hf (i : ι) : f (rb i) = rb' i := by
    simpa only [f, rb, rb', Module.Basis.ofZLatticeBasis_apply,
      Module.Basis.map_apply] using (extendIntegralLinearEquiv_apply_basis L b e i)
  have hmap : Submodule.map (f.toLinearMap.restrictScalars ℤ) L = L := by
    calc
      Submodule.map (f.toLinearMap.restrictScalars ℤ) L =
          Submodule.span ℤ
            ((f.toLinearMap.restrictScalars ℤ) '' Set.range rb) := by
        rw [← hb, Submodule.map_span]
      _ = Submodule.span ℤ (Set.range (fun i => f (rb i))) := by
        congr 1
        ext v
        constructor
        · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
        · rintro ⟨i, rfl⟩
          exact ⟨rb i, ⟨i, rfl⟩, rfl⟩
      _ = Submodule.span ℤ (Set.range rb') := by
        have hFun : (fun i : ι => f (rb i)) = rb' := by
          funext i
          exact hf i
        rw [hFun]
      _ = L := hb'
  change f x ∈ L ↔ x ∈ L
  calc
    f x ∈ L ↔ f x ∈ Submodule.map (f.toLinearMap.restrictScalars ℤ) L := by
      rw [hmap]
    _ ↔ x ∈ L := by
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, hxy⟩
        simpa [f.injective hxy] using hy
      · intro hx
        exact ⟨x, hx, rfl⟩

/-- Every integral-linear automorphism of a full lattice preserving the
Gram matrix of its integral basis determines an intrinsic lattice-point-group
isometry. This is the converse to the intrinsic Gram congruence at the
coordinate-free lattice-automorphism level. -/
noncomputable def ofIntegralLinearEquivGramPreserving [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (e : L ≃ₗ[ℤ] L)
    (hGram :
      Matrix.gram ℝ (fun i => ((e (b i) : L) : V)) =
        Matrix.gram ℝ (fun i => ((b i : L) : V))) :
    latticePointGroup L :=
  ofBasisGramPreservingLinearEquiv L (b.ofZLatticeBasis ℝ L)
    (extendIntegralLinearEquiv L b e)
    (extendIntegralLinearEquiv_mem_iff L b e)
    (by
      simpa only [Module.Basis.ofZLatticeBasis_apply,
        extendIntegralLinearEquiv_apply_basis] using hGram)

/-- An invertible integer matrix preserving the metric of a full lattice basis
induces an intrinsic lattice isometry. The matrix is interpreted using Mathlib's
general linear group, not a separate crystallographic matrix group. -/
noncomputable def ofGLGramPreserving [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (A : Matrix.GeneralLinearGroup ι ℤ)
    (hGram :
      let G := Matrix.gram ℝ (fun i => ((b i : L) : V))
      ((A : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ)).transpose * G *
        ((A : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ)) = G) :
    latticePointGroup L := by
  classical
  let e : L ≃ₗ[ℤ] L := (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv
  let Ar : Matrix ι ι ℝ := (A : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ)
  let v : ι → V := fun i => ((b i : L) : V)
  have hBasis (j : ι) :
      e (b j) = ∑ i, (A : Matrix ι ι ℤ) i j • b i := by
    change (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv (b j) = _
    rw [Matrix.GeneralLinearGroup.toLin'_apply]
    simp only [Module.Basis.repr_self, Finsupp.single_eq_pi_single,
      Matrix.mulVec_single_one, Matrix.col_apply, Fintype.linearCombination_apply]
  have hImage (j : ι) :
      ((e (b j) : L) : V) = ∑ i, Ar i j • v i := by
    have h := congrArg (fun x : L => (x : V)) (hBasis j)
    simpa only [v, Ar, Matrix.map_apply, Submodule.coe_sum,
      Submodule.coe_smul, Int.cast_smul_eq_zsmul] using h
  apply ofIntegralLinearEquivGramPreserving L b e
  calc
    Matrix.gram ℝ (fun i => ((e (b i) : L) : V)) =
        Matrix.gram ℝ (fun j => ∑ i, Ar i j • v i) := by
      congr 1
      funext j
      exact hImage j
    _ = Ar.transpose * Matrix.gram ℝ v * Ar :=
      gram_matrix_congruence v Ar
    _ = Matrix.gram ℝ (fun i => ((b i : L) : V)) := by
      exact hGram

/-- The intrinsic lattice isometry constructed from an integral-linear
automorphism restricts back to that automorphism. This makes the metric
extension compatible with the original integral action. -/
@[simp]
theorem restrict_ofIntegralLinearEquivGramPreserving [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (e : L ≃ₗ[ℤ] L)
    (hGram :
      Matrix.gram ℝ (fun i => ((e (b i) : L) : V)) =
        Matrix.gram ℝ (fun i => ((b i : L) : V))) :
    restrict L (ofIntegralLinearEquivGramPreserving L b e hGram) = e := by
  have hLin :
      (restrict L (ofIntegralLinearEquivGramPreserving L b e hGram)).toLinearMap =
        e.toLinearMap := by
    apply b.ext
    intro i
    apply Subtype.ext
    change extendIntegralLinearEquiv L b e ((b i : L) : V) = ((e (b i) : L) : V)
    exact extendIntegralLinearEquiv_apply_basis L b e i
  exact LinearEquiv.ext (fun x => LinearMap.congr_fun hLin x)

/-- Lifting a Gram-preserving unimodular integer matrix to an intrinsic lattice
isometry and restricting to the lattice recovers Mathlib's original integral
linear automorphism represented by that matrix. -/
@[simp]
theorem restrict_ofGLGramPreserving [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (A : Matrix.GeneralLinearGroup ι ℤ)
    (hGram :
      let G := Matrix.gram ℝ (fun i => ((b i : L) : V))
      ((A : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ)).transpose * G *
        ((A : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ)) = G) :
    restrict L (ofGLGramPreserving L b A hGram) =
      (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv := by
  unfold ofGLGramPreserving
  apply restrict_ofIntegralLinearEquivGramPreserving

/-- In the chosen integral basis, the intrinsic lattice isometry obtained from
a Gram-preserving integer matrix has *exactly* that matrix as its coordinate
representation. This connects concrete planar symmetry matrices to geometry. -/
theorem ofGLGramPreserving_basis_coordinates [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (A : Matrix.GeneralLinearGroup ι ℤ)
    (hGram :
      let G := Matrix.gram ℝ (fun i => ((b i : L) : V))
      ((A : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ)).transpose * G *
        ((A : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ)) = G)
    (i j : ι) :
    (b.repr (restrict L (ofGLGramPreserving L b A hGram) (b j))) i =
      (A : Matrix ι ι ℤ) i j := by
  rw [restrict_ofGLGramPreserving]
  rw [Matrix.GeneralLinearGroup.toLin'_apply]
  simp only [Module.Basis.repr_self, Finsupp.single_eq_pi_single,
    Matrix.mulVec_single_one, Matrix.col_apply, Fintype.linearCombination_apply]
  rw [Module.Basis.repr_sum_self]

/-- Restricting an intrinsic lattice isometry preserves the Gram matrix of any
integral lattice basis. This statement needs neither periodicity nor a choice
of coordinate representation for the isometry. -/
theorem gram_restrict
    {ι : Type*}
    (L : Submodule ℤ V) (b : Module.Basis ι ℤ L)
    (g : latticePointGroup L) :
    Matrix.gram ℝ (fun i => (((restrict L g) (b i) : L) : V)) =
      Matrix.gram ℝ (fun i => ((b i : L) : V)) := by
  ext i j
  change inner ℝ ((g : V ≃ₗᵢ[ℝ] V) ((b i : L) : V))
    ((g : V ≃ₗᵢ[ℝ] V) ((b j : L) : V)) =
      inner ℝ ((b i : L) : V) ((b j : L) : V)
  exact LinearIsometryEquiv.inner_map_map (g : V ≃ₗᵢ[ℝ] V) _ _

/-- Extending the restriction of an intrinsic lattice isometry back to the
ambient real vector space recovers the original isometry. Together with
`restrict_ofIntegralLinearEquivGramPreserving`, this completes the
coordinate-free round trip between lattice symmetries and Gram-preserving
integral lattice automorphisms. -/
@[simp]
theorem ofIntegralLinearEquivGramPreserving_restrict [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (g : latticePointGroup L) :
    ofIntegralLinearEquivGramPreserving L b (restrict L g)
      (gram_restrict L b g) = g := by
  have hLin :
      (ofIntegralLinearEquivGramPreserving L b (restrict L g)
        (gram_restrict L b g) : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap =
        (g : V ≃ₗᵢ[ℝ] V).toLinearEquiv.toLinearMap := by
    apply (b.ofZLatticeBasis ℝ L).ext
    intro i
    rw [b.ofZLatticeBasis_apply ℝ L i]
    change extendIntegralLinearEquiv L b (restrict L g) ((b i : L) : V) =
      (g : V ≃ₗᵢ[ℝ] V) ((b i : L) : V)
    rw [extendIntegralLinearEquiv_apply_basis]
    rfl
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro x
  exact LinearMap.congr_fun hLin x

/-- A unimodular integer matrix is realized as the integral-coordinate action
of an intrinsic lattice isometry if and only if it stabilizes the basis Gram
matrix. This gives the rank-independent classification criterion used to
identify symmetries of concrete Bravais metrics. -/
theorem exists_basis_coordinates_iff_gram_congruence [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Module.Basis ι ℤ L) (A : Matrix.GeneralLinearGroup ι ℤ) :
    (∃ g : latticePointGroup L, ∀ i j : ι,
      (b.repr (restrict L g (b j))) i = (A : Matrix ι ι ℤ) i j) ↔
      (let G := Matrix.gram ℝ (fun i => ((b i : L) : V))
       ((A : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ)).transpose * G *
         ((A : Matrix ι ι ℤ).map (Int.cast : ℤ → ℝ)) = G) := by
  constructor
  · rintro ⟨g, hg⟩
    let M : Matrix ι ι ℤ :=
      Matrix.of fun i j => (b.repr (restrict L g (b j))) i
    have hM : M = (A : Matrix ι ι ℤ) := by
      ext i j
      exact hg i j
    have hInv := gram_congruence L g b
    change (M.map (Int.cast : ℤ → ℝ)).transpose *
      Matrix.gram ℝ (fun i => ((b i : L) : V)) *
        (M.map (Int.cast : ℤ → ℝ)) =
      Matrix.gram ℝ (fun i => ((b i : L) : V)) at hInv
    rw [hM] at hInv
    exact hInv
  · intro hGram
    exact ⟨ofGLGramPreserving L b A hGram,
      ofGLGramPreserving_basis_coordinates L b A hGram⟩

/-- A Gram-metric stabilizer condition is invariant under an invertible
change of coordinates. In a lattice basis change the matrices `P` and `Q`
have integral entries and satisfy `Q = P⁻¹`; the statement only uses their
real inverse relations. The symmetry matrix changes by conjugation, while
the Gram matrix changes by congruence. -/
theorem gram_congruence_change_basis_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G A P Q : Matrix ι ι ℝ)
    (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    (A.transpose * G * A = G) ↔
      (Q * A * P).transpose * (P.transpose * G * P) *
        (Q * A * P) = P.transpose * G * P := by
  have forward (G A P Q : Matrix ι ι ℝ)
      (hPQ : P * Q = 1) (h : A.transpose * G * A = G) :
      (Q * A * P).transpose * (P.transpose * G * P) *
        (Q * A * P) = P.transpose * G * P := by
    calc
      (Q * A * P).transpose * (P.transpose * G * P) *
          (Q * A * P) =
        P.transpose * A.transpose * (P * Q).transpose *
          G * (P * Q) * A * P := by
            simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = P.transpose * (A.transpose * G * A) * P := by
        rw [hPQ]
        simp only [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]
      _ = P.transpose * G * P := by rw [h]
  constructor
  · exact forward G A P Q hPQ
  · intro h
    have hBack := forward (P.transpose * G * P) (Q * A * P) Q P hQP h
    have hA : P * (Q * A * P) * Q = A := by
      calc
        P * (Q * A * P) * Q = (P * Q) * A * (P * Q) := by
          simp only [Matrix.mul_assoc]
        _ = A := by rw [hPQ]; simp
    have hG :
        Q.transpose * (P.transpose * G * P) * Q = G := by
      calc
        Q.transpose * (P.transpose * G * P) * Q =
            (P * Q).transpose * G * (P * Q) := by
              simp only [Matrix.transpose_mul, Matrix.mul_assoc]
        _ = G := by rw [hPQ]; simp
    rw [hA, hG] at hBack
    exact hBack

end

end latticePointGroup

end LeanCondensedMatter.Crystal
