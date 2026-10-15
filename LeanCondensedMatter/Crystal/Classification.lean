/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
import LeanCondensedMatter.Crystal.Periodicity
import LeanCondensedMatter.Crystal.PointGroup
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Order.Floor.Ring
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
  have hLin :
      (restrict L (ofGLGramPreserving L b A hGram)).toLinearMap =
        (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv.toLinearMap := by
    apply b.ext
    intro i
    apply Subtype.ext
    change
      extendIntegralLinearEquiv L b
        (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv ((b i : L) : V) =
          (((Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv (b i) : L) : V)
    exact extendIntegralLinearEquiv_apply_basis L b
      (Matrix.GeneralLinearGroup.toLin' b A).toLinearEquiv i
  exact LinearEquiv.ext (fun x => LinearMap.congr_fun hLin x)

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

/-- An integer shear of a planar primitive basis is unimodular. -/
theorem integerShear_det (n : ℤ) :
    (Matrix.det (!![(1 : ℤ), -n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ)) = 1 := by
  simp [Matrix.det_fin_two]

/-- The elementary integral shear `e₂ ↦ e₂ - n e₁` changes the Gram
coefficients by the standard binary-quadratic-form substitution. Together
with `integerShear_det`, this is a primitive lattice-basis operation. -/
theorem gram_integerShear
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) (n : ℤ) :
    (let T : Matrix (Fin 2) (Fin 2) ℝ := !![1, -(n : ℝ); 0, 1]
     T.transpose * G * T =
       !![G 0 0, G 0 1 - (n : ℝ) * G 0 0;
          G 0 1 - (n : ℝ) * G 0 0,
          G 1 1 - 2 * (n : ℝ) * G 0 1 + (n : ℝ) ^ 2 * G 0 0]) := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← hSymm] <;> ring

/-- Every positive planar first Gram coefficient admits an integer shear
that reduces the off-diagonal entry to at most half of that coefficient in
absolute value. This is the size-reduction step of Gauss lattice reduction;
it does not yet assert the ordering of the two diagonal coefficients. -/
theorem exists_gram_integerShear_reduced
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) (hPos : 0 < G 0 0) :
    ∃ n : ℤ,
      |G 0 1 - (n : ℝ) * G 0 0| ≤ G 0 0 / 2 ∧
      (let T : Matrix (Fin 2) (Fin 2) ℝ := !![1, -(n : ℝ); 0, 1]
       T.transpose * G * T =
         !![G 0 0, G 0 1 - (n : ℝ) * G 0 0;
            G 0 1 - (n : ℝ) * G 0 0,
            G 1 1 - 2 * (n : ℝ) * G 0 1 + (n : ℝ) ^ 2 * G 0 0]) := by
  let a : ℝ := G 0 0
  let b : ℝ := G 0 1
  let x : ℝ := b / a + 1 / 2
  let n : ℤ := ⌊x⌋
  have ha : 0 < a := hPos
  have hane : a ≠ 0 := ne_of_gt ha
  have hnLow : (n : ℝ) ≤ x := Int.floor_le x
  have hnHigh : x < (n : ℝ) + 1 := Int.lt_floor_add_one x
  have hLower : -(a / 2) ≤ b - (n : ℝ) * a := by
    have h := mul_le_mul_of_nonneg_right hnLow ha.le
    change (n : ℝ) * a ≤ (b / a + 1 / 2) * a at h
    rw [add_mul, div_mul_cancel₀ b hane] at h
    nlinarith
  have hUpper : b - (n : ℝ) * a ≤ a / 2 := by
    have h := mul_lt_mul_of_pos_right hnHigh ha
    change (b / a + 1 / 2) * a < ((n : ℝ) + 1) * a at h
    rw [add_mul, div_mul_cancel₀ b hane] at h
    nlinarith
  refine ⟨n, ?_, gram_integerShear G hSymm n⟩
  change |b - (n : ℝ) * a| ≤ a / 2
  exact abs_le.mpr ⟨hLower, hUpper⟩

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

/-- The sum and difference of two primitive lattice vectors form an orthogonal
conventional cell exactly when the vectors have equal squared lengths.

For a symmetric Gram metric `G`, the columns of `S = !![1, 1; 1, -1]`
are the sum and difference of the primitive basis vectors. When `G₀₀ = G₁₁`,
the conventional squared lengths are `2 * (G₀₀ + G₀₁)` and
`2 * (G₀₀ - G₀₁)`. This is the metric relation underlying the
centered-rectangular Bravais class. The matrix `S` has determinant `-2`,
so this conventional cell is not an integral primitive basis change. -/
theorem gram_sumDiff_diagonal_iff (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) :
    (let S : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, -1];
     S.transpose * G * S =
       !![2 * (G 0 0 + G 0 1), 0;
          0, 2 * (G 0 0 - G 0 1)]) ↔ G 0 0 = G 1 1 := by
  constructor
  · intro h
    dsimp at h
    have h01 := congrArg
      (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h01
    linarith
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
