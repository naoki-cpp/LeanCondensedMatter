/-
Copyright (c) 2026 Naoki Yano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naoki Yano
-/
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
# Gauss reduction of planar lattice bases

Integer shears and swaps act on planar Gram matrices. Discreteness gives finitely many
bounded lattice vectors and a shortest primitive basis vector, from which a Gauss-reduced
basis is constructed.
-/

namespace LeanCondensedMatter.Crystal

namespace latticePointGroup

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable section

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
    (let T : Matrix (Fin 2) (Fin 2) ℝ := !![1, -(n : ℝ); 0, 1];
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
      (let T : Matrix (Fin 2) (Fin 2) ℝ := !![1, -(n : ℝ); 0, 1];
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

/-- Swapping the planar basis vectors and then applying an integer shear
is an integral primitive basis change of determinant minus one. -/
theorem integerSwapShear_det (n : ℤ) :
    (Matrix.det (!![(0 : ℤ), 1; 1, -n] : Matrix (Fin 2) (Fin 2) ℤ)) = -1 := by
  simp [Matrix.det_fin_two]

/-- Under the swap-and-shear primitive basis change
`e₁' = e₂`, `e₂' = e₁ - n e₂`, the Gram coefficients transform
by the binary quadratic form substitution with the shorter vector first. -/
theorem gram_integerSwapShear
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0) (n : ℤ) :
    (let U : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, -(n : ℝ)];
     U.transpose * G * U =
       !![G 1 1, G 0 1 - (n : ℝ) * G 1 1;
          G 0 1 - (n : ℝ) * G 1 1,
          G 0 0 - 2 * (n : ℝ) * G 0 1 + (n : ℝ) ^ 2 * G 1 1]) := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ← hSymm] <;> ring

/-- If the second primitive vector is shorter than the first, swapping the
vectors and size-reducing by an integer shear gives a new primitive basis
whose first squared length strictly decreases and whose off-diagonal Gram
coefficient is at most half that first squared length.

This is the descent step of the Gauss algorithm. Termination requires an
additional discreteness argument for the squared lengths of lattice vectors. -/
theorem exists_gram_swapShear_descends
    (G : Matrix (Fin 2) (Fin 2) ℝ)
    (hSymm : G 0 1 = G 1 0)
    (hPos : 0 < G 1 1) (hLess : G 1 1 < G 0 0) :
    ∃ n : ℤ,
      |G 0 1 - (n : ℝ) * G 1 1| ≤ G 1 1 / 2 ∧
      (let U : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, -(n : ℝ)];
       (U.transpose * G * U) 0 0 < G 0 0 ∧
       U.transpose * G * U =
         !![G 1 1, G 0 1 - (n : ℝ) * G 1 1;
            G 0 1 - (n : ℝ) * G 1 1,
            G 0 0 - 2 * (n : ℝ) * G 0 1 + (n : ℝ) ^ 2 * G 1 1]) := by
  let H : Matrix (Fin 2) (Fin 2) ℝ :=
    !![G 1 1, G 0 1; G 0 1, G 0 0]
  have hHSymm : H 0 1 = H 1 0 := by simp [H]
  have hHPos : 0 < H 0 0 := by simpa [H] using hPos
  obtain ⟨n, hn, _⟩ := exists_gram_integerShear_reduced H hHSymm hHPos
  refine ⟨n, ?_, ?_⟩
  · simpa [H] using hn
  · have hGram := gram_integerSwapShear G hSymm n
    dsimp at hGram ⊢
    constructor
    · rw [hGram]
      simpa using hLess
    · exact hGram

/-- A discrete integral submodule of a finite-dimensional real normed space
has only finitely many vectors of bounded norm. In particular, the first
squared length of any primitive lattice basis takes values in a finite set
as long as it remains below a fixed bound. -/
theorem finite_lattice_vectors_norm_le [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] (R : ℝ) :
    {x : L | ‖x‖ ≤ R}.Finite := by
  have hClosed : IsClosed (L : Set V) := by
    change IsClosed ((L.toAddSubgroup : AddSubgroup V) : Set V)
    infer_instance
  letI : ProperSpace L := ProperSpace.of_isClosed hClosed
  have hCompact : IsCompact (Metric.closedBall (0 : L) R) :=
    isCompact_closedBall (0 : L) R
  have hFinite := hCompact.finite_of_discrete
  simpa only [Metric.closedBall, Set.mem_ofPred_eq, dist_zero_right] using hFinite

/-- Among all integral bases of a discrete planar lattice, there is a basis
whose first vector has globally minimal norm. Its first vector is no longer
than its second vector, because swapping the vectors is again an integral
basis. This supplies the shortest-primitive-vector starting point for Gauss
basis reduction without assuming a preselected reduced basis. -/
theorem exists_basis_shortest_first_vector [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L]
    (b : Module.Basis (Fin 2) ℤ L) :
    ∃ c : Module.Basis (Fin 2) ℤ L,
      (∀ d : Module.Basis (Fin 2) ℤ L, ‖c 0‖ ≤ ‖d 0‖) ∧
        ‖c 0‖ ≤ ‖c 1‖ := by
  classical
  let S : Set L :=
    {v | (∃ d : Module.Basis (Fin 2) ℤ L, d 0 = v) ∧ ‖v‖ ≤ ‖b 0‖}
  have hFinite : S.Finite :=
    (finite_lattice_vectors_norm_le L ‖b 0‖).subset (by
      intro v hv
      exact hv.2)
  have hNonempty : S.Nonempty := by
    refine ⟨b 0, ?_⟩
    exact ⟨⟨b, rfl⟩, le_rfl⟩
  obtain ⟨v, hv, hMinimal⟩ :=
    Set.exists_min_image S (fun x : L => ‖x‖) hFinite hNonempty
  obtain ⟨c, hc⟩ := hv.1
  have hBound : ‖c 0‖ ≤ ‖b 0‖ := by
    rw [hc]
    exact hv.2
  have hLeast (d : Module.Basis (Fin 2) ℤ L) : ‖c 0‖ ≤ ‖d 0‖ := by
    by_cases hd : ‖d 0‖ ≤ ‖b 0‖
    · have hdS : d 0 ∈ S := ⟨⟨d, rfl⟩, hd⟩
      rw [hc]
      exact hMinimal (d 0) hdS
    · exact hBound.trans (le_of_lt (lt_of_not_ge hd))
  refine ⟨c, hLeast, ?_⟩
  have hSwap := hLeast (c.reindex (Equiv.swap (0 : Fin 2) 1))
  simpa [Module.Basis.reindex_apply] using hSwap


/-- The elementary shear on the integer coordinate plane. -/
private def integerShearCoordinates (n : ℤ) :
    (Fin 2 → ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x 0 + n * x 1, x 1]
  invFun x := ![x 0 - n * x 1, x 1]
  left_inv x := by
    funext i
    fin_cases i <;> simp
  right_inv x := by
    funext i
    fin_cases i <;> simp
  map_add' x y := by
    funext i
    fin_cases i <;> simp; ring
  map_smul' r x := by
    funext i
    fin_cases i <;> simp; ring

/-- Change the second vector of an integral basis by an integer multiple
of its first vector, without changing the first vector or the lattice. -/
private noncomputable def integerShearBasis
    {L : Submodule ℤ V}
    (c : Module.Basis (Fin 2) ℤ L) (n : ℤ) :
    Module.Basis (Fin 2) ℤ L :=
  c.map (((c.equivFun).trans (integerShearCoordinates (-n))).trans c.equivFun.symm)

omit [InnerProductSpace ℝ V] in
private theorem integerShearBasis_apply_zero
    {L : Submodule ℤ V}
    (c : Module.Basis (Fin 2) ℤ L) (n : ℤ) :
    integerShearBasis c n 0 = c 0 := by
  apply c.equivFun.injective
  ext i
  fin_cases i <;>
    simp [integerShearBasis, integerShearCoordinates, Module.Basis.map_apply,
      Module.Basis.equivFun_self]

omit [InnerProductSpace ℝ V] in
private theorem integerShearBasis_apply_one
    {L : Submodule ℤ V}
    (c : Module.Basis (Fin 2) ℤ L) (n : ℤ) :
    integerShearBasis c n 1 = c 1 - n • c 0 := by
  apply c.equivFun.injective
  ext i
  fin_cases i <;>
    simp [integerShearBasis, integerShearCoordinates, Module.Basis.map_apply]

/-- Every discrete rank-two integral lattice admits a Gauss-reduced primitive
basis. Its Gram matrix has nondecreasing diagonal coefficients and its
off-diagonal coefficient is at most half the first diagonal coefficient
in absolute value. The proof minimizes the first primitive basis vector
globally and then uses an integral shear, which keeps that vector fixed. -/
theorem exists_gauss_reduced_basis [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L]
    (b : Module.Basis (Fin 2) ℤ L) :
    ∃ d : Module.Basis (Fin 2) ℤ L,
      let G := Matrix.gram ℝ (fun i => ((d i : L) : V))
      G 0 0 ≤ G 1 1 ∧ 2 * |G 0 1| ≤ G 0 0 := by
  classical
  obtain ⟨c, hMinimal, _⟩ := exists_basis_shortest_first_vector L b
  let G : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.gram ℝ (fun i => ((c i : L) : V))
  have hSymm : G 0 1 = G 1 0 := by
    simp only [G, Matrix.gram_apply]
    exact real_inner_comm _ _
  have hPos : 0 < G 0 0 := by
    change 0 < inner ℝ ((c 0 : L) : V) ((c 0 : L) : V)
    rw [real_inner_self_eq_norm_sq]
    have hNonzero : (((c 0 : L) : V)) ≠ 0 := by
      exact Subtype.coe_ne_coe.mpr (c.ne_zero 0)
    exact sq_pos_of_pos (norm_pos_iff.mpr hNonzero)
  obtain ⟨n, hn, _⟩ := exists_gram_integerShear_reduced G hSymm hPos
  let d := integerShearBasis c n
  have hd0 : d 0 = c 0 := integerShearBasis_apply_zero c n
  have hd1 : d 1 = c 1 - n • c 0 := integerShearBasis_apply_one c n
  have hNorm : ‖c 0‖ ≤ ‖d 1‖ := by
    have h := hMinimal (d.reindex (Equiv.swap (0 : Fin 2) 1))
    simpa [Module.Basis.reindex_apply] using h
  have hSq : ‖c 0‖ ^ 2 ≤ ‖d 1‖ ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr hNorm)
      (add_nonneg (norm_nonneg (c 0)) (norm_nonneg (d 1)))
    nlinarith
  have hOff : inner ℝ ((d 0 : L) : V) ((d 1 : L) : V) =
      G 0 1 - (n : ℝ) * G 0 0 := by
    rw [hd0, hd1]
    simp only [G, Matrix.gram_apply]
    simp only [Fin.isValue, AddSubgroupClass.coe_sub, SetLike.val_smul,
      inner_self_eq_norm_sq_to_K, RCLike.ofReal_real_eq_id, id_eq]
    rw [inner_sub_right]
    rw [← Int.cast_smul_eq_zsmul ℝ n ((c 0 : L) : V)]
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  refine ⟨d, ?_⟩
  dsimp
  constructor
  · simp only [real_inner_self_eq_norm_sq]
    rw [hd0]
    exact hSq
  · simp only [hOff]
    have hGdiag : G 0 0 = ‖c 0‖ ^ 2 := by
      simp [G, Matrix.gram_apply]
    have hh : 2 * |G 0 1 - (n : ℝ) * G 0 0| ≤ G 0 0 := by
      linarith [hn]
    rw [hd0]
    simpa [real_inner_self_eq_norm_sq, hGdiag] using hh

/-- An infinite sequence of lattice vectors cannot remain bounded while its
squared norms strictly decrease at every step. Applied to the first vectors
of successive primitive bases, this rules out infinitely many swap-and-shear
descent steps from a fixed initial metric.

The separate task of assembling a Gauss-reduced basis still has to track
the basis transformations between steps. -/
theorem not_exists_bounded_strict_norm_sq_descent [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] (R : ℝ) :
    ¬ ∃ v : ℕ → L,
      (∀ n, ‖v n‖ ≤ R) ∧
        (∀ n, ‖v (n + 1)‖ ^ 2 < ‖v n‖ ^ 2) := by
  rintro ⟨v, hv, hdesc⟩
  have hFinite : (Set.range v).Finite :=
    (finite_lattice_vectors_norm_le L R).subset (by
      rintro x ⟨n, rfl⟩
      exact hv n)
  have hStrict : StrictAnti (fun n : ℕ => ‖v n‖ ^ 2) :=
    strictAnti_nat_of_succ_lt hdesc
  have hInj : Function.Injective v := by
    intro m n hmn
    apply hStrict.injective
    exact congrArg (fun x : L => ‖x‖ ^ 2) hmn
  exact (Set.infinite_range_of_injective hInj) hFinite

end

end latticePointGroup

end LeanCondensedMatter.Crystal
