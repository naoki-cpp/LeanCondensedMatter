import LeanCondensedMatter.Analysis.Operator.DiagonalExpectation
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pointwise Berry connection and differentiated eigenpair identities

This module provides the finite-dimensional, pointwise spectral data needed by Berry-geometry
consumers without choosing a global gauge of eigenvectors over parameter space.

At one parameter point we store an orthonormal eigenbasis of a self-adjoint Hamiltonian together
with directional derivatives of the Hamiltonian, eigenvectors, and eigenvalues indexed by a type
`κ` of parameter directions. The differentiated eigenpair and orthonormality identities are
explicit fields. They can later be supplied by a `HasFDerivAt`-based family, but that global analytic
layer is not required for the algebraic identities proved here.

The convention in direction `μ` is

```text
A_mn^μ = i ⟪φ_m, ∂_μ φ_n⟫,
F_mn^μ = ⟪φ_m, (∂_μ H) φ_n⟫.
```

The full band-index Berry-connection matrix is Hermitian for each direction; only its diagonal
entries are asserted to be real. This module deliberately does not define Berry phase along paths,
Berry curvature, transport response, or disorder.
-/

namespace BerryGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}

/-- Pointwise data for differentiating a finite orthonormal eigenbasis in indexed parameter
directions.

All directions share the same Hamiltonian, eigenbasis, and spectrum. The differentiated eigenpair
and orthonormality identities are stored directionwise. No self-adjointness assumption is imposed
on the Hamiltonian derivatives here; results that need it state it separately. -/
structure PointwiseEigenbasisData (κ ι H : Type*) [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- Hamiltonian at the chosen parameter point. -/
  hamiltonian : H →L[ℂ] H
  /-- Self-adjointness of the Hamiltonian. -/
  hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian
  /-- Complete finite orthonormal eigenbasis. -/
  eigenbasis : OrthonormalBasis ι ℂ H
  /-- Real eigenenergy of each band. -/
  energy : ι → ℝ
  /-- Eigenpair equation at the chosen parameter point. -/
  hamiltonian_eigenvector :
    ∀ n, hamiltonian (eigenbasis n) = ((energy n : ℝ) : ℂ) • eigenbasis n
  /-- Directional derivatives of the Hamiltonian. -/
  hamiltonianDerivative : κ → H →L[ℂ] H
  /-- Directional derivatives of the eigenvectors in the chosen local gauge. -/
  eigenvectorDerivative : κ → ι → H
  /-- Directional derivatives of the real eigenenergies. -/
  energyDerivative : κ → ι → ℝ
  /-- Differentiated eigenpair equation in every parameter direction. -/
  differentiatedEigenpair :
    ∀ μ n,
      hamiltonianDerivative μ (eigenbasis n) + hamiltonian (eigenvectorDerivative μ n) =
        ((energyDerivative μ n : ℝ) : ℂ) • eigenbasis n +
          ((energy n : ℝ) : ℂ) • eigenvectorDerivative μ n
  /-- Differentiated orthonormality relation in every parameter direction. -/
  differentiatedOrthonormality :
    ∀ μ m n,
      inner ℂ (eigenvectorDerivative μ m) (eigenbasis n) +
        inner ℂ (eigenbasis m) (eigenvectorDerivative μ n) = 0

namespace PointwiseEigenbasisData

private noncomputable def bornFockDerivative [DecidableEq ι]
    (eigenbasis : OrthonormalBasis ι ℂ H) (energy : ι → ℝ)
    (hamiltonianDerivative : κ → H →L[ℂ] H) (μ : κ) (n : ι) : H :=
  ∑ m : ι,
    (if m = n then 0 else
      inner ℂ (eigenbasis m) (hamiltonianDerivative μ (eigenbasis n)) /
        (((energy n - energy m : ℝ) : ℂ))) • eigenbasis m

private theorem inner_bornFockDerivative [DecidableEq ι]
    (eigenbasis : OrthonormalBasis ι ℂ H) (energy : ι → ℝ)
    (hamiltonianDerivative : κ → H →L[ℂ] H) (μ : κ) (m n : ι) :
    inner ℂ (eigenbasis m)
        (bornFockDerivative eigenbasis energy hamiltonianDerivative μ n) =
      if m = n then 0 else
        inner ℂ (eigenbasis m) (hamiltonianDerivative μ (eigenbasis n)) /
          (((energy n - energy m : ℝ) : ℂ)) := by
  classical
  have hb : ∀ i j,
      inner ℂ (eigenbasis i) (eigenbasis j) = if i = j then 1 else 0 :=
    orthonormal_iff_ite.mp eigenbasis.orthonormal
  simp [bornFockDerivative, hb]

private theorem inner_hamiltonian_of_eigenbasis
    (hamiltonian : H →L[ℂ] H) (hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian)
    (eigenbasis : OrthonormalBasis ι ℂ H) (energy : ι → ℝ)
    (hamiltonian_eigenvector :
      ∀ n, hamiltonian (eigenbasis n) = ((energy n : ℝ) : ℂ) • eigenbasis n)
    (m : ι) (x : H) :
    inner ℂ (eigenbasis m) (hamiltonian x) =
      ((energy m : ℝ) : ℂ) * inner ℂ (eigenbasis m) x := by
  calc
    inner ℂ (eigenbasis m) (hamiltonian x) =
        inner ℂ (hamiltonian (eigenbasis m)) x := by
      symm
      exact hamiltonian_selfAdjoint.isSymmetric.apply_clm _ _
    _ = inner ℂ (((energy m : ℝ) : ℂ) • eigenbasis m) x := by
      rw [hamiltonian_eigenvector]
    _ = ((energy m : ℝ) : ℂ) * inner ℂ (eigenbasis m) x := by
      rw [inner_smul_left]
      simp

private theorem star_hamiltonianDerivativeMatrixElement_of_selfAdjoint
    (eigenbasis : OrthonormalBasis ι ℂ H)
    (hamiltonianDerivative : κ → H →L[ℂ] H)
    (hamiltonianDerivative_selfAdjoint :
      ∀ μ, IsSelfAdjoint (hamiltonianDerivative μ))
    (μ : κ) (m n : ι) :
    (starRingEnd ℂ)
        (inner ℂ (eigenbasis m) (hamiltonianDerivative μ (eigenbasis n))) =
      inner ℂ (eigenbasis n) (hamiltonianDerivative μ (eigenbasis m)) := by
  calc
    (starRingEnd ℂ)
        (inner ℂ (eigenbasis m) (hamiltonianDerivative μ (eigenbasis n))) =
        inner ℂ (hamiltonianDerivative μ (eigenbasis n)) (eigenbasis m) := by
      simp [inner_conj_symm]
    _ = inner ℂ (eigenbasis n) (hamiltonianDerivative μ (eigenbasis m)) := by
      exact (hamiltonianDerivative_selfAdjoint μ).isSymmetric.apply_clm _ _

private theorem bornFockDerivative_differentiatedOrthonormality [DecidableEq ι]
    (eigenbasis : OrthonormalBasis ι ℂ H) (energy : ι → ℝ)
    (hamiltonianDerivative : κ → H →L[ℂ] H)
    (hamiltonianDerivative_selfAdjoint :
      ∀ μ, IsSelfAdjoint (hamiltonianDerivative μ))
    (hnondegenerate : ∀ m n, m ≠ n → energy m ≠ energy n)
    (μ : κ) (m n : ι) :
    inner ℂ (bornFockDerivative eigenbasis energy hamiltonianDerivative μ m)
        (eigenbasis n) +
      inner ℂ (eigenbasis m)
        (bornFockDerivative eigenbasis energy hamiltonianDerivative μ n) = 0 := by
  classical
  by_cases hmn : m = n
  · subst n
    have hdiag :=
      inner_bornFockDerivative eigenbasis energy hamiltonianDerivative μ m m
    simp at hdiag
    rw [show
      inner ℂ (bornFockDerivative eigenbasis energy hamiltonianDerivative μ m)
          (eigenbasis m) =
        (starRingEnd ℂ)
          (inner ℂ (eigenbasis m)
            (bornFockDerivative eigenbasis energy hamiltonianDerivative μ m)) by
      simp [inner_conj_symm]]
    rw [hdiag]
    simp
  · have hgap : (((energy n - energy m : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (hnondegenerate m n hmn).symm
    have hgap' : (((energy m - energy n : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (hnondegenerate m n hmn)
    rw [show
      inner ℂ (bornFockDerivative eigenbasis energy hamiltonianDerivative μ m)
          (eigenbasis n) =
        (starRingEnd ℂ)
          (inner ℂ (eigenbasis n)
            (bornFockDerivative eigenbasis energy hamiltonianDerivative μ m)) by
      simp [inner_conj_symm]]
    rw [inner_bornFockDerivative, inner_bornFockDerivative]
    simp only [if_neg hmn, if_neg (Ne.symm hmn)]
    rw [map_div,
      star_hamiltonianDerivativeMatrixElement_of_selfAdjoint
        eigenbasis hamiltonianDerivative hamiltonianDerivative_selfAdjoint]
    simp only [Complex.conj_ofReal]
    field_simp [hgap, hgap']
    ring

private theorem bornFockDerivative_differentiatedEigenpair [DecidableEq ι]
    (hamiltonian : H →L[ℂ] H) (hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian)
    (eigenbasis : OrthonormalBasis ι ℂ H) (energy : ι → ℝ)
    (hamiltonian_eigenvector :
      ∀ n, hamiltonian (eigenbasis n) = ((energy n : ℝ) : ℂ) • eigenbasis n)
    (hamiltonianDerivative : κ → H →L[ℂ] H)
    (hamiltonianDerivative_selfAdjoint :
      ∀ μ, IsSelfAdjoint (hamiltonianDerivative μ))
    (hnondegenerate : ∀ m n, m ≠ n → energy m ≠ energy n)
    (μ : κ) (n : ι) :
    hamiltonianDerivative μ (eigenbasis n) +
        hamiltonian (bornFockDerivative eigenbasis energy hamiltonianDerivative μ n) =
      ((ContinuousLinearMap.diagonalExpectationValue
          (hamiltonianDerivative μ) (hamiltonianDerivative_selfAdjoint μ)
          (eigenbasis n) : ℝ) : ℂ) • eigenbasis n +
        ((energy n : ℝ) : ℂ) •
          bornFockDerivative eigenbasis energy hamiltonianDerivative μ n := by
  classical
  apply eigenbasis.repr.injective
  ext m
  simp only [map_add, map_smul]
  rw [eigenbasis.repr_apply_apply,
    inner_hamiltonian_of_eigenbasis hamiltonian hamiltonian_selfAdjoint
      eigenbasis energy hamiltonian_eigenvector,
    eigenbasis.repr_apply_apply,
    eigenbasis.repr_apply_apply,
    inner_bornFockDerivative]
  have hb : inner ℂ (eigenbasis m) (eigenbasis n) =
      if m = n then 1 else 0 :=
    orthonormal_iff_ite.mp eigenbasis.orthonormal m n
  rw [hb]
  by_cases hmn : m = n
  · subst m
    simp only [if_pos rfl, mul_zero, add_zero, mul_one, zero_mul]
    exact ContinuousLinearMap.coe_diagonalExpectationValue_right
      (hamiltonianDerivative μ) (hamiltonianDerivative_selfAdjoint μ) (eigenbasis n)
  · simp only [if_neg hmn, mul_zero, zero_add]
    have hgap : (((energy n - energy m : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (hnondegenerate m n hmn).symm
    field_simp [hgap]
    push_cast
    ring

/-- Build pointwise Berry data from a nondegenerate orthonormal eigenbasis and self-adjoint
Hamiltonian derivatives.

The eigenvector derivative is the off-diagonal Born--Fock derivative with zero band-diagonal
component. This is a pointwise local gauge choice only; it makes no global smooth-gauge or topology
claim. -/
noncomputable def ofNondegenerateEigenbasis [DecidableEq ι]
    (hamiltonian : H →L[ℂ] H) (hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian)
    (eigenbasis : OrthonormalBasis ι ℂ H) (energy : ι → ℝ)
    (hamiltonian_eigenvector :
      ∀ n, hamiltonian (eigenbasis n) = ((energy n : ℝ) : ℂ) • eigenbasis n)
    (hamiltonianDerivative : κ → H →L[ℂ] H)
    (hamiltonianDerivative_selfAdjoint :
      ∀ μ, IsSelfAdjoint (hamiltonianDerivative μ))
    (hnondegenerate : ∀ m n, m ≠ n → energy m ≠ energy n) :
    PointwiseEigenbasisData κ ι H where
  hamiltonian := hamiltonian
  hamiltonian_selfAdjoint := hamiltonian_selfAdjoint
  eigenbasis := eigenbasis
  energy := energy
  hamiltonian_eigenvector := hamiltonian_eigenvector
  hamiltonianDerivative := hamiltonianDerivative
  eigenvectorDerivative :=
    bornFockDerivative eigenbasis energy hamiltonianDerivative
  energyDerivative := fun μ n =>
    ContinuousLinearMap.diagonalExpectationValue
      (hamiltonianDerivative μ) (hamiltonianDerivative_selfAdjoint μ) (eigenbasis n)
  differentiatedEigenpair :=
    bornFockDerivative_differentiatedEigenpair
      hamiltonian hamiltonian_selfAdjoint eigenbasis energy hamiltonian_eigenvector
        hamiltonianDerivative hamiltonianDerivative_selfAdjoint hnondegenerate
  differentiatedOrthonormality :=
    bornFockDerivative_differentiatedOrthonormality
      eigenbasis energy hamiltonianDerivative hamiltonianDerivative_selfAdjoint hnondegenerate

variable (data : PointwiseEigenbasisData κ ι H)

/-- Berry-connection matrix element in parameter direction `μ`,
`A_mn^μ = i ⟪φ_m, ∂_μ φ_n⟫`. -/
noncomputable def berryConnection (μ : κ) (m n : ι) : ℂ :=
  Complex.I * inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative μ n)

/-- Matrix element of the Hamiltonian derivative in parameter direction `μ`,
`F_mn^μ = ⟪φ_m, (∂_μ H) φ_n⟫`. -/
noncomputable def hamiltonianDerivativeMatrixElement (μ : κ) (m n : ι) : ℂ :=
  inner ℂ (data.eigenbasis m) (data.hamiltonianDerivative μ (data.eigenbasis n))

/-- Moving a self-adjoint Hamiltonian from the right slot of the inner product to the left and
using the eigenpair equation multiplies by the corresponding real eigenenergy. -/
theorem inner_hamiltonian_right (m : ι) (x : H) :
    inner ℂ (data.eigenbasis m) (data.hamiltonian x) =
      ((data.energy m : ℝ) : ℂ) * inner ℂ (data.eigenbasis m) x := by
  calc
    inner ℂ (data.eigenbasis m) (data.hamiltonian x) =
        inner ℂ (data.hamiltonian (data.eigenbasis m)) x := by
      symm
      exact data.hamiltonian_selfAdjoint.isSymmetric.apply_clm _ _
    _ = inner ℂ (((data.energy m : ℝ) : ℂ) • data.eigenbasis m) x := by
      rw [data.hamiltonian_eigenvector]
    _ = ((data.energy m : ℝ) : ℂ) * inner ℂ (data.eigenbasis m) x := by
      rw [inner_smul_left]
      simp

/-- The Berry-connection matrix is Hermitian in band indices for every parameter direction:
`(A_mn^μ)⁎ = A_nm^μ`. In particular, off-diagonal entries are not asserted to be real. -/
theorem star_berryConnection (μ : κ) (m n : ι) :
    (starRingEnd ℂ) (data.berryConnection μ m n) = data.berryConnection μ n m := by
  calc
    (starRingEnd ℂ) (data.berryConnection μ m n) =
        -Complex.I * inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) := by
      simp [berryConnection, inner_conj_symm]
    _ = Complex.I * inner ℂ (data.eigenbasis n) (data.eigenvectorDerivative μ m) := by
      have horth := data.differentiatedOrthonormality μ n m
      linear_combination (-Complex.I) * horth
    _ = data.berryConnection μ n m := rfl

/-- A diagonal Berry connection is real, expressed as vanishing imaginary part. -/
theorem berryConnection_diagonal_im_eq_zero (μ : κ) (n : ι) :
    (data.berryConnection μ n n).im = 0 := by
  have h := congrArg Complex.im (data.star_berryConnection μ n n)
  simp at h
  linarith

/-- Hellmann--Feynman theorem in parameter direction `μ`:
`∂_μ E_n = ⟪φ_n, (∂_μ H) φ_n⟫`. -/
theorem hellmannFeynman (μ : κ) (n : ι) :
    ((data.energyDerivative μ n : ℝ) : ℂ) =
      data.hamiltonianDerivativeMatrixElement μ n n := by
  have h := congrArg (fun x : H => inner ℂ (data.eigenbasis n) x)
    (data.differentiatedEigenpair μ n)
  simp only [inner_add_right, inner_smul_right] at h
  rw [data.inner_hamiltonian_right n, data.eigenbasis.inner_eq_one] at h
  simp only [mul_one] at h
  unfold hamiltonianDerivativeMatrixElement
  linear_combination -h

/-- Born--Fock off-diagonal eigenvector-derivative formula in parameter direction `μ`.

The nondegeneracy needed for division by the level spacing is an explicit theorem hypothesis rather
than a global restriction on `PointwiseEigenbasisData`. -/
theorem bornFock_inner (μ : κ) {m n : ι} (hmn : m ≠ n)
    (henergy : data.energy m ≠ data.energy n) :
    inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative μ n) =
      data.hamiltonianDerivativeMatrixElement μ m n /
        (((data.energy n - data.energy m : ℝ) : ℂ)) := by
  have h := congrArg (fun x : H => inner ℂ (data.eigenbasis m) x)
    (data.differentiatedEigenpair μ n)
  simp only [inner_add_right, inner_smul_right] at h
  rw [data.inner_hamiltonian_right m, data.eigenbasis.inner_eq_zero hmn] at h
  simp only [mul_zero, zero_add] at h
  have hgap : (((data.energy n - data.energy m : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr henergy.symm
  apply (eq_div_iff hgap).2
  unfold hamiltonianDerivativeMatrixElement
  have hF :
      inner ℂ (data.eigenbasis m) (data.hamiltonianDerivative μ (data.eigenbasis n)) =
        ((data.energy n : ℝ) : ℂ) *
            inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative μ n) -
          ((data.energy m : ℝ) : ℂ) *
            inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative μ n) :=
    (eq_sub_iff_add_eq).2 h
  rw [hF]
  push_cast
  ring

/-- Born--Fock formula in Berry-connection form. -/
theorem bornFock_berryConnection (μ : κ) {m n : ι} (hmn : m ≠ n)
    (henergy : data.energy m ≠ data.energy n) :
    data.berryConnection μ m n =
      Complex.I * data.hamiltonianDerivativeMatrixElement μ m n /
        (((data.energy n - data.energy m : ℝ) : ℂ)) := by
  rw [berryConnection, data.bornFock_inner μ hmn henergy]
  ring

end PointwiseEigenbasisData

end
end BerryGeometry
