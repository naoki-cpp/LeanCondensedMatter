import LeanCondensedMatter.Analysis.Operator.Spectral.BerryConnection
import Mathlib.Data.Complex.BigOperators

set_option linter.style.header false

/-!
# Pointwise Berry curvature and force-matrix representation

This module extends the one-direction spectral data in `BerryConnection` to a family of parameter
directions sharing one Hamiltonian, eigenbasis, and spectrum.  Each direction reduces to the
existing `DirectionalEigenbasisData`, so Hellmann--Feynman and Born--Fock are reused rather than
reproved.

The pointwise Berry curvature convention is

```text
Ω_n^{μν} = -2 Im ⟪∂_μ φ_n, ∂_ν φ_n⟫.
```

For self-adjoint Hamiltonian derivatives and a nondegenerate band `n`, completeness plus the
Born--Fock formula give the finite-band force-matrix representation.  No global gauge choice,
parameter-space topology, transport response, or disorder is introduced here.
-/

namespace BerryGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}

/-- Pointwise differentiated spectral data for several parameter directions.

All directions share the same self-adjoint Hamiltonian, finite orthonormal eigenbasis, and real
spectrum.  The derivative of the Hamiltonian is required to be self-adjoint in every direction;
this is the pointwise property needed to convert conjugated derivative matrix elements into the
standard interband force-matrix ordering. -/
structure MultidirectionalEigenbasisData (κ ι H : Type*) [Fintype ι]
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
  /-- Every directional Hamiltonian derivative is self-adjoint. -/
  hamiltonianDerivative_selfAdjoint : ∀ μ, IsSelfAdjoint (hamiltonianDerivative μ)
  /-- Directional derivatives of the eigenvectors in a chosen local gauge. -/
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

namespace MultidirectionalEigenbasisData

variable (data : MultidirectionalEigenbasisData κ ι H)

/-- Restrict multidirectional data to one parameter direction. -/
noncomputable def direction (μ : κ) : DirectionalEigenbasisData ι H where
  hamiltonian := data.hamiltonian
  hamiltonian_selfAdjoint := data.hamiltonian_selfAdjoint
  eigenbasis := data.eigenbasis
  energy := data.energy
  hamiltonian_eigenvector := data.hamiltonian_eigenvector
  hamiltonianDerivative := data.hamiltonianDerivative μ
  eigenvectorDerivative := data.eigenvectorDerivative μ
  energyDerivative := data.energyDerivative μ
  differentiatedEigenpair := data.differentiatedEigenpair μ
  differentiatedOrthonormality := data.differentiatedOrthonormality μ

/-- Hamiltonian-derivative matrix element in direction `μ`. -/
noncomputable def hamiltonianDerivativeMatrixElement (μ : κ) (m n : ι) : ℂ :=
  inner ℂ (data.eigenbasis m) (data.hamiltonianDerivative μ (data.eigenbasis n))

@[simp]
theorem direction_hamiltonianDerivativeMatrixElement (μ : κ) (m n : ι) :
    (data.direction μ).hamiltonianDerivativeMatrixElement m n =
      data.hamiltonianDerivativeMatrixElement μ m n := rfl

/-- Self-adjointness of `∂_μ H` makes its band matrix Hermitian. -/
theorem star_hamiltonianDerivativeMatrixElement (μ : κ) (m n : ι) :
    (starRingEnd ℂ) (data.hamiltonianDerivativeMatrixElement μ m n) =
      data.hamiltonianDerivativeMatrixElement μ n m := by
  calc
    (starRingEnd ℂ) (data.hamiltonianDerivativeMatrixElement μ m n) =
        inner ℂ (data.hamiltonianDerivative μ (data.eigenbasis n)) (data.eigenbasis m) := by
      simp [hamiltonianDerivativeMatrixElement, inner_conj_symm]
    _ = inner ℂ (data.eigenbasis n) (data.hamiltonianDerivative μ (data.eigenbasis m)) := by
      exact (data.hamiltonianDerivative_selfAdjoint μ).isSymmetric.apply_clm _ _
    _ = data.hamiltonianDerivativeMatrixElement μ n m := rfl

/-- Pointwise Berry curvature from two eigenvector derivatives. -/
noncomputable def berryCurvature (μ ν : κ) (n : ι) : ℝ :=
  -2 * (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenvectorDerivative ν n)).im

/-- Berry curvature is antisymmetric in its two parameter directions. -/
theorem berryCurvature_swap (μ ν : κ) (n : ι) :
    data.berryCurvature ν μ n = -data.berryCurvature μ ν n := by
  unfold berryCurvature
  rw [inner_im_symm]
  ring

/-- Completeness of the finite orthonormal eigenbasis expands the derivative-state curvature into
band-resolved inner-product terms. -/
theorem berryCurvature_eq_sum_innerProducts (μ ν : κ) (n : ι) :
    data.berryCurvature μ ν n =
      ∑ m : ι,
        -2 * (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) *
          inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative ν n)).im := by
  have hsum := data.eigenbasis.sum_inner_mul_inner
    (data.eigenvectorDerivative μ n) (data.eigenvectorDerivative ν n)
  calc
    data.berryCurvature μ ν n =
        -2 * (inner ℂ (data.eigenvectorDerivative μ n)
          (data.eigenvectorDerivative ν n)).im := rfl
    _ = -2 * (∑ m : ι,
          inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) *
            inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative ν n)).im := by
      rw [hsum]
    _ = -2 * ∑ m : ι,
          (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) *
            inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative ν n)).im := by
      rw [Complex.im_sum]
    _ = ∑ m : ι,
        -2 * (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) *
          inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative ν n)).im := by
      rw [Finset.mul_sum]

/-- The band-diagonal completeness term has zero imaginary part.  It therefore does not contribute
to Berry curvature. -/
theorem diagonal_innerProduct_im_eq_zero (μ ν : κ) (n : ι) :
    (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis n) *
      inner ℂ (data.eigenbasis n) (data.eigenvectorDerivative ν n)).im = 0 := by
  have hμ := congrArg Complex.re (data.differentiatedOrthonormality μ n n)
  have hν := congrArg Complex.re (data.differentiatedOrthonormality ν n n)
  simp only [Complex.add_re, Complex.zero_re] at hμ hν
  have hμsym := inner_re_symm (𝕜 := ℂ)
    (data.eigenvectorDerivative μ n) (data.eigenbasis n)
  have hνsym := inner_re_symm (𝕜 := ℂ)
    (data.eigenvectorDerivative ν n) (data.eigenbasis n)
  have hμre : (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis n)).re = 0 := by
    linarith
  have hνre : (inner ℂ (data.eigenbasis n) (data.eigenvectorDerivative ν n)).re = 0 := by
    linarith
  simp [Complex.mul_im, hμre, hνre]

/-- The left derivative-state matrix element is the Hermitian-conjugate Born--Fock term. -/
theorem innerDerivative_basis_eq_hamiltonianDerivativeMatrixElement_div
    (μ : κ) {m n : ι} (hmn : m ≠ n) (henergy : data.energy m ≠ data.energy n) :
    inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) =
      data.hamiltonianDerivativeMatrixElement μ n m /
        (((data.energy n - data.energy m : ℝ) : ℂ)) := by
  have hbf := (data.direction μ).bornFock_inner hmn henergy
  have hbf' :
      inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative μ n) =
        data.hamiltonianDerivativeMatrixElement μ m n /
          (((data.energy n - data.energy m : ℝ) : ℂ)) := by
    simpa [direction, hamiltonianDerivativeMatrixElement] using hbf
  calc
    inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) =
        (starRingEnd ℂ)
          (inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative μ n)) := by
      simp [inner_conj_symm]
    _ = (starRingEnd ℂ)
          (data.hamiltonianDerivativeMatrixElement μ m n /
            (((data.energy n - data.energy m : ℝ) : ℂ))) := by
      rw [hbf']
    _ = data.hamiltonianDerivativeMatrixElement μ n m /
        (((data.energy n - data.energy m : ℝ) : ℂ)) := by
      simp [data.star_hamiltonianDerivativeMatrixElement]

/-- An off-diagonal completeness term equals the conventional force-matrix Berry-curvature term.
The complex denominator is the real level spacing embedded in `ℂ`; keeping it inside `im` avoids
introducing any additional real/complex coercion API at this layer. -/
theorem curvatureInnerTerm_eq_hamiltonianDerivativeMatrixElements
    (μ ν : κ) {m n : ι} (hmn : m ≠ n) (henergy : data.energy m ≠ data.energy n) :
    -2 * (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) *
      inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative ν n)).im =
      2 * ((data.hamiltonianDerivativeMatrixElement μ m n *
        data.hamiltonianDerivativeMatrixElement ν n m) /
          (((data.energy n - data.energy m : ℝ) : ℂ) ^ 2)).im := by
  have hbfν := (data.direction ν).bornFock_inner hmn henergy
  have hbfν' :
      inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative ν n) =
        data.hamiltonianDerivativeMatrixElement ν m n /
          (((data.energy n - data.energy m : ℝ) : ℂ)) := by
    simpa [direction, hamiltonianDerivativeMatrixElement] using hbfν
  rw [data.innerDerivative_basis_eq_hamiltonianDerivativeMatrixElement_div μ hmn henergy]
  rw [hbfν']
  let z : ℂ :=
    (data.hamiltonianDerivativeMatrixElement μ n m /
      (((data.energy n - data.energy m : ℝ) : ℂ))) *
    (data.hamiltonianDerivativeMatrixElement ν m n /
      (((data.energy n - data.energy m : ℝ) : ℂ)))
  have hstar :
      (starRingEnd ℂ) z =
        (data.hamiltonianDerivativeMatrixElement μ m n *
          data.hamiltonianDerivativeMatrixElement ν n m) /
            (((data.energy n - data.energy m : ℝ) : ℂ) ^ 2) := by
    dsimp [z]
    simp [data.star_hamiltonianDerivativeMatrixElement]
    ring
  have him := congrArg Complex.im hstar
  simp at him
  change -2 * z.im =
    2 * ((data.hamiltonianDerivativeMatrixElement μ m n *
      data.hamiltonianDerivativeMatrixElement ν n m) /
        (((data.energy n - data.energy m : ℝ) : ℂ) ^ 2)).im
  linarith

/-- Force/Hamiltonian-derivative matrix-element representation of Berry curvature for a
nondegenerate band.

This is the finite-dimensional pointwise formula needed by the clean anomalous-Hall consumer. -/
theorem berryCurvature_eq_sum_hamiltonianDerivativeMatrixElements [DecidableEq ι]
    (μ ν : κ) (n : ι)
    (hnondegenerate : ∀ m, m ≠ n → data.energy m ≠ data.energy n) :
    data.berryCurvature μ ν n =
      ∑ m : ι, if m = n then 0 else
        2 * ((data.hamiltonianDerivativeMatrixElement μ m n *
          data.hamiltonianDerivativeMatrixElement ν n m) /
            (((data.energy n - data.energy m : ℝ) : ℂ) ^ 2)).im := by
  rw [data.berryCurvature_eq_sum_innerProducts]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    rw [data.diagonal_innerProduct_im_eq_zero]
    ring
  · rw [if_neg hmn]
    exact data.curvatureInnerTerm_eq_hamiltonianDerivativeMatrixElements μ ν hmn
      (hnondegenerate m hmn)

end MultidirectionalEigenbasisData

end
end BerryGeometry
