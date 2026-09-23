import LeanCondensedMatter.Analysis.Operator.BerryGeometry.Connection
import Mathlib.Data.Complex.BigOperators

set_option linter.style.header false

/-!
# Pointwise Berry curvature and force-matrix representation

This module uses the direction-indexed pointwise spectral data from `BerryGeometry.Connection`. Berry
connection, Hellmann--Feynman, and Born--Fock identities are already stated directionwise on the
same `PointwiseEigenbasisData`, so curvature proofs specialize them directly without constructing a
second one-direction record.

For the standard Berry-curvature and force-matrix framework used here, see Xiao, Chang, and Niu,
*Rev. Mod. Phys.* **82**, 1959–2007 (2010),
[doi:10.1103/RevModPhys.82.1959](https://doi.org/10.1103/RevModPhys.82.1959). The sign is fixed by
the displayed convention, and no global-gauge or topology claim is imported.

The pointwise Berry curvature convention is

```text
Ω_n^{μν} = -2 Im ⟪∂_μ φ_n, ∂_ν φ_n⟫.
```

For self-adjoint Hamiltonian derivatives and a nondegenerate band `n`, completeness plus the
Born--Fock formula give the finite-band force-matrix representation. Self-adjointness of the
Hamiltonian derivatives is kept as an explicit curvature-side hypothesis rather than strengthening
the shared pointwise spectral-data owner. No global gauge choice, parameter-space topology,
transport response, or disorder is introduced here.
-/

namespace BerryGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι]
variable {κ : Type*}

namespace PointwiseEigenbasisData

variable (data : PointwiseEigenbasisData κ ι H)

/-- Self-adjointness of `∂_μ H` makes its band matrix Hermitian. -/
theorem star_hamiltonianDerivativeMatrixElement
    (μ : κ) (hself : IsSelfAdjoint (data.hamiltonianDerivative μ)) (m n : ι) :
    (starRingEnd ℂ) (data.hamiltonianDerivativeMatrixElement μ m n) =
      data.hamiltonianDerivativeMatrixElement μ n m := by
  calc
    (starRingEnd ℂ) (data.hamiltonianDerivativeMatrixElement μ m n) =
        inner ℂ (data.hamiltonianDerivative μ (data.eigenbasis n)) (data.eigenbasis m) := by
      simp [hamiltonianDerivativeMatrixElement, inner_conj_symm]
    _ = inner ℂ (data.eigenbasis n) (data.hamiltonianDerivative μ (data.eigenbasis m)) := by
      exact hself.isSymmetric.apply_clm _ _
    _ = data.hamiltonianDerivativeMatrixElement μ n m := rfl

/-- Pointwise Berry curvature from two eigenvector derivatives. -/
noncomputable def berryCurvature (μ ν : κ) (n : ι) : ℝ :=
  -2 * (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenvectorDerivative ν n)).im

/-- Berry curvature is antisymmetric in its two parameter directions. -/
theorem berryCurvature_swap (μ ν : κ) (n : ι) :
    data.berryCurvature ν μ n = -data.berryCurvature μ ν n := by
  unfold berryCurvature
  have him :
      -(inner ℂ (data.eigenvectorDerivative ν n) (data.eigenvectorDerivative μ n)).im =
        (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenvectorDerivative ν n)).im := by
    have h := congrArg Complex.im
      (inner_conj_symm (𝕜 := ℂ)
        (data.eigenvectorDerivative μ n) (data.eigenvectorDerivative ν n))
    simpa only [Complex.conj_im] using h
  linarith

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

/-- The band-diagonal completeness term has zero imaginary part. It therefore does not contribute
to Berry curvature. -/
theorem diagonal_innerProduct_im_eq_zero (μ ν : κ) (n : ι) :
    (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis n) *
      inner ℂ (data.eigenbasis n) (data.eigenvectorDerivative ν n)).im = 0 := by
  have hμ := congrArg Complex.re (data.differentiatedOrthonormality μ n n)
  have hν := congrArg Complex.re (data.differentiatedOrthonormality ν n n)
  simp only [Complex.add_re, Complex.zero_re] at hμ hν
  have hμsym :
      (inner ℂ (data.eigenbasis n) (data.eigenvectorDerivative μ n)).re =
        (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis n)).re := by
    have h := congrArg Complex.re
      (inner_conj_symm (𝕜 := ℂ) (data.eigenvectorDerivative μ n) (data.eigenbasis n))
    simpa only [Complex.conj_re] using h
  have hνsym :
      (inner ℂ (data.eigenbasis n) (data.eigenvectorDerivative ν n)).re =
        (inner ℂ (data.eigenvectorDerivative ν n) (data.eigenbasis n)).re := by
    have h := congrArg Complex.re
      (inner_conj_symm (𝕜 := ℂ) (data.eigenvectorDerivative ν n) (data.eigenbasis n))
    simpa only [Complex.conj_re] using h
  have hμre : (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis n)).re = 0 := by
    linarith
  have hνre : (inner ℂ (data.eigenbasis n) (data.eigenvectorDerivative ν n)).re = 0 := by
    linarith
  simp [Complex.mul_im, hμre, hνre]

/-- The left derivative-state matrix element is the Hermitian-conjugate Born--Fock term. -/
theorem innerDerivative_basis_eq_hamiltonianDerivativeMatrixElement_div
    (μ : κ) (hself : IsSelfAdjoint (data.hamiltonianDerivative μ))
    {m n : ι} (hmn : m ≠ n) (henergy : data.energy m ≠ data.energy n) :
    inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) =
      data.hamiltonianDerivativeMatrixElement μ n m /
        (((data.energy n - data.energy m : ℝ) : ℂ)) := by
  have hbf := data.bornFock_inner μ hmn henergy
  calc
    inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) =
        (starRingEnd ℂ)
          (inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative μ n)) := by
      simp [inner_conj_symm]
    _ = (starRingEnd ℂ)
          (data.hamiltonianDerivativeMatrixElement μ m n /
            (((data.energy n - data.energy m : ℝ) : ℂ))) := by
      rw [hbf]
    _ = data.hamiltonianDerivativeMatrixElement μ n m /
        (((data.energy n - data.energy m : ℝ) : ℂ)) := by
      simp [data.star_hamiltonianDerivativeMatrixElement μ hself]

/-- An off-diagonal completeness term equals the conventional force-matrix Berry-curvature term.
The two real level-spacing factors are intentionally kept separate here; a downstream consumer may
normalize them to a squared denominator if desired. -/
theorem curvatureInnerTerm_eq_hamiltonianDerivativeMatrixElements
    (μ ν : κ)
    (hselfμ : IsSelfAdjoint (data.hamiltonianDerivative μ))
    (hselfν : IsSelfAdjoint (data.hamiltonianDerivative ν))
    {m n : ι} (hmn : m ≠ n) (henergy : data.energy m ≠ data.energy n) :
    -2 * (inner ℂ (data.eigenvectorDerivative μ n) (data.eigenbasis m) *
      inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative ν n)).im =
      2 * ((data.hamiltonianDerivativeMatrixElement μ m n /
        (((data.energy n - data.energy m : ℝ) : ℂ))) *
        (data.hamiltonianDerivativeMatrixElement ν n m /
          (((data.energy n - data.energy m : ℝ) : ℂ)))).im := by
  have hbfν := data.bornFock_inner ν hmn henergy
  rw [data.innerDerivative_basis_eq_hamiltonianDerivativeMatrixElement_div μ hselfμ hmn henergy]
  rw [hbfν]
  let z : ℂ :=
    (data.hamiltonianDerivativeMatrixElement μ n m /
      (((data.energy n - data.energy m : ℝ) : ℂ))) *
    (data.hamiltonianDerivativeMatrixElement ν m n /
      (((data.energy n - data.energy m : ℝ) : ℂ)))
  have hstar :
      (starRingEnd ℂ) z =
        (data.hamiltonianDerivativeMatrixElement μ m n /
          (((data.energy n - data.energy m : ℝ) : ℂ))) *
        (data.hamiltonianDerivativeMatrixElement ν n m /
          (((data.energy n - data.energy m : ℝ) : ℂ))) := by
    dsimp [z]
    simp [data.star_hamiltonianDerivativeMatrixElement μ hselfμ,
      data.star_hamiltonianDerivativeMatrixElement ν hselfν]
  have him :
      -z.im =
        ((data.hamiltonianDerivativeMatrixElement μ m n /
          (((data.energy n - data.energy m : ℝ) : ℂ))) *
        (data.hamiltonianDerivativeMatrixElement ν n m /
          (((data.energy n - data.energy m : ℝ) : ℂ)))).im := by
    have h := congrArg Complex.im hstar
    simpa only [Complex.conj_im] using h
  change -2 * z.im =
    2 * ((data.hamiltonianDerivativeMatrixElement μ m n /
      (((data.energy n - data.energy m : ℝ) : ℂ))) *
      (data.hamiltonianDerivativeMatrixElement ν n m /
        (((data.energy n - data.energy m : ℝ) : ℂ)))).im
  calc
    -2 * z.im = 2 * (-z.im) := by ring
    _ = 2 * ((data.hamiltonianDerivativeMatrixElement μ m n /
      (((data.energy n - data.energy m : ℝ) : ℂ))) *
      (data.hamiltonianDerivativeMatrixElement ν n m /
        (((data.energy n - data.energy m : ℝ) : ℂ)))).im := by rw [him]

/-- Force/Hamiltonian-derivative matrix-element representation of Berry curvature for a
nondegenerate band.

This is the finite-dimensional pointwise formula needed by the clean anomalous-Hall consumer.
Self-adjointness of all directional Hamiltonian derivatives is an explicit hypothesis. -/
theorem berryCurvature_eq_sum_hamiltonianDerivativeMatrixElements [DecidableEq ι]
    (μ ν : κ) (n : ι)
    (hself : ∀ ρ, IsSelfAdjoint (data.hamiltonianDerivative ρ))
    (hnondegenerate : ∀ m, m ≠ n → data.energy m ≠ data.energy n) :
    data.berryCurvature μ ν n =
      ∑ m : ι, if m = n then 0 else
        2 * ((data.hamiltonianDerivativeMatrixElement μ m n /
          (((data.energy n - data.energy m : ℝ) : ℂ))) *
          (data.hamiltonianDerivativeMatrixElement ν n m /
            (((data.energy n - data.energy m : ℝ) : ℂ)))).im := by
  rw [data.berryCurvature_eq_sum_innerProducts]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hmn : m = n
  · subst m
    rw [if_pos rfl]
    rw [data.diagonal_innerProduct_im_eq_zero]
    ring
  · rw [if_neg hmn]
    exact data.curvatureInnerTerm_eq_hamiltonianDerivativeMatrixElements
      μ ν (hself μ) (hself ν) hmn (hnondegenerate m hmn)

end PointwiseEigenbasisData

end
end BerryGeometry
