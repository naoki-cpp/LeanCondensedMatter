import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Pointwise Berry connection and differentiated eigenpair identities

This module provides the finite-dimensional, pointwise spectral data needed by Berry-geometry
consumers without choosing a global gauge of eigenvectors over parameter space.

At one parameter point and in one parameter direction we store an orthonormal eigenbasis of a
self-adjoint Hamiltonian together with the directional derivatives of the Hamiltonian, eigenvectors,
and eigenvalues.  The differentiated eigenpair and orthonormality identities are explicit fields.
They can later be supplied by a `HasFDerivAt`-based family, but that global analytic layer is not
required for the algebraic identities proved here.

The convention is

```text
A_mn = i ⟪φ_m, ∂φ_n⟫,
F_mn = ⟪φ_m, (∂H) φ_n⟫.
```

The full band-index Berry-connection matrix is Hermitian; only its diagonal entries are asserted
to be real.  This module deliberately does not define Berry phase along paths, Berry curvature,
transport response, or disorder.
-/

namespace BerryGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pointwise data for differentiating a finite orthonormal eigenbasis in one parameter direction.

`differentiatedEigenpair` is the derivative of `H φ_n = E_n φ_n`, while
`differentiatedOrthonormality` is the derivative of `⟪φ_m, φ_n⟫ = δ_mn`.
The Hamiltonian derivative need not itself be self-adjoint for the algebra below. -/
structure DirectionalEigenbasisData (ι H : Type*) [Fintype ι]
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
  /-- Directional derivative of the Hamiltonian. -/
  hamiltonianDerivative : H →L[ℂ] H
  /-- Directional derivative of each eigenvector in the chosen local gauge. -/
  eigenvectorDerivative : ι → H
  /-- Directional derivative of each real eigenenergy. -/
  energyDerivative : ι → ℝ
  /-- Differentiated eigenpair equation
  `(∂H) φ_n + H (∂φ_n) = (∂E_n) φ_n + E_n (∂φ_n)`. -/
  differentiatedEigenpair :
    ∀ n,
      hamiltonianDerivative (eigenbasis n) + hamiltonian (eigenvectorDerivative n) =
        ((energyDerivative n : ℝ) : ℂ) • eigenbasis n +
          ((energy n : ℝ) : ℂ) • eigenvectorDerivative n
  /-- Differentiated orthonormality relation
  `⟪∂φ_m, φ_n⟫ + ⟪φ_m, ∂φ_n⟫ = 0`. -/
  differentiatedOrthonormality :
    ∀ m n,
      inner ℂ (eigenvectorDerivative m) (eigenbasis n) +
        inner ℂ (eigenbasis m) (eigenvectorDerivative n) = 0

namespace DirectionalEigenbasisData

variable (data : DirectionalEigenbasisData ι H)

/-- Berry-connection matrix element in the chosen parameter direction,
`A_mn = i ⟪φ_m, ∂φ_n⟫`. -/
noncomputable def berryConnection (m n : ι) : ℂ :=
  Complex.I * inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative n)

/-- Matrix element of the Hamiltonian derivative,
`F_mn = ⟪φ_m, (∂H) φ_n⟫`. -/
noncomputable def hamiltonianDerivativeMatrixElement (m n : ι) : ℂ :=
  inner ℂ (data.eigenbasis m) (data.hamiltonianDerivative (data.eigenbasis n))

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
      simp

/-- The Berry-connection matrix is Hermitian in band indices:
`(A_mn)⁎ = A_nm`.  In particular, off-diagonal entries are not asserted to be real. -/
theorem star_berryConnection (m n : ι) :
    (starRingEnd ℂ) (data.berryConnection m n) = data.berryConnection n m := by
  calc
    (starRingEnd ℂ) (data.berryConnection m n) =
        -Complex.I * inner ℂ (data.eigenvectorDerivative n) (data.eigenbasis m) := by
      simp [berryConnection, inner_conj_symm]
    _ = Complex.I * inner ℂ (data.eigenbasis n) (data.eigenvectorDerivative m) := by
      have horth := data.differentiatedOrthonormality n m
      linear_combination (-Complex.I) * horth
    _ = data.berryConnection n m := rfl

/-- A diagonal Berry connection is real, expressed as vanishing imaginary part. -/
theorem berryConnection_diagonal_im_eq_zero (n : ι) :
    (data.berryConnection n n).im = 0 := by
  have h := congrArg Complex.im (data.star_berryConnection n n)
  simp at h
  linarith

/-- Hellmann--Feynman theorem in the chosen parameter direction:
`∂E_n = ⟪φ_n, (∂H) φ_n⟫`. -/
theorem hellmannFeynman (n : ι) :
    ((data.energyDerivative n : ℝ) : ℂ) =
      data.hamiltonianDerivativeMatrixElement n n := by
  have h := congrArg (fun x : H => inner ℂ (data.eigenbasis n) x)
    (data.differentiatedEigenpair n)
  simp only [inner_add_right, inner_smul_right] at h
  rw [data.inner_hamiltonian_right n, data.eigenbasis.inner_eq_one] at h
  simp only [mul_one] at h
  unfold hamiltonianDerivativeMatrixElement
  linear_combination -h

/-- Born--Fock off-diagonal eigenvector-derivative formula.

The nondegeneracy needed for division by the level spacing is an explicit theorem hypothesis rather
than a global restriction on `DirectionalEigenbasisData`. -/
theorem bornFock_inner {m n : ι} (hmn : m ≠ n)
    (henergy : data.energy m ≠ data.energy n) :
    inner ℂ (data.eigenbasis m) (data.eigenvectorDerivative n) =
      data.hamiltonianDerivativeMatrixElement m n /
        (((data.energy n - data.energy m : ℝ) : ℂ)) := by
  have h := congrArg (fun x : H => inner ℂ (data.eigenbasis m) x)
    (data.differentiatedEigenpair n)
  simp only [inner_add_right, inner_smul_right] at h
  rw [data.inner_hamiltonian_right m, data.eigenbasis.inner_eq_zero hmn] at h
  simp only [mul_zero, zero_add] at h
  have hgap : (((data.energy n - data.energy m : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr henergy.symm
  apply (eq_div_iff hgap).2
  unfold hamiltonianDerivativeMatrixElement at h ⊢
  push_cast at h ⊢
  linear_combination h

/-- Born--Fock formula in Berry-connection form. -/
theorem bornFock_berryConnection {m n : ι} (hmn : m ≠ n)
    (henergy : data.energy m ≠ data.energy n) :
    data.berryConnection m n =
      Complex.I * data.hamiltonianDerivativeMatrixElement m n /
        (((data.energy n - data.energy m : ℝ) : ℂ)) := by
  rw [berryConnection, data.bornFock_inner hmn henergy]
  ring

end DirectionalEigenbasisData

end
end BerryGeometry
