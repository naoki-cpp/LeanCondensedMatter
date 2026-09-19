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

/-- Parallel-transport-gauge eigenvector derivative determined by a simple spectrum and a
Hamiltonian derivative. The diagonal basis component is fixed to zero; every off-diagonal
component is the Born--Fock quotient. -/
private noncomputable def simpleSpectrumEigenvectorDerivative [DecidableEq ι]
    (eigenbasis : OrthonormalBasis ι ℂ H) (energy : ι → ℝ)
    (hamiltonianDerivative : κ → H →L[ℂ] H) (μ : κ) (n : ι) : H :=
  ∑ m : ι, if m = n then 0 else
    (inner ℂ (eigenbasis m) (hamiltonianDerivative μ (eigenbasis n)) /
      (((energy n - energy m : ℝ) : ℂ))) • eigenbasis m

private theorem inner_simpleSpectrumEigenvectorDerivative [DecidableEq ι]
    (eigenbasis : OrthonormalBasis ι ℂ H) (energy : ι → ℝ)
    (hamiltonianDerivative : κ → H →L[ℂ] H) (μ : κ) (n k : ι) :
    inner ℂ (eigenbasis k)
        (simpleSpectrumEigenvectorDerivative eigenbasis energy hamiltonianDerivative μ n) =
      if k = n then 0 else
        inner ℂ (eigenbasis k) (hamiltonianDerivative μ (eigenbasis n)) /
          (((energy n - energy k : ℝ) : ℂ)) := by
  rw [simpleSpectrumEigenvectorDerivative, inner_sum]
  by_cases hkn : k = n
  · subst k
    simp
  · rw [if_neg hkn]
    apply Finset.sum_eq_single k
    · simp [hkn]
    · intro x _ hxk
      by_cases hxn : x = n
      · simp [hxn]
      · simp [hxn, hxk]
    · intro hnot
      exact (hnot (Finset.mem_univ k)).elim

private theorem inner_hamiltonian_right_of_eigenbasis
    (hamiltonian : H →L[ℂ] H) (hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian)
    (eigenbasis : OrthonormalBasis ι ℂ H) (energy : ι → ℝ)
    (hamiltonian_eigenvector :
      ∀ n, hamiltonian (eigenbasis n) = ((energy n : ℝ) : ℂ) • eigenbasis n)
    (n : ι) (x : H) :
    inner ℂ (eigenbasis n) (hamiltonian x) =
      ((energy n : ℝ) : ℂ) * inner ℂ (eigenbasis n) x := by
  calc
    inner ℂ (eigenbasis n) (hamiltonian x) =
        inner ℂ (hamiltonian (eigenbasis n)) x := by
      symm
      exact hamiltonian_selfAdjoint.isSymmetric.apply_clm _ _
    _ = inner ℂ (((energy n : ℝ) : ℂ) • eigenbasis n) x := by
      rw [hamiltonian_eigenvector]
    _ = ((energy n : ℝ) : ℂ) * inner ℂ (eigenbasis n) x := by
      rw [inner_smul_left]
      simp

/-- Construct pointwise differentiated eigenbasis data from a simple finite spectrum.

The supplied energy derivative is required only through its diagonal Hellmann--Feynman identity.
Eigenvector derivatives are constructed algebraically in the parallel-transport gauge
`⟪φ_n, ∂_μ φ_n⟫ = 0`, so a concrete model need not differentiate an explicit eigenvector gauge. -/
noncomputable def ofSimpleSpectrum [DecidableEq ι]
    (hamiltonian : H →L[ℂ] H)
    (hamiltonian_selfAdjoint : IsSelfAdjoint hamiltonian)
    (eigenbasis : OrthonormalBasis ι ℂ H)
    (energy : ι → ℝ)
    (hamiltonian_eigenvector :
      ∀ n, hamiltonian (eigenbasis n) = ((energy n : ℝ) : ℂ) • eigenbasis n)
    (hamiltonianDerivative : κ → H →L[ℂ] H)
    (hamiltonianDerivative_selfAdjoint :
      ∀ μ, IsSelfAdjoint (hamiltonianDerivative μ))
    (energyDerivative : κ → ι → ℝ)
    (energyDerivative_eq :
      ∀ μ n, ((energyDerivative μ n : ℝ) : ℂ) =
        inner ℂ (eigenbasis n) (hamiltonianDerivative μ (eigenbasis n)))
    (energy_injective : Function.Injective energy) :
    PointwiseEigenbasisData κ ι H := by
  classical
  let eigenvectorDerivative : κ → ι → H :=
    simpleSpectrumEigenvectorDerivative eigenbasis energy hamiltonianDerivative
  refine
    { hamiltonian := hamiltonian
      hamiltonian_selfAdjoint := hamiltonian_selfAdjoint
      eigenbasis := eigenbasis
      energy := energy
      hamiltonian_eigenvector := hamiltonian_eigenvector
      hamiltonianDerivative := hamiltonianDerivative
      eigenvectorDerivative := eigenvectorDerivative
      energyDerivative := energyDerivative
      differentiatedEigenpair := ?_
      differentiatedOrthonormality := ?_ }
  · intro μ n
    apply eigenbasis.repr.injective
    ext k
    rw [eigenbasis.repr_apply_apply, eigenbasis.repr_apply_apply]
    simp only [inner_add_right, inner_smul_right]
    rw [inner_hamiltonian_right_of_eigenbasis hamiltonian hamiltonian_selfAdjoint
      eigenbasis energy hamiltonian_eigenvector]
    change
      inner ℂ (eigenbasis k) (hamiltonianDerivative μ (eigenbasis n)) +
          ((energy k : ℝ) : ℂ) *
            inner ℂ (eigenbasis k) (eigenvectorDerivative μ n) =
        ((energyDerivative μ n : ℝ) : ℂ) *
            inner ℂ (eigenbasis k) (eigenbasis n) +
          ((energy n : ℝ) : ℂ) *
            inner ℂ (eigenbasis k) (eigenvectorDerivative μ n)
    simp only [eigenvectorDerivative, inner_simpleSpectrumEigenvectorDerivative]
    by_cases hkn : k = n
    · subst k
      simp [energyDerivative_eq]
    · have henergy : energy k ≠ energy n := fun h => hkn (energy_injective h)
      have hgap : (((energy n - energy k : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr henergy.symm
      simp only [if_neg hkn, eigenbasis.inner_eq_zero hkn]
      field_simp [hgap]
      push_cast
      ring
  · intro μ m n
    change
      inner ℂ (eigenvectorDerivative μ m) (eigenbasis n) +
        inner ℂ (eigenbasis m) (eigenvectorDerivative μ n) = 0
    rw [show inner ℂ (eigenvectorDerivative μ m) (eigenbasis n) =
      (starRingEnd ℂ) (inner ℂ (eigenbasis n) (eigenvectorDerivative μ m)) by
        simp [inner_conj_symm]]
    simp only [eigenvectorDerivative, inner_simpleSpectrumEigenvectorDerivative]
    by_cases hmn : m = n
    · subst m
      simp
    · have henergy : energy m ≠ energy n := fun h => hmn (energy_injective h)
      have hgapMN : (((energy n - energy m : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr henergy.symm
      have hgapNM : (((energy m - energy n : ℝ) : ℂ)) ≠ 0 := by
        exact_mod_cast sub_ne_zero.mpr henergy
      have hstar :
          (starRingEnd ℂ)
              (inner ℂ (eigenbasis n) (hamiltonianDerivative μ (eigenbasis m))) =
            inner ℂ (eigenbasis m) (hamiltonianDerivative μ (eigenbasis n)) := by
        calc
          (starRingEnd ℂ)
              (inner ℂ (eigenbasis n) (hamiltonianDerivative μ (eigenbasis m))) =
              inner ℂ (hamiltonianDerivative μ (eigenbasis m)) (eigenbasis n) := by
                simp [inner_conj_symm]
          _ = inner ℂ (eigenbasis m) (hamiltonianDerivative μ (eigenbasis n)) := by
            exact (hamiltonianDerivative_selfAdjoint μ).isSymmetric.apply_clm _ _
      simp only [if_neg (Ne.symm hmn), if_neg hmn]
      rw [map_div, hstar]
      simp only [starRingEnd_apply, Complex.conj_ofReal]
      field_simp [hgapMN, hgapNM]
      push_cast
      ring

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
