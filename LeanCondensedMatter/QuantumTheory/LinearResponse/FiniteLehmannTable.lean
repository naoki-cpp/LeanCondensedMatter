import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann

set_option linter.style.header false

/-!
# Finite scalar Lehmann evaluation tables

This module is the calculation boundary between the operator-level Kubo/Lehmann theorems and
small finite benchmark models.  A finite response calculation only needs the scalar spectral data

```text
Eₙ, pₙ, Aₘₙ = ⟨m|A|n⟩, Bₘₙ = ⟨m|B|n⟩.
```

`FiniteLehmannTable` stores exactly these quantities.  Its evaluator is the ordinary finite double
sum built from the repository's existing `lehmannTerm`, so Fourier/sign/broadening conventions are
not duplicated here.

The bridge `finiteLehmannTableOfPurePoint` constructs a table from the theorem-level
`PurePointLehmannData` API and bounded observables.  The main equality proves that evaluating the
scalar table is exactly the existing finite pure-point Lehmann series.

This layer intentionally carries no SecondQuantization or conductivity-specific data.  Contact
terms and finite-volume electric-field normalization belong to the downstream transport wrapper.
-/

namespace QuantumTheory
namespace LinearResponse

noncomputable section

/-- Scalar data sufficient to evaluate a finite pure-point Lehmann response.

`matrixA m n` and `matrixB m n` represent `⟨m|A|n⟩` and `⟨m|B|n⟩`, respectively. -/
structure FiniteLehmannTable (ι : Type*) where
  /-- Energy eigenvalue `Eₙ` associated with each finite spectral index. -/
  energy : ι → ℝ
  /-- Diagonal state probability `pₙ` associated with each finite spectral index. -/
  probability : ι → ℝ
  /-- Matrix element table `Aₘₙ = ⟨m|A|n⟩` for the measured observable. -/
  matrixA : ι → ι → ℂ
  /-- Matrix element table `Bₘₙ = ⟨m|B|n⟩` for the source-coupling observable. -/
  matrixB : ι → ι → ℂ

/-- The physical transition weight `(i/ℏ)(pₘ-pₙ)AₘₙBₙₘ` read only from a scalar table. -/
def finiteLehmannTableTransitionWeight
    {ι : Type*} (hbar : ℝ) (table : FiniteLehmannTable ι) (mn : ι × ι) : ℂ :=
  (Complex.I / (hbar : ℂ)) *
    ((table.probability mn.1 - table.probability mn.2 : ℝ) : ℂ) *
    table.matrixA mn.1 mn.2 * table.matrixB mn.2 mn.1

/-- Diagonal transitions vanish already at the scalar-table level. -/
@[simp]
theorem finiteLehmannTableTransitionWeight_diag
    {ι : Type*} (hbar : ℝ) (table : FiniteLehmannTable ι) (i : ι) :
    finiteLehmannTableTransitionWeight hbar table (i, i) = 0 := by
  simp [finiteLehmannTableTransitionWeight]

/-- Fixed-rate finite Lehmann response evaluated from scalar spectral data. -/
noncomputable def finiteLehmannTableResponse
    {ι : Type*} [Fintype ι]
    (hbar omega eta : ℝ) (table : FiniteLehmannTable ι) : ℂ :=
  ∑ mn : ι × ι,
    lehmannTerm hbar omega eta
      (table.energy mn.1 - table.energy mn.2)
      (finiteLehmannTableTransitionWeight hbar table mn)

variable {H ι : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Forget an operator-level pure-point response problem to the scalar data needed for finite
Lehmann evaluation. -/
noncomputable def finiteLehmannTableOfPurePoint
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) : FiniteLehmannTable ι where
  energy := data.energy
  probability := data.probability
  matrixA := fun m n => inner ℂ (data.basis m) (A (data.basis n))
  matrixB := fun m n => inner ℂ (data.basis m) (B (data.basis n))

/-- For a finite spectral index, scalar-table evaluation is exactly the theorem-level pure-point
Lehmann series.  This is the main operator-to-calculation bridge. -/
theorem finiteLehmannTableResponse_ofPurePoint
    [Fintype ι]
    (system : BoundedFreeSystem H)
    (data : PurePointLehmannData system ι)
    (A B : H →L[ℂ] H) (omega eta : ℝ) :
    finiteLehmannTableResponse system.hbar omega eta
        (finiteLehmannTableOfPurePoint system data A B) =
      purePointLehmannSeries system data A B omega eta := by
  rw [purePointLehmannSeries_eq_finite_sum]
  rfl

end
end LinearResponse
end QuantumTheory
