import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Transition

set_option linter.style.header false

/-!
# Finite scalar Lehmann evaluation tables

This module is the calculation boundary between the operator-level Kubo/Lehmann theorems and
small finite benchmark models.  A finite response calculation only needs the scalar spectral data

```text
Eₙ, pₙ, Aₘₙ = ⟨m|A|n⟩, Bₘₙ = ⟨m|B|n⟩.
```

`FiniteLehmannTable` stores exactly these quantities.  `finiteLehmannTableTransitionData` is the
explicit scalar adapter to the canonical `LehmannTransitionData` seam in `Lehmann/Transition.lean`; evaluation
then uses the record's fixed-rate frequency term.

The operator-to-table adapter is owned separately by `Lehmann/PurePointTable.lean`.

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

/-- Adapt one scalar-table ordered pair to the canonical Lehmann transition data. -/
noncomputable def finiteLehmannTableTransitionData
    {ι : Type*} (hbar : ℝ) (table : FiniteLehmannTable ι)
    (mn : ι × ι) : LehmannTransitionData hbar :=
  orderedLehmannTransitionData hbar
    (table.energy mn.1) (table.energy mn.2)
    (table.probability mn.1) (table.probability mn.2)
    (table.matrixA mn.1 mn.2) (table.matrixB mn.2 mn.1)

@[simp]
theorem finiteLehmannTableTransitionData_energyGap
    {ι : Type*} (hbar : ℝ) (table : FiniteLehmannTable ι) (mn : ι × ι) :
    (finiteLehmannTableTransitionData hbar table mn).energyGap =
      orderedLehmannEnergyGap (table.energy mn.1) (table.energy mn.2) := rfl

/-- Diagonal transitions vanish already at the scalar-table level. -/
@[simp]
theorem finiteLehmannTableTransitionData_weight_diag
    {ι : Type*} (hbar : ℝ) (table : FiniteLehmannTable ι) (i : ι) :
    (finiteLehmannTableTransitionData hbar table (i, i)).weight = 0 := by
  simp [finiteLehmannTableTransitionData]

/-- Fixed-rate finite Lehmann response evaluated from scalar spectral data. -/
noncomputable def finiteLehmannTableResponse
    {ι : Type*} [Fintype ι]
    (hbar omega eta : ℝ) (table : FiniteLehmannTable ι) : ℂ :=
  ∑ mn : ι × ι,
    (finiteLehmannTableTransitionData hbar table mn).frequencyTerm omega eta


end
end LinearResponse
end QuantumTheory
