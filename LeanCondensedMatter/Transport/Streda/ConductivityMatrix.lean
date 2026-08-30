import LeanCondensedMatter.Transport.Streda.Integration

set_option linter.style.header false

/-!
# Static Středa conductivity matrices

A static conductivity tensor should be represented before selecting a longitudinal or Hall channel.
This file packages a coordinate-indexed regularized Středa conductivity into the two contributions
of the Středa decomposition:

```text
Fermi-surface + Fermi-sea.
```

Peierls observable-variation/contact terms belong to the upstream Kubo response and to the explicit
Ward/f-sum bridge that identifies that response with a Středa representation. They are not stored as
a third contribution in the final Středa conductivity matrix.

The surface/sea split is an analytic Středa split. It is deliberately not identified here with an
intrinsic/extrinsic mechanism split. Longitudinal response is obtained from a diagonal matrix entry;
Hall response is the antisymmetric part of the complete conductivity matrix, not merely an arbitrary
off-diagonal entry.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Coordinate-indexed static conductivity data after a regularized Středa decomposition.

No claim is made that the Fermi-surface part is purely extrinsic or that the Fermi-sea part is purely
intrinsic. Any contact-term cancellation or absorption required to reach this final conductivity is
proved upstream when constructing the componentwise `RegularizedStredaRepresentation`. -/
structure StaticStredaConductivityMatrix (ι : Type*) where
  /-- Regularized Fermi-surface conductivity contribution. -/
  fermiSurface : ι → ι → ℂ
  /-- Regularized Fermi-sea conductivity contribution. -/
  fermiSea : ι → ι → ℂ

namespace StaticStredaConductivityMatrix

variable {ι : Type*}

/-- Complete static conductivity matrix. -/
noncomputable def total (conductivity : StaticStredaConductivityMatrix ι) : ι → ι → ℂ :=
  fun i j => conductivity.fermiSurface i j + conductivity.fermiSea i j

/-- Longitudinal conductivity along one selected coordinate. -/
noncomputable def longitudinal
    (conductivity : StaticStredaConductivityMatrix ι) (i : ι) : ℂ :=
  conductivity.total i i

/-- Symmetric part of one conductivity-matrix component. -/
noncomputable def symmetricComponent
    (conductivity : StaticStredaConductivityMatrix ι) (i j : ι) : ℂ :=
  (conductivity.total i j + conductivity.total j i) / 2

/-- Antisymmetric part of one conductivity-matrix component. -/
noncomputable def antisymmetricComponent
    (conductivity : StaticStredaConductivityMatrix ι) (i j : ι) : ℂ :=
  (conductivity.total i j - conductivity.total j i) / 2

/-- Hall conductivity component, defined as the antisymmetric part of the complete conductivity
matrix. An off-diagonal component equals this Hall component only under the corresponding
antisymmetry hypothesis. -/
noncomputable def hallComponent
    (conductivity : StaticStredaConductivityMatrix ι) (i j : ι) : ℂ :=
  conductivity.antisymmetricComponent i j

/-- Every conductivity component is the sum of its symmetric and antisymmetric parts. -/
theorem symmetricComponent_add_antisymmetricComponent
    (conductivity : StaticStredaConductivityMatrix ι) (i j : ι) :
    conductivity.symmetricComponent i j + conductivity.antisymmetricComponent i j =
      conductivity.total i j := by
  unfold symmetricComponent antisymmetricComponent
  ring

/-- The Hall component vanishes on the diagonal. -/
@[simp]
theorem hallComponent_self
    (conductivity : StaticStredaConductivityMatrix ι) (i : ι) :
    conductivity.hallComponent i i = 0 := by
  simp [hallComponent, antisymmetricComponent]

/-- If the total conductivity is antisymmetric in a coordinate pair, its off-diagonal entry is
already the Hall component for that pair. -/
theorem hallComponent_eq_total_of_antisymmetric
    (conductivity : StaticStredaConductivityMatrix ι) (i j : ι)
    (hantisym : conductivity.total j i = -conductivity.total i j) :
    conductivity.hallComponent i j = conductivity.total i j := by
  simp [hallComponent, antisymmetricComponent, hantisym]

/-- Build a Středa conductivity matrix from a componentwise family of proved Středa
representations of the already-normalized physical conductivity. -/
noncomputable def ofRepresentations
    (conductivity : ι → ι → ℂ)
    (representation : ∀ i j, RegularizedStredaRepresentation (conductivity i j)) :
    StaticStredaConductivityMatrix ι where
  fermiSurface := fun i j =>
    regularizedStredaFermiSurface
      (representation i j).toRegularizedStredaIntegralData
  fermiSea := fun i j =>
    regularizedStredaFermiSea
      (representation i j).toRegularizedStredaIntegralData

/-- The complete matrix constructed from Středa representations reproduces the represented
conductivity component by component. -/
theorem ofRepresentations_total
    (conductivity : ι → ι → ℂ)
    (representation : ∀ i j, RegularizedStredaRepresentation (conductivity i j))
    (i j : ι) :
    (ofRepresentations conductivity representation).total i j = conductivity i j := by
  unfold total ofRepresentations
  exact (representation i j).response_eq_surface_add_sea.symm

end StaticStredaConductivityMatrix

end
end Transport
end QuantumTheory
