import LeanCondensedMatter.Transport.Streda.Integration

set_option linter.style.header false

/-!
# Static Středa conductivity matrices

A static conductivity tensor should be represented before selecting a longitudinal or Hall channel.
This file packages a coordinate-indexed regularized Středa conductivity into three contributions:

```text
Fermi-surface + Fermi-sea + explicit contact.
```

The surface/sea split is the analytic Středa split. It is deliberately not identified here with an
intrinsic/extrinsic mechanism split. The contact term remains separate because the generic static
Kubo–Bastin/Středa boundary keeps observable variation outside the surface/sea integration by parts.

Longitudinal response is obtained from a diagonal matrix entry. Hall response is the antisymmetric
part of the complete conductivity matrix, not merely an arbitrary off-diagonal entry.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Coordinate-indexed static conductivity data after a regularized Středa decomposition.

Each field already carries the same physical conductivity normalization. No claim is made that the
Fermi-surface part is purely extrinsic or that the Fermi-sea part is purely intrinsic. -/
structure StaticStredaConductivityMatrix (ι : Type*) where
  /-- Regularized Fermi-surface conductivity contribution. -/
  fermiSurface : ι → ι → ℂ
  /-- Regularized Fermi-sea conductivity contribution. -/
  fermiSea : ι → ι → ℂ
  /-- Explicit observable-variation/contact conductivity contribution. -/
  contact : ι → ι → ℂ

namespace StaticStredaConductivityMatrix

variable {ι : Type*}

/-- Complete static conductivity matrix. -/
noncomputable def total (conductivity : StaticStredaConductivityMatrix ι) : ι → ι → ℂ :=
  fun i j =>
    conductivity.fermiSurface i j + conductivity.fermiSea i j + conductivity.contact i j

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

/-- A symmetric contact contribution drops out of the Hall projection. -/
theorem hallComponent_eq_surface_sea_of_contact_symmetric
    (conductivity : StaticStredaConductivityMatrix ι) (i j : ι)
    (hcontact : conductivity.contact i j = conductivity.contact j i) :
    conductivity.hallComponent i j =
      ((conductivity.fermiSurface i j + conductivity.fermiSea i j) -
        (conductivity.fermiSurface j i + conductivity.fermiSea j i)) / 2 := by
  unfold hallComponent antisymmetricComponent total
  rw [hcontact]
  ring

/-- Build normalized Středa conductivity data from a family of regularized vertex-response
representations plus the explicit contact response. -/
noncomputable def ofRepresentations
    (response contactResponse : ι → ι → ℂ)
    (representation : ∀ i j, RegularizedStredaRepresentation (response i j))
    (normalization : ℂ) : StaticStredaConductivityMatrix ι where
  fermiSurface := fun i j =>
    regularizedStredaFermiSurface
        (representation i j).toRegularizedStredaIntegralData * normalization
  fermiSea := fun i j =>
    regularizedStredaFermiSea
        (representation i j).toRegularizedStredaIntegralData * normalization
  contact := fun i j => contactResponse i j * normalization

/-- The complete matrix constructed from Středa representations reproduces the normalized full
response, including the explicit contact contribution. -/
theorem ofRepresentations_total
    (response contactResponse : ι → ι → ℂ)
    (representation : ∀ i j, RegularizedStredaRepresentation (response i j))
    (normalization : ℂ) (i j : ι) :
    (ofRepresentations response contactResponse representation normalization).total i j =
      (response i j + contactResponse i j) * normalization := by
  unfold total ofRepresentations
  rw [(representation i j).response_eq_surface_add_sea]
  ring

end StaticStredaConductivityMatrix

end
end Transport
end QuantumTheory
