import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Tactic.Ring

set_option linter.style.header false

open scoped Matrix

/-!
# Conductivity tensors

This module owns the representation-independent tensor structure of electrical conductivity. It does
not assume a Kubo, Bastin, Středa, Boltzmann, or other representation. Concrete transport formalisms
must supply the physical normalization needed to construct this tensor from their response data.

Longitudinal and Hall components are projections of the completed conductivity tensor rather than
properties of any one representation.
-/

namespace QuantumTheory
namespace Transport

noncomputable section

/-- Coordinate-indexed physical conductivity tensor, independent of how its components were
derived. -/
structure ConductivityTensor (ι : Type*) where
  /-- Conductivity component for one ordered measured/source coordinate pair. -/
  component : ι → ι → ℂ

namespace ConductivityTensor

variable {ι : Type*}

/-- Longitudinal conductivity along one selected coordinate. -/
noncomputable def longitudinal
    (conductivity : ConductivityTensor ι) (i : ι) : ℂ :=
  conductivity.component i i

/-- Hall conductivity component, defined as the antisymmetric part of the full conductivity tensor. -/
noncomputable def hallComponent
    (conductivity : ConductivityTensor ι) (i j : ι) : ℂ :=
  (conductivity.component i j - conductivity.component j i) / 2

/-- The Hall projection vanishes on the diagonal. -/
@[simp]
theorem hallComponent_self
    (conductivity : ConductivityTensor ι) (i : ι) :
    conductivity.hallComponent i i = 0 := by
  simp [hallComponent]


/-- Symmetric component of the completed physical conductivity tensor. This is distinct from
the symmetric part of a resistivity tensor, which is obtained only after tensor inversion. -/
noncomputable def symmetricComponent
    (conductivity : ConductivityTensor ι) (i j : ι) : ℂ :=
  (conductivity.component i j + conductivity.component j i) / 2

/-- Exchanging the measured and source indices leaves the symmetric projection unchanged. -/
theorem symmetricComponent_swap
    (conductivity : ConductivityTensor ι) (i j : ι) :
    conductivity.symmetricComponent j i =
      conductivity.symmetricComponent i j := by
  simp only [symmetricComponent, add_comm]

/-- Exchanging the measured and source indices reverses the Hall projection. -/
theorem hallComponent_swap
    (conductivity : ConductivityTensor ι) (i j : ι) :
    conductivity.hallComponent j i =
      -conductivity.hallComponent i j := by
  unfold hallComponent
  ring

/-- Longitudinal conductivity lies entirely in the symmetric projection. -/
@[simp]
theorem symmetricComponent_self
    (conductivity : ConductivityTensor ι) (i : ι) :
    conductivity.symmetricComponent i i = conductivity.longitudinal i := by
  unfold symmetricComponent longitudinal
  ring

/-- Every ordered conductivity component is its symmetric part plus its Hall part. -/
theorem component_eq_symmetricComponent_add_hallComponent
    (conductivity : ConductivityTensor ι) (i j : ι) :
    conductivity.component i j =
      conductivity.symmetricComponent i j + conductivity.hallComponent i j := by
  unfold symmetricComponent hallComponent
  ring

/-- A two-dimensional conductivity tensor invariant under planar rotations: its diagonal
entries agree and its off-diagonal entries are opposite. This is a property of the
completed conductivity, not an assumption about its microscopic response representation. -/
def IsPlanarIsotropic (conductivity : ConductivityTensor (Fin 2)) : Prop :=
  conductivity.component 1 1 = conductivity.component 0 0 ∧
    conductivity.component 1 0 = -conductivity.component 0 1

/-- The completed planar conductivity is invariant under the quarter-turn
`R = [[0,-1],[1,0]]` acting on both its measured and source directions.
The finite component sum is the `(R σ Rᵀ)ᵢⱼ = σᵢⱼ` condition, spelled out
without converting the existing function-valued tensor to a new matrix type.
This is a spatial-symmetry constraint, not a microscopic Kubo hypothesis or
an assertion that the Hall component vanishes. -/
def IsQuarterTurnInvariant (conductivity : ConductivityTensor (Fin 2)) : Prop :=
  let R : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]
  ∀ i j : Fin 2,
    (∑ k : Fin 2, ∑ l : Fin 2,
      R i k * conductivity.component k l * R j l) = conductivity.component i j

/-- Quarter-turn invariance is exactly the existing planar isotropy condition:
equal longitudinal components and antisymmetric off-diagonal components.
The antisymmetric Hall response is permitted by this proper rotation. -/
theorem isQuarterTurnInvariant_iff_isPlanarIsotropic
    (conductivity : ConductivityTensor (Fin 2)) :
    conductivity.IsQuarterTurnInvariant ↔ conductivity.IsPlanarIsotropic := by
  constructor
  · intro h
    dsimp [IsQuarterTurnInvariant] at h
    have h00 := h 0 0
    have h01 := h 0 1
    simp [Fin.sum_univ_two] at h00 h01
    constructor
    · exact h00
    · calc
        conductivity.component 1 0 =
            -(-conductivity.component 1 0) := by ring
        _ = -conductivity.component 0 1 := by rw [h01]
  · rintro ⟨hdiag, hoffdiag⟩
    dsimp [IsQuarterTurnInvariant]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Fin.sum_univ_two, hdiag, hoffdiag]

/-- Quarter-turn symmetry forces the symmetric xy conductivity to vanish,
even though it does not force the full xy (Hall) component to vanish. -/
theorem symmetricComponent_zero_one_eq_zero_of_isQuarterTurnInvariant
    (conductivity : ConductivityTensor (Fin 2))
    (h : conductivity.IsQuarterTurnInvariant) :
    conductivity.symmetricComponent 0 1 = 0 := by
  have hiso := (isQuarterTurnInvariant_iff_isPlanarIsotropic conductivity).mp h
  change (conductivity.component 0 1 + conductivity.component 1 0) / 2 = 0
  rw [hiso.2]
  ring

/-- Quarter-turn symmetry makes the two in-plane longitudinal
conductivities equal, independently of the Hall part. -/
theorem longitudinal_zero_eq_one_of_isQuarterTurnInvariant
    (conductivity : ConductivityTensor (Fin 2))
    (h : conductivity.IsQuarterTurnInvariant) :
    conductivity.longitudinal 0 = conductivity.longitudinal 1 := by
  change conductivity.component 0 0 = conductivity.component 1 1
  exact ((isQuarterTurnInvariant_iff_isPlanarIsotropic conductivity).mp h).1.symm

/-- For a planar-isotropic tensor, the Hall projection equals the ordered xy component. -/
theorem hallComponent_zero_one_eq_of_isPlanarIsotropic
    (conductivity : ConductivityTensor (Fin 2))
    (hiso : conductivity.IsPlanarIsotropic) :
    conductivity.hallComponent 0 1 = conductivity.component 0 1 := by
  rw [hallComponent, hiso.2]
  ring

/-- Onsager–Casimir reciprocity as a *property* of a magnetization-indexed physical
conductivity family. A concrete Kubo model must establish this hypothesis using its
time-reversal and current/source transformation laws; it is not automatic for a tensor. -/
def IsOnsagerReciprocal {M : Type*}
    (conductivity : M → ConductivityTensor ι) (reverse : M → M) : Prop :=
  ∀ m i j,
    (conductivity m).component i j =
      (conductivity (reverse m)).component j i

/-- Conditional Onsager reciprocity makes the symmetric conductivity even under reversal. -/
theorem symmetricComponent_reverse {M : Type*}
    (conductivity : M → ConductivityTensor ι) (reverse : M → M)
    (hreciprocal : IsOnsagerReciprocal conductivity reverse)
    (m : M) (i j : ι) :
    (conductivity m).symmetricComponent i j =
      (conductivity (reverse m)).symmetricComponent i j := by
  unfold symmetricComponent
  rw [hreciprocal m i j, hreciprocal m j i]
  ring

/-- Conditional Onsager reciprocity makes Hall conductivity odd under reversal. -/
theorem hallComponent_reverse {M : Type*}
    (conductivity : M → ConductivityTensor ι) (reverse : M → M)
    (hreciprocal : IsOnsagerReciprocal conductivity reverse)
    (m : M) (i j : ι) :
    (conductivity m).hallComponent i j =
      -(conductivity (reverse m)).hallComponent i j := by
  unfold hallComponent
  rw [hreciprocal m i j, hreciprocal m j i]
  ring

/-- A diagonal (longitudinal) conductivity is even under Onsager reversal. -/
theorem longitudinal_reverse {M : Type*}
    (conductivity : M → ConductivityTensor ι) (reverse : M → M)
    (hreciprocal : IsOnsagerReciprocal conductivity reverse)
    (m : M) (i : ι) :
    (conductivity m).longitudinal i =
      (conductivity (reverse m)).longitudinal i := by
  simpa only [longitudinal] using hreciprocal m i i

end ConductivityTensor

end
end Transport
end QuantumTheory
