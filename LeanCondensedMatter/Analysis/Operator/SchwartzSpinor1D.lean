import LeanCondensedMatter.Analysis.Operator.SchwartzKinetic1D
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

set_option linter.style.header false

/-!
# One-dimensional Schwartz spinor operators

This module adds a minimal spin-1/2 internal degree of freedom to the analysis-only Schwartz
Schrodinger model.  A spinor is represented as two complex Schwartz components,
`Fin 2 → SchwartzMap ℝ ℂ`.  Spatial operators act componentwise, while a `2 × 2` complex matrix
acts only on the internal index.

This separation makes the internal-degree hypothesis structural: every componentwise spatial
operator commutes with every internal matrix operator.  In particular, multiplication localizers
commute with spin, and the velocity operator commutes with spin.  An arbitrary internal Hamiltonian
matrix may nevertheless fail to commute with spin and therefore supplies a spin-torque/source term.

The module is purely analytic/algebraic and does not depend on `QuantumMechanics` or
`SecondQuantization`.
-/

namespace SchwartzSpinor1D

noncomputable section

/-- Scalar complex Schwartz space used for each spin component. -/
abbrev Spatial := SchwartzKinetic1D.Space

/-- Two-component complex Schwartz spinors. -/
abbrev Spinor := Fin 2 → Spatial

/-- Complex `2 × 2` matrices acting on the internal spin index. -/
abbrev SpinMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Lift a scalar Schwartz operator componentwise to a two-component spinor. -/
noncomputable def spatialLift (A : Spatial →ₗ[ℂ] Spatial) : Spinor →ₗ[ℂ] Spinor where
  toFun := fun ψ a => A (ψ a)
  map_add' := by
    intro ψ χ
    funext a
    simp
  map_smul' := by
    intro c ψ
    funext a
    simp

@[simp]
theorem spatialLift_apply (A : Spatial →ₗ[ℂ] Spatial) (ψ : Spinor) (a : Fin 2) :
    spatialLift A ψ a = A (ψ a) :=
  rfl

/-- A finite internal matrix acting on the spin index and leaving the spatial wavefunction intact. -/
noncomputable def internalOperator (S : SpinMatrix) : Spinor →ₗ[ℂ] Spinor where
  toFun := fun ψ a => ∑ b : Fin 2, S a b • ψ b
  map_add' := by
    intro ψ χ
    funext a
    simp [smul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c ψ
    funext a
    simp [smul_smul, mul_comm]

@[simp]
theorem internalOperator_apply (S : SpinMatrix) (ψ : Spinor) (a : Fin 2) :
    internalOperator S ψ a = ∑ b : Fin 2, S a b • ψ b :=
  rfl

/-- Spatial and internal operators commute because they act on independent factors. -/
theorem spatialLift_comp_internalOperator_comm
    (A : Spatial →ₗ[ℂ] Spatial) (S : SpinMatrix) :
    (spatialLift A).comp (internalOperator S) =
      (internalOperator S).comp (spatialLift A) := by
  apply LinearMap.ext
  intro ψ
  funext a
  simp [internalOperator]

/-- Spinor multiplication by a scalar Schwartz localizer. -/
noncomputable def multiplicationOperator (f : Spatial) : Spinor →ₗ[ℂ] Spinor :=
  spatialLift (SchwartzKinetic1D.multiplicationOperator f)

@[simp]
theorem multiplicationOperator_apply
    (f : Spatial) (ψ : Spinor) (a : Fin 2) (x : ℝ) :
    multiplicationOperator f ψ a x = f x * ψ a x :=
  rfl

/-- Multiplication localizers depend complex-linearly on the scalar Schwartz test function. -/
noncomputable def multiplicationLinear : Spatial →ₗ[ℂ] (Spinor →ₗ[ℂ] Spinor) where
  toFun := multiplicationOperator
  map_add' := by
    intro f g
    apply LinearMap.ext
    intro ψ
    funext a
    ext x
    simp [multiplicationOperator]
    ring
  map_smul' := by
    intro c f
    apply LinearMap.ext
    intro ψ
    funext a
    ext x
    simp [multiplicationOperator]
    ring

@[simp]
theorem multiplicationLinear_apply (f : Spatial) :
    multiplicationLinear f = multiplicationOperator f :=
  rfl

/-- The scalar Schwartz derivative used as the localization differential. -/
noncomputable def derivative : Spatial →ₗ[ℂ] Spatial :=
  SchwartzKinetic1D.derivative

/-- Componentwise Schwartz velocity operator. -/
noncomputable def velocityOperator (ℏ κ : ℝ) : Spinor →ₗ[ℂ] Spinor :=
  spatialLift (SchwartzKinetic1D.velocityOperator ℏ κ)

/-- Componentwise scalar Schrodinger Hamiltonian. -/
noncomputable def spatialHamiltonian (κ : ℝ) (potential : Spatial) : Spinor →ₗ[ℂ] Spinor :=
  spatialLift (SchwartzKinetic1D.schrodingerOperator κ potential)

/-- Spinor Hamiltonian consisting of scalar spatial dynamics plus an arbitrary internal matrix.

The internal term may model a Zeeman/exchange/SOC-like on-site spin coupling at this abstract level.
It commutes with spatial localization but need not commute with the selected spin component. -/
noncomputable def hamiltonian
    (κ : ℝ) (potential : Spatial) (internalH : SpinMatrix) : Spinor →ₗ[ℂ] Spinor :=
  spatialHamiltonian κ potential + internalOperator internalH

/-- Cartesian spin axes. -/
inductive SpinAxis
  | x
  | y
  | z
  deriving DecidableEq, Repr

/-- Pauli matrix `σ_x`. -/
noncomputable def pauliX : SpinMatrix :=
  !![0, 1; 1, 0]

/-- Pauli matrix `σ_y`. -/
noncomputable def pauliY : SpinMatrix :=
  !![0, -Complex.I; Complex.I, 0]

/-- Pauli matrix `σ_z`. -/
noncomputable def pauliZ : SpinMatrix :=
  !![1, 0; 0, -1]

/-- Pauli matrix associated with a Cartesian spin axis. -/
noncomputable def pauli : SpinAxis → SpinMatrix
  | .x => pauliX
  | .y => pauliY
  | .z => pauliZ

/-- Spin-1/2 matrix `S_a = ℏ σ_a / 2`. -/
noncomputable def spinMatrix (ℏ : ℝ) (axis : SpinAxis) : SpinMatrix :=
  (((ℏ / 2 : ℝ) : ℂ)) • pauli axis

/-- Spin-1/2 operator acting only on the internal index. -/
noncomputable def spinOperator (ℏ : ℝ) (axis : SpinAxis) : Spinor →ₗ[ℂ] Spinor :=
  internalOperator (spinMatrix ℏ axis)

/-- Scalar multiplication localizers commute with every spin component. -/
theorem multiplicationOperator_comp_spinOperator_comm
    (f : Spatial) (ℏ : ℝ) (axis : SpinAxis) :
    (multiplicationOperator f).comp (spinOperator ℏ axis) =
      (spinOperator ℏ axis).comp (multiplicationOperator f) :=
  spatialLift_comp_internalOperator_comm
    (SchwartzKinetic1D.multiplicationOperator f) (spinMatrix ℏ axis)

/-- The componentwise velocity commutes with every internal spin component. -/
theorem velocityOperator_comp_spinOperator_comm
    (ℏ κ : ℝ) (axis : SpinAxis) :
    (velocityOperator ℏ κ).comp (spinOperator ℏ axis) =
      (spinOperator ℏ axis).comp (velocityOperator ℏ κ) :=
  spatialLift_comp_internalOperator_comm
    (SchwartzKinetic1D.velocityOperator ℏ κ) (spinMatrix ℏ axis)

/-- The scalar spatial Hamiltonian commutes with every internal spin component. -/
theorem spatialHamiltonian_comp_spinOperator_comm
    (κ : ℝ) (potential : Spatial) (ℏ : ℝ) (axis : SpinAxis) :
    (spatialHamiltonian κ potential).comp (spinOperator ℏ axis) =
      (spinOperator ℏ axis).comp (spatialHamiltonian κ potential) :=
  spatialLift_comp_internalOperator_comm
    (SchwartzKinetic1D.schrodingerOperator κ potential) (spinMatrix ℏ axis)

/-- The localization commutator of the spinor Hamiltonian is unaffected by the internal matrix term. -/
theorem hamiltonian_localization_commutator_eq_spatial
    (κ : ℝ) (potential : Spatial) (internalH : SpinMatrix) (f : Spatial) :
    (hamiltonian κ potential internalH).comp (multiplicationOperator f) -
        (multiplicationOperator f).comp (hamiltonian κ potential internalH) =
      (spatialHamiltonian κ potential).comp (multiplicationOperator f) -
        (multiplicationOperator f).comp (spatialHamiltonian κ potential) := by
  rw [hamiltonian]
  apply LinearMap.ext
  intro ψ
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  have hcomm := congrArg (fun T : Spinor →ₗ[ℂ] Spinor => T ψ)
    (spatialLift_comp_internalOperator_comm
      (SchwartzKinetic1D.multiplicationOperator f) internalH)
  have hcomm' :
      internalOperator internalH (multiplicationOperator f ψ) =
        multiplicationOperator f (internalOperator internalH ψ) := by
    simpa [multiplicationOperator] using hcomm.symm
  rw [hcomm']
  abel

/-- The spinor localization has the same first-order Heisenberg current identity as the scalar
Schwartz model, independently of the internal Hamiltonian matrix. -/
theorem heisenberg_localization_eq_symmetrized_velocity
    (ℏ κ : ℝ) (potential : Spatial) (internalH : SpinMatrix) (f : Spatial) :
    (Complex.I / (ℏ : ℂ)) •
        ((hamiltonian κ potential internalH).comp (multiplicationOperator f) -
          (multiplicationOperator f).comp (hamiltonian κ potential internalH)) =
      (1 / 2 : ℂ) •
        ((multiplicationOperator (derivative f)).comp (velocityOperator ℏ κ) +
          (velocityOperator ℏ κ).comp (multiplicationOperator (derivative f))) := by
  rw [hamiltonian_localization_commutator_eq_spatial]
  apply LinearMap.ext
  intro ψ
  funext a
  have hbase := congrArg
    (fun T : Spatial →ₗ[ℂ] Spatial => T (ψ a))
    (SchwartzKinetic1D.heisenberg_localization_eq_symmetrized_velocity ℏ κ potential f)
  simpa [spatialHamiltonian, multiplicationOperator, velocityOperator, derivative, spatialLift] using hbase

/-- For the full spinor Hamiltonian, the commutator with spin is entirely generated by the internal
matrix term; scalar spatial dynamics contributes no spin torque. -/
theorem hamiltonian_spin_commutator_eq_internal
    (κ : ℝ) (potential : Spatial) (internalH : SpinMatrix)
    (ℏ : ℝ) (axis : SpinAxis) :
    (hamiltonian κ potential internalH).comp (spinOperator ℏ axis) -
        (spinOperator ℏ axis).comp (hamiltonian κ potential internalH) =
      (internalOperator internalH).comp (spinOperator ℏ axis) -
        (spinOperator ℏ axis).comp (internalOperator internalH) := by
  rw [hamiltonian]
  apply LinearMap.ext
  intro ψ
  simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  have hcomm := congrArg (fun T : Spinor →ₗ[ℂ] Spinor => T ψ)
    (spatialHamiltonian_comp_spinOperator_comm κ potential ℏ axis)
  have hcomm' :
      spatialHamiltonian κ potential (spinOperator ℏ axis ψ) =
        spinOperator ℏ axis (spatialHamiltonian κ potential ψ) := by
    simpa only [LinearMap.comp_apply] using hcomm
  rw [hcomm']
  abel

end
end SchwartzSpinor1D
