import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Antiunitary
import LeanCondensedMatter.QuantumTheory.LinearResponse.Lehmann.Eigenbasis.Data
import LeanCondensedMatter.Transport.FiniteConductivityTable.Reciprocity

set_option linter.style.header false

/-!
# Antiunitary-to-Lehmann charge-current reciprocity bridge

The input is a family of bounded self-adjoint free systems with genuine
energy eigenbases, a common reduced Planck constant, and a supplied
antiunitary map. The reversed eigenbasis is the antiunitary image of the
original eigenbasis, and directional charge currents are self-adjoint
and odd under the antiunitary covariance relation.

These operator-level assumptions imply the conjugation and reversal
identities required by `FiniteReciprocalCurrentData`. The generic finite
Kubo–Lehmann reciprocity theorem then gives reciprocal normalized
conductivity tensors without assuming the conductivity identity itself.

Checking Hamiltonian covariance, basis pairing, and Peierls-contact
covariance for a concrete material remains a model-specific obligation.
-/

namespace QuantumTheory.Transport

open QuantumTheory.LinearResponse

noncomputable section

/-- Operator-level data sufficient to instantiate the finite Lehmann
charge-current Onsager theorem. The system's spectral eigenbasis is
explicit, rather than an arbitrary table of matrix elements. -/
structure AntiunitaryCurrentPairing (M ι d H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  /-- Reversal of all time-reversal-odd controls. -/
  reverse : M → M
  /-- Shared physical reduced Planck constant. -/
  hbar : ℝ
  /-- The bounded quantum system for each set of controls. -/
  system : M → BoundedFreeSystem H
  /-- The system-specific Planck constants agree with the shared one. -/
  system_hbar : ∀ m, (system m).hbar = hbar
  /-- A genuine energy eigenbasis and its normalized diagonal state. -/
  spectral : (m : M) → EnergyEigenbasisLehmannData (system m) ι
  /-- Supplied antiunitary on the common Hilbert space. -/
  timeReversal : AntiunitaryMap H
  /-- Reversed eigenstates are antiunitary images, at the same spectral label. -/
  basis_reverse : ∀ m a,
    (spectral (reverse m)).basis a =
      timeReversal.toFun ((spectral m).basis a)
  /-- Reversed energy eigenvalues agree in the paired labeling. -/
  energy_reverse : ∀ m a,
    (spectral (reverse m)).energy a = (spectral m).energy a
  /-- The paired equilibrium occupations agree. -/
  probability_reverse : ∀ m a,
    (spectral (reverse m)).probability a = (spectral m).probability a
  /-- Directional bounded charge-current operators. -/
  current : M → d → (H →L[ℂ] H)
  /-- The charge-current operators are Hermitian. -/
  current_selfAdjoint : ∀ m i, IsSelfAdjoint (current m i)
  /-- Each charge current is odd under antiunitary time reversal. -/
  current_covariant : ∀ m i x,
    timeReversal.toFun (current m i x) =
      -(current (reverse m) i (timeReversal.toFun x))
  /-- Scalar expectation of the observable-variation/contact term. -/
  contact : M → d → d → ℂ
  /-- Reciprocal contact expectations of the two current directions. -/
  contact_reverse : ∀ m i j, contact m i j = contact (reverse m) j i

namespace AntiunitaryCurrentPairing

variable {M ι d H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (data : AntiunitaryCurrentPairing M ι d H)

/-- Hermiticity of the charge-current operator determines the conjugate
transposed matrix element in its actual eigenbasis. -/
theorem star_currentMatrixElement (m : M) (i : d) (a b : ι) :
    (starRingEnd ℂ)
        (inner ℂ ((data.spectral m).basis a)
          (data.current m i ((data.spectral m).basis b))) =
      inner ℂ ((data.spectral m).basis b)
        (data.current m i ((data.spectral m).basis a)) := by
  calc
    _ = inner ℂ (data.current m i ((data.spectral m).basis b))
          ((data.spectral m).basis a) := by
          simp [inner_conj_symm]
    _ = inner ℂ ((data.spectral m).basis b)
          (data.current m i ((data.spectral m).basis a)) := by
          exact (data.current_selfAdjoint m i).isSymmetric.apply_clm _ _

/-- Time-reversal covariance makes each reversed current matrix element
the negative conjugate of the original one. This is an operator-level
derivation of the scalar condition used by the finite Lehmann theorem. -/
theorem currentMatrixElement_reverse (m : M) (i : d) (a b : ι) :
    inner ℂ ((data.spectral (data.reverse m)).basis a)
      (data.current (data.reverse m) i
        ((data.spectral (data.reverse m)).basis b)) =
      -(starRingEnd ℂ)
        (inner ℂ ((data.spectral m).basis a)
          (data.current m i ((data.spectral m).basis b))) := by
  have hcov :
      data.current (data.reverse m) i
          (data.timeReversal.toFun ((data.spectral m).basis b)) =
        -(data.timeReversal.toFun
          (data.current m i ((data.spectral m).basis b))) := by
    have h := congrArg (fun x : H => -x)
      (data.current_covariant m i ((data.spectral m).basis b))
    simpa only [neg_neg] using h.symm
  rw [data.basis_reverse m a, data.basis_reverse m b, hcov]
  simp only [inner_neg_right, data.timeReversal.inner_map]

/-- Canonical scalar spectral input built from a genuine eigenbasis and
current operators, with all required reversal identities proved above. -/
noncomputable def toReciprocalCurrentData :
    FiniteReciprocalCurrentData M ι d where
  reverse := data.reverse
  energy := fun m => (data.spectral m).energy
  probability := fun m => (data.spectral m).probability
  current := fun m i a b =>
    inner ℂ ((data.spectral m).basis a)
      (data.current m i ((data.spectral m).basis b))
  contact := data.contact
  energy_reverse := data.energy_reverse
  probability_reverse := data.probability_reverse
  current_conj := data.star_currentMatrixElement
  current_reverse := data.currentMatrixElement_reverse
  contact_reverse := data.contact_reverse

/-- Microscopic antiunitary current covariance is sufficient for the
Onsager–Casimir property of the finite Kubo–Lehmann conductivity family,
at a shared Planck constant and fixed driving/switching rates. -/
theorem conductivityFamily_isOnsagerReciprocal [Fintype ι]
    (volume : PositiveVolume) (omega eta : ℝ) :
    ConductivityTensor.IsOnsagerReciprocal
      ((data.toReciprocalCurrentData).conductivityFamily
        volume data.hbar omega eta)
      data.reverse := by
  exact (data.toReciprocalCurrentData).conductivityFamily_isOnsagerReciprocal
    volume data.hbar omega eta

end AntiunitaryCurrentPairing

end
end QuantumTheory.Transport
