import LeanCondensedMatter.Transport.FiniteConductivityTable
import LeanCondensedMatter.Transport.Core.ConductivityTensor
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Onsager reciprocity from a finite charge-current Lehmann table

This module derives reciprocal ordered conductivity components from *spectral*
time-reversal data, rather than assuming reciprocity of the conductivity tensor.

Reversed eigenstates are indexed by the same abstract finite label as their original
time-reversed partners. The hypotheses express preservation of energies and diagonal
state occupations, the antiunitary conjugation and odd time-reversal parity of each
charge-current matrix element, Hermiticity of each current, and the reciprocal
Peierls/observable-variation contact expectation.

The response is evaluated by the existing canonical `finiteLehmannTableResponse`,
including its causal frequency denominator, and `finiteConductivityTableValue`,
including the contact term and physical finite-volume electric-field normalization.
No independent Kubo formula or postulated conductivity reciprocity is introduced.

It is a finite-spectral reduction, *not yet* an operator-level construction of the
antiunitary transformation or a thermodynamic/zero-switching/DC limit theorem.
-/

namespace QuantumTheory.Transport

open QuantumTheory.LinearResponse

noncomputable section

/-- Spectral charge-current data for an antiunitarily paired magnetic system.
The label `a` at reversed magnetization denotes the time reverse of label `a`
at the original magnetization. The current matrix has odd time-reversal parity. -/
structure FiniteReciprocalCurrentData (M ι d : Type*) where
  reverse : M → M
  energy : M → ι → ℝ
  probability : M → ι → ℝ
  current : M → d → ι → ι → ℂ
  contact : M → d → d → ℂ
  energy_reverse : ∀ m a, energy (reverse m) a = energy m a
  probability_reverse : ∀ m a, probability (reverse m) a = probability m a
  current_conj : ∀ m i a b, Complex.conj (current m i a b) = current m i b a
  current_reverse : ∀ m i a b,
    current (reverse m) i a b = -Complex.conj (current m i a b)
  contact_reverse : ∀ m i j, contact m i j = contact (reverse m) j i

namespace FiniteReciprocalCurrentData

variable {M ι d : Type*} (data : FiniteReciprocalCurrentData M ι d)

/-- Existing physical conductivity table specialized to two directional charge currents. -/
noncomputable def finiteTable (m : M) (i j : d) : FiniteConductivityTable ι where
  lehmann :=
    { energy := data.energy m
      probability := data.probability m
      matrixA := data.current m i
      matrixB := data.current m j }
  contact := data.contact m i j

/-- The antiunitary reversal and Hermiticity hypotheses give the transposed
ordered product of the two current vertices, including the two odd-current signs. -/
theorem current_product_reverse (m : M) (i j : d) (a b : ι) :
    data.current m i a b * data.current m j b a =
      data.current (data.reverse m) j a b *
        data.current (data.reverse m) i b a := by
  rw [data.current_reverse m j a b, data.current_reverse m i b a,
    data.current_conj m j a b, data.current_conj m i b a]
  ring

/-- Equality of *canonical* finite Lehmann transition terms after time reversal.
The energy gap and causal frequency denominator are preserved, without swapping
the ordered spectral indices or altering the frequency/regulator. -/
theorem transition_reverse (hbar omega eta : ℝ)
    (m : M) (i j : d) (a b : ι) :
    (finiteLehmannTableTransitionData hbar
        (data.finiteTable m i j).lehmann (a, b)).frequencyTerm omega eta =
      (finiteLehmannTableTransitionData hbar
        (data.finiteTable (data.reverse m) j i).lehmann (a, b)).frequencyTerm omega eta := by
  dsimp [finiteTable, finiteLehmannTableTransitionData,
    orderedLehmannTransitionData, orderedLehmannTransitionWeight,
    LehmannTransitionData.frequencyTerm, lehmannTerm]
  rw [data.energy_reverse m a, data.energy_reverse m b,
    data.probability_reverse m a, data.probability_reverse m b,
    data.current_reverse m j a b, data.current_reverse m i b a,
    data.current_conj m j a b, data.current_conj m i b a]
  ring

/-- The full finite Lehmann *vertex* response is reciprocal, at any supplied
frequency and switching rate. This is a spectral Kubo result, not a tensor axiom. -/
theorem finiteLehmannTableResponse_reverse [Fintype ι]
    (hbar omega eta : ℝ) (m : M) (i j : d) :
    finiteLehmannTableResponse hbar omega eta (data.finiteTable m i j).lehmann =
      finiteLehmannTableResponse hbar omega eta
        (data.finiteTable (data.reverse m) j i).lehmann := by
  unfold finiteLehmannTableResponse
  apply Finset.sum_congr rfl
  intro mn _
  rcases mn with ⟨a, b⟩
  exact data.transition_reverse hbar omega eta m i j a b

/-- Reciprocity of the *physical* finite-volume conductivity follows from the
spectral Kubo theorem and the independently supplied reciprocal contact term. -/
theorem finiteConductivityTableValue_reverse [Fintype ι]
    (volume : PositiveVolume) (hbar omega eta : ℝ) (m : M) (i j : d) :
    finiteConductivityTableValue volume hbar omega eta (data.finiteTable m i j) =
      finiteConductivityTableValue volume hbar omega eta
        (data.finiteTable (data.reverse m) j i) := by
  calc
    _ =
        (finiteLehmannTableResponse hbar omega eta (data.finiteTable m i j).lehmann +
          data.contact m i j) *
          finiteVolumeConductivityNormalization volume omega eta := rfl
    _ =
        (finiteLehmannTableResponse hbar omega eta
            (data.finiteTable (data.reverse m) j i).lehmann +
          data.contact (data.reverse m) j i) *
          finiteVolumeConductivityNormalization volume omega eta := by
            rw [data.finiteLehmannTableResponse_reverse hbar omega eta m i j,
              data.contact_reverse m i j]
    _ = _ := rfl

/-- A complete finite-volume conductivity tensor constructed from the already
normalized canonical charge-current Lehmann tables for every direction pair. -/
noncomputable def conductivityFamily [Fintype ι]
    (volume : PositiveVolume) (hbar omega eta : ℝ) :
    M → ConductivityTensor d :=
  fun m =>
    { component := fun i j =>
        finiteConductivityTableValue volume hbar omega eta (data.finiteTable m i j) }

/-- Unlike the conditional tensor-level reciprocity projection, this theorem
*derives* the Onsager property from energy, occupation, antiunitary-current,
Hermiticity, and contact-transformation hypotheses of the finite spectral Kubo data. -/
theorem conductivityFamily_isOnsagerReciprocal [Fintype ι]
    (volume : PositiveVolume) (hbar omega eta : ℝ) :
    ConductivityTensor.IsOnsagerReciprocal
      (data.conductivityFamily volume hbar omega eta) data.reverse := by
  intro m i j
  exact data.finiteConductivityTableValue_reverse volume hbar omega eta m i j

end FiniteReciprocalCurrentData

end
end QuantumTheory.Transport
