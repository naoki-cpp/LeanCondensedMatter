import LeanCondensedMatter.Models.OrbitalTransport.TwoSite
import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.BoundedMatrixUnitAdjoint
import LeanCondensedMatter.QuantumTheory.LinearResponse.Dynamics.Free
import LeanCondensedMatter.QuantumTheory.LinearResponse.Response.Channel
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Bounded fermionic Kubo response for the two-site internal-orbital model

The four one-particle basis labels are (0,p_x), (0,p_y), (1,p_x), (1,p_y).
Every finite matrix is realized through the canonical bounded second-quantized
matrix units on the *full* 16-dimensional fermionic Fock space.

The Hamiltonian is the second quantization of the explicit two-site orbital
Hamiltonian, rather than an unrelated free propagator. A measured orbital bond
flux is paired with a charge bond-current source derived from the *same*
hopping Hamiltonian. The fixed-observable Kubo channel is a specific response
convention: it does not include the explicit Peierls derivative of a source-
dependent orbital current, and the response to vector potential must not be
called a physical DC orbital Hall conductivity without further contact, field
and geometry normalizations.
-/

namespace SecondQuantization.Fermionic.Validation.TwoSiteOrbitalResponse

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse
open QuantumTheory.Models.OrbitalTransport.TwoSite
open scoped BigOperators

noncomputable section

/-- Full finite fermionic Fock space for four spinless orbital modes. -/
abbrev OrbitalFock := FiniteLatticeHilbertFock (Fin 4)

/-- Four-state one-body matrices are represented by the existing finite-Fock
second-quantization Lie homomorphism, using canonical matrix units. -/
noncomputable def boundedOrbitalMatrix (A : OrbitalMatrix) :
    OrbitalFock →L[ℂ] OrbitalFock :=
  boundedOneBodyOperator
    (∑ i : Fin 4, ∑ j : Fin 4, A i j • matrixUnit i j)

/-- Recover the former matrix-unit expansion directly from linearity of
the canonical one-body second quantization. -/
theorem boundedOrbitalMatrix_eq_sum (A : OrbitalMatrix) :
    boundedOrbitalMatrix A =
      ∑ i : Fin 4, ∑ j : Fin 4, A i j • boundedDgammaMatrixUnit i j := by
  simp only [boundedOrbitalMatrix, map_sum, map_smul,
    boundedOneBodyOperator_eq, boundedDgammaMatrixUnit]

/-- Orbital matrix realization preserves sign reversal. -/
theorem boundedOrbitalMatrix_neg (A : OrbitalMatrix) :
    boundedOrbitalMatrix (-A) = -boundedOrbitalMatrix A := by
  rw [boundedOrbitalMatrix_eq_sum, boundedOrbitalMatrix_eq_sum]
  simp [Finset.sum_neg_distrib, neg_smul]

/-- A Hermitian four-state matrix gives a self-adjoint Fock observable. -/
theorem boundedOrbitalMatrix_selfAdjoint (A : OrbitalMatrix)
    (hA : A.IsHermitian) :
    IsSelfAdjoint (boundedOrbitalMatrix A) := by
  have hEntry (i j : Fin 4) : star (A j i) = A i j := by
    have h := congrArg (fun B : OrbitalMatrix => B i j) hA.star_eq
    simpa [Matrix.conjTranspose_apply] using h
  rw [isSelfAdjoint_iff]
  simp only [boundedOrbitalMatrix_eq_sum, star_sum, star_smul,
    star_boundedDgammaMatrixUnit]
  rw [Finset.sum_comm]
  simp_rw [hEntry]

/-- Explicit two-site Hamiltonian is Hermitian for real hopping and splitting. -/
theorem orbitalHamiltonian_isHermitian (Δ hoppingStrength : ℝ) :
    (hamiltonian Δ hoppingStrength).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hamiltonian, crystalField, hopping]

/-- Bounded Fock Hamiltonian of the same finite orbital model. -/
noncomputable def boundedOrbitalHamiltonian (Δ hoppingStrength : ℝ) :
    OrbitalFock →L[ℂ] OrbitalFock :=
  boundedOrbitalMatrix (hamiltonian Δ hoppingStrength)

/-- Canonical finite free dynamics with the model's Hamiltonian and ℏ=1. -/
noncomputable def orbitalFreeSystem (Δ hoppingStrength : ℝ) :
    BoundedFreeSystem OrbitalFock where
  hamiltonian := ⟨boundedOrbitalHamiltonian Δ hoppingStrength,
    boundedOrbitalMatrix_selfAdjoint _ (orbitalHamiltonian_isHermitian Δ hoppingStrength)⟩
  hbar := 1
  hbar_pos := by norm_num

/-- Second-quantized orbital flux from site zero to one. -/
noncomputable def boundedOrbitalBondFlux (hoppingStrength : ℝ) :
    OrbitalFock →L[ℂ] OrbitalFock :=
  boundedOrbitalMatrix (bondFluxZeroToOne hoppingStrength)

/-- Reversing the bond reverses its bounded orbital current. -/
theorem boundedOrbitalBondFlux_reverse (hoppingStrength : ℝ) :
    boundedOrbitalMatrix (bondFluxOneToZero hoppingStrength) =
      -boundedOrbitalBondFlux hoppingStrength := by
  rw [bondFluxOneToZero_eq_neg, boundedOrbitalMatrix_neg]
  rfl

/-- Charge within the left two-orbital site, with q=1. -/
def chargeProjectorZero : OrbitalMatrix :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 0]

/-- The oriented charge-bond vertex obtained from the same hopping term as
the orbital flux. It is the negative Heisenberg change in the left-site charge. -/
noncomputable def chargeBondSource (hoppingStrength : ℝ) : OrbitalMatrix :=
  -Complex.I • (hopping hoppingStrength * chargeProjectorZero -
    chargeProjectorZero * hopping hoppingStrength)

/-- Bounded charge-current source coupled to an external vector-potential-like
parameter; any physical charge or lattice-spacing factors remain explicit. -/
noncomputable def boundedChargeBondSource (hoppingStrength : ℝ) :
    OrbitalFock →L[ℂ] OrbitalFock :=
  boundedOrbitalMatrix (chargeBondSource hoppingStrength)

/-- A concrete mixed orbital-flux / charge-source causal response channel.
Its fixed measured observable has no explicit source/contact variation by
construction; a Peierls-dependent measured orbital flux requires another channel. -/
noncomputable def orbitalChargeResponseChannel (hoppingStrength : ℝ) :
    ResponseChannel OrbitalFock :=
  ResponseChannel.fixed
    (boundedOrbitalBondFlux hoppingStrength)
    (boundedChargeBondSource hoppingStrength)

end
end SecondQuantization.Fermionic.Validation.TwoSiteOrbitalResponse
