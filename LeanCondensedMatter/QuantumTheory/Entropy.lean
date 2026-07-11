import LeanCondensedMatter.QuantumTheory.DensityOperator
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Von Neumann entropy and Boltzmann's principle

Formalizes the von Neumann entropy of a density operator, the mathematical content of
**Boltzmann's principle**: the postulate that `k_B` times the von Neumann entropy equals
the thermodynamic entropy `S[U,V,N]`.

**Scope note:** Boltzmann's principle itself — the equality of `k_B * vonNeumannEntropy ρ`
with a thermodynamic entropy `S[U,V,N]` — is a postulate connecting this formal quantity to
thermodynamics, which is not formalized in this project (see `notes/model-and-assumptions.md`
and the scope discussion for the Linked Cluster Theorem target in `notes/roadmap.md`, which
argues thermodynamics proper is out of scope for that target). Only the mathematical object
the postulate is about — the von Neumann entropy of a density operator — is defined here.
-/

namespace QuantumTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {n : ℕ} (hn : Module.finrank ℂ H = n)

/-- The von Neumann entropy `-Tr[ρ ln ρ]` of a density operator `ρ`, computed from its
eigenvalues (which are real since `ρ` is self-adjoint). The physical entropy of Boltzmann's
principle is `k_B` times this quantity. -/
noncomputable def vonNeumannEntropy (ρ : DensityOperator H) : ℝ :=
  ∑ i : Fin n, Real.negMulLog (ρ.2.1.isSymmetric.eigenvalues hn i)

end QuantumTheory
