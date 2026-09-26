import LeanCondensedMatter.SecondQuantization.Fermionic.Lattice.Spinful
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.SymmetrizedVelocityCurrent
import LeanCondensedMatter.QuantumTheory.SpinHalf
import LeanCondensedMatter.QuantumTheory.LinearResponse.ResponseChannel

set_option linter.style.header false

/-!
# Finite spin-current / electric-source cross response

This module gives a concrete generalized-current response on the finite spinful lattice
`Site × Fin 2`. A physical-space vector `n : SpinHalf.Direction` selects the measured spin
observable `S(n) = ℏ_spin (n · σ) / 2`; the Pauli coordinates remain internal representation data.
The measured spin current is

```text
J^(S(n)) = dΓ( 1/2 {v, S(n)} ),
```

transported to the bounded finite-lattice Hilbert realization. The source is an ordinary electric
bond current, so the response kernel is genuinely mixed:

```text
χᴿ_{J^(S(n)), J^charge_{u→v}}.
```

No equality between spin current and charge current is assumed. The velocity is supplied as a
one-particle operator so later finite Rashba/Dirac models can instantiate it with the velocity derived
from their Hamiltonian. Conductivity normalization and source-dependent contact terms remain separate
from this causal cross-response kernel. The symmetrized-current/proper-current distinction is
motivated by Shi, Zhang, Xiao, and Niu, *Phys. Rev. Lett.* **96**, 076604 (2006),
[doi:10.1103/PhysRevLett.96.076604](https://doi.org/10.1103/PhysRevLett.96.076604); this module
does not identify this symmetrized (conventional) operator with their torque-dipole-completed current. The finite
Rashba, disorder-vertex, and inverse-response follow-ups are tracked in
`notes/roadmaps/spin-hall.md`.
-/

namespace SecondQuantization
namespace Fermionic
namespace Transport

open _root_.SecondQuantization.Fermionic.Lattice
open QuantumTheory.LinearResponse

noncomputable section

variable {Site : Type*} [LinearOrder Site] [Fintype Site]

/-- One-particle spin-1/2 observable associated with a physical polarization vector. -/
noncomputable def spinOneBody
    (spinScale : ℝ) (polarization : QuantumTheory.SpinHalf.Direction) :
    LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site) :=
  internalOneBody (QuantumTheory.SpinHalf.spinMatrix spinScale polarization)

/-- Neutral fixed-observable response channel for a finite spin current selected by a physical
polarization vector and driven by an electric bond-current source. -/
noncomputable def boundedSpinCurrentBondSourceResponseChannel
    (velocity : LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site))
    (spinScale : ℝ) (polarization : QuantumTheory.SpinHalf.Direction)
    (ℏ q : ℂ)
    (K : LocallyFiniteHopping (SpinfulSite Site))
    (u v : SpinfulSite Site) :
    ResponseChannel (FiniteLatticeHilbertFock (SpinfulSite Site)) :=
  ResponseChannel.fixed
    (boundedSymmetrizedVelocityCurrent velocity (spinOneBody spinScale polarization))
    (boundedBondCurrent ℏ q K u v)

/-- Retarded response of a finite spin current selected by a physical polarization vector to an
electric bond-current source.

The measured observable and source are intentionally distinct. The source carries electric charge
`q`, while the measured current transports `S(n)`. -/
noncomputable def boundedSpinCurrentBondSourceRetardedSusceptibility
    (system : QuantumTheory.LinearResponse.BoundedFreeSystem
      (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (expectation : QuantumTheory.LinearResponse.NormalizedExpectation
      (FiniteLatticeHilbertFock (SpinfulSite Site)))
    (velocity : LatticeState (SpinfulSite Site) →ₗ[ℂ] LatticeState (SpinfulSite Site))
    (spinScale : ℝ) (polarization : QuantumTheory.SpinHalf.Direction)
    (ℏ q : ℂ)
    (K : LocallyFiniteHopping (SpinfulSite Site))
    (u v : SpinfulSite Site) (t s : ℝ) : ℂ :=
  (boundedSpinCurrentBondSourceResponseChannel
    velocity spinScale polarization ℏ q K u v).retardedKernel
    system expectation t s

end
end Transport
end Fermionic
end SecondQuantization
