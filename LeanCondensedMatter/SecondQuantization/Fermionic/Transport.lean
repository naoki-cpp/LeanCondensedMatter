import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CurrentInsertions
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.SymmetrizedVelocityCurrent
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.CorrectedCurrentResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.OneBodyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.SpinCurrentResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.ConductivityNormalization
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.ChargeCurrentChannel
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinSpectral
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboGreenwood
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinOccupation
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinCommonEnergy
import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.FiniteDisorderConductivity

set_option linter.style.header false

/-!
# Fermionic transport adapters

Canonical downstream owner for fermionic Kubo/frequency response, intrinsic-flux and generalized
current response, conductivity normalization, directional Kubo–Greenwood/spectral Bastin/Středa,
finite-table evaluation, and finite-disorder adapters. Generic reusable response and density
theory remains under `QuantumTheory`, while statistics-independent Kubo–Bastin, resolvent, and
Středa infrastructure lives under `QuantumTheory.Transport`.

This layer consumes `Fermionic.Lattice` model operators and does not own finite toy checks; those are
terminal consumers under `Fermionic.Validation`. Old transport declarations are not forwarded from
`Fermionic.Field`.
-/
