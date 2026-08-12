import LeanCondensedMatter.SecondQuantization.Fermionic.Algebra.AlgebraicFock
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ChargeDensity
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ContinuumChargeDensity1D
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.BoundedCurrentResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.PeierlsContactResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.HermitianBondCurrentResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.GeometricCurrentResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.FrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.HarmonicSourceResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StationaryFrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.InfiniteTimeFrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.SpectralFrequencyResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.ConductivityNormalization
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.KuboGreenwood
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.KuboBastinSpectral
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.KuboBastinTrace
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.StaticKuboBastinResponse
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Validation.FiniteToys
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Validation.TwoLevelExplicit
import LeanCondensedMatter.SecondQuantization.Fermionic.Field.Validation.TwoSiteDimer

set_option linter.style.header false

/-!
# Fermionic field and response adapters

This umbrella is downstream of the canonical fermionic algebra and lattice/model layers.

- `Fermionic.Algebra.AlgebraicFock` owns the basis-independent exterior-Fock algebra, creation and
  annihilation operators, CAR, occupation equivalences, and algebraic second quantization.
- `Fermionic.Lattice` owns discrete lattice states, locally finite hopping, site and bond currents,
  Peierls families, finite-lattice bounded model realizations, Hermiticity facts, rank-one lattice
  specializations, and geometric current constructions.
- `Fermionic.Field` retains the basis-independent charge-density interface, its continuum
  specialization, and the downstream Kubo/frequency/conductivity/validation adapters that consume
  lattice model operators.
- `Fermionic.Transport` owns the Středa, Ward, disorder, and related transport adapters.

The intended dependency direction is

```text
Fermionic.Algebra
      ↓
Fermionic.Lattice
      ↓
Fermionic.Field / Fermionic.Transport
```

No lattice/model forwarding modules are retained under `Fermionic.Field`; consumers import the
canonical `Fermionic.Lattice` owner and explicitly qualify or open its namespace.
-/
