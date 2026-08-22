import LeanCondensedMatter.Transport.Foundations
import LeanCondensedMatter.Transport.ResolventAPI
import LeanCondensedMatter.Transport.KuboBastin
import LeanCondensedMatter.Transport.Streda
import LeanCondensedMatter.Transport.Disorder

set_option linter.style.header false

/-!
# Transport

Public entry point for generic transport infrastructure, organized into five logical layers:

- `Transport.Foundations` — finite physical volume, normalization, scalar conductivity tables, and
  finite-dimensional trace infrastructure;
- `Transport.ResolventAPI` — retarded/advanced resolvents, spectral action, and energy derivatives;
- `Transport.KuboBastin` — finite regularized Kubo–Bastin and occupation/common-energy bridges;
- `Transport.Streda` — operator/trace Středa kernels, decomposition, integration, and spectral forms;
- `Transport.Disorder` — exact finite disorder plus Born/advanced-Born/SCBA approximation layers.

Concrete model umbrellas such as `LeanCondensedMatter.Transport.AnomalousHall` remain explicit
downstream imports rather than part of this generic umbrella. Model-specific fermionic transport
adapters likewise remain downstream in `SecondQuantization.Fermionic`.

Implementation modules should continue to import the narrow leaves they use; these umbrellas expose
the architecture and stable public grouping without forcing broad dependencies into leaf modules.
-/
