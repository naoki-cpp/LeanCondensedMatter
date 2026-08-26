import LeanCondensedMatter.SecondQuantization.Fermionic.Transport.KuboBastinSpectral

set_option linter.style.header false

/-!
# Retired directional Kubo–Bastin trace shim

The former API in this module specialized an artificial trace carrier obtained by multiplying an
already-computed scalar spectral response by a trace-one density operator. That representation has
been retired.

Directional finite-frequency Kubo–Bastin responses are owned by `KuboBastinSpectral`; genuine
operator traces enter only in the canonical static Bastin/Středa layer. This file remains
temporarily as an import-compatible shim and intentionally declares no API.
-/
