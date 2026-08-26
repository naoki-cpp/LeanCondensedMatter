import LeanCondensedMatter.Transport.KuboBastin.Finite

set_option linter.style.header false

/-!
# Retired finite-dimensional Kubo–Bastin trace shim

The former declarations in this module manufactured an ordinary trace representation by multiplying
an already-computed scalar spectral response by a trace-one density operator. That construction did
not represent the canonical Bastin operator kernel and has been retired.

Finite-frequency Kubo–Bastin responses live in `Transport.KuboBastin.Finite`; genuine ordinary
operator traces belong to the canonical static Bastin/Středa layer under `Transport.Streda`.

This file remains temporarily as an import-compatible shim and intentionally declares no API.
-/
