import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Intrinsic
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Response
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.Integral
import LeanCondensedMatter.Transport.AnomalousHall.MassiveDirac.Streda.FiniteBroadeningBornLadder

set_option linter.style.header false

/-!
# Massive-Dirac Středa specialization

Public umbrella for the model-specific Bastin/Středa trace identity, finite-energy surface/sea
decomposition, and finite-`η` Born-Dyson RA-dressed Hall surface bridge.  The bridge dresses only the
retarded-advanced source vertex while retaining the bare source in the RR/AA same-side remainder;
it is not a fully dressed finite-disorder Středa surface primitive.  Bounded-operator and
spectral/resolvent infrastructure is owned by `MassiveDirac.Model`; ladder and Born-Dyson Green
construction remain owned by `MassiveDirac.Disorder`.
-/
