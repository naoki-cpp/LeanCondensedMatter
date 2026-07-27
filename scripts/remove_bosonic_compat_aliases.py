#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def replace_exact(path: Path, old: str, new: str) -> None:
    text = path.read_text(encoding="utf-8")
    if old not in text:
        raise SystemExit(f"expected text not found in {path}: {old!r}")
    path.write_text(text.replace(old, new, 1), encoding="utf-8")


occupation = ROOT / "LeanCondensedMatter/SecondQuantization/Bosonic/Foundations/Occupation.lean"
text = occupation.read_text(encoding="utf-8")
text = text.replace(
    "The canonical API lives in `SecondQuantization.Bosonic`. Compatibility aliases for the older\n"
    "`SecondQuantization`-level names are retained at the end of the file.",
    "The public API lives in `SecondQuantization.Bosonic`; the former plain-namespace compatibility\n"
    "aliases have been removed.",
    1,
)
marker = "\n/-! ## Compatibility aliases\n"
if marker not in text:
    raise SystemExit("Bosonic occupation compatibility block was not found")
text = text.split(marker, 1)[0].rstrip() + "\n\nend SecondQuantization\n"
occupation.write_text(text, encoding="utf-8")

fock = ROOT / "LeanCondensedMatter/SecondQuantization/Bosonic/Foundations/FockSpace.lean"
replace_exact(
    fock,
    "`Bosonic.FockSpace` is the canonical name. `FockSpaceBosonic` is retained as a compatibility alias.",
    "The public type is `Bosonic.FockSpace`.",
)
replace_exact(
    fock,
    "\n/-- Compatibility alias for the original bosonic Fock-space name. -/\n"
    "abbrev FockSpaceBosonic (Mode : Type*) [DecidableEq Mode] := FockSpace Mode\n",
    "",
)

algebraic_fock = ROOT / "LeanCondensedMatter/SecondQuantization/Common/Algebra/AlgebraicFock.lean"
replace_exact(
    algebraic_fock,
    "both `FockSpaceFermionic Mode` (basis\n"
    "`FermionOccupation Mode := Finset Mode`) and `FockSpaceBosonic Mode` (basis\n"
    "`Occupation Mode := Mode →₀ ℕ`)",
    "both `FockSpaceFermionic Mode` (basis\n"
    "`FermionOccupation Mode := Finset Mode`) and `Bosonic.FockSpace Mode` (basis\n"
    "`Bosonic.Occupation Mode := Mode →₀ ℕ`)",
)
replace_exact(
    algebraic_fock,
    "concrete `Config` (`FermionOccupation Mode`/`Occupation Mode`)",
    "concrete `Config` (`FermionOccupation Mode`/`Bosonic.Occupation Mode`)",
)

audit = ROOT / "notes/roadmaps/second-quantization-common-audit.md"
replace_exact(
    audit,
    "No compatibility shims remain at the former flat Common or Fermionic implementation paths. The\n"
    "statistics-specific Bloch–de Dominicis specializations now live under each statistics' `Thermal/`\n"
    "directory. Bosonic plain-namespace occupation/Fock aliases still exist as compatibility API, but\n"
    "internal Bosonic code uses the canonical `SecondQuantization.Bosonic` names.",
    "No compatibility shims remain at the former flat Common or Fermionic implementation paths, and the\n"
    "legacy plain-namespace Bosonic occupation/Fock aliases have also been removed. The\n"
    "statistics-specific Bloch–de Dominicis specializations live under each statistics' `Thermal/`\n"
    "directory, while the canonical Bosonic API lives exclusively under `SecondQuantization.Bosonic`.",
)

roadmap = ROOT / "notes/roadmaps/second-quantization.md"
replace_exact(
    roadmap,
    "(`Occupation`, `basisState`, `create`,\n"
    "`annihilate`, etc.) live under `namespace SecondQuantization.Bosonic`, distinct from the fermionic\n"
    "line's plain `SecondQuantization` namespace. Legacy plain-namespace occupation/Fock aliases remain\n"
    "for compatibility, but the Bosonic implementation now uses only the canonical names internally.",
    "(`Occupation`, `basisState`, `create`,\n"
    "`annihilate`, etc.) live exclusively under `namespace SecondQuantization.Bosonic`, distinct from\n"
    "the fermionic line's plain `SecondQuantization` namespace. The former plain-namespace\n"
    "occupation/Fock aliases have been removed.",
)

for path in ROOT.rglob("*.lean"):
    content = path.read_text(encoding="utf-8")
    if "FockSpaceBosonic" in content:
        raise SystemExit(f"stale FockSpaceBosonic reference remains in {path}")

for path in [audit, roadmap, occupation, fock]:
    content = path.read_text(encoding="utf-8")
    for stale in [
        "Legacy plain-namespace occupation/Fock aliases remain",
        "plain-namespace occupation/Fock aliases still exist",
        "## Compatibility aliases",
    ]:
        if stale in content:
            raise SystemExit(f"stale compatibility text remains in {path}: {stale}")
