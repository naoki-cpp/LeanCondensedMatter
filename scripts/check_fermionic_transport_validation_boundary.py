from __future__ import annotations

from architecture_audit_common import finish_audit, repository_root, require_files

ROOT = repository_root(__file__)
FERMIONIC = ROOT / "LeanCondensedMatter" / "SecondQuantization" / "Fermionic"
TRANSPORT = FERMIONIC / "Transport"
VALIDATION = FERMIONIC / "Validation"

TRANSPORT_NAMES = (
    "BoundedOneBodyResponse",
    "ConductivityNormalization",
    "FrequencyResponse",
    "GeometricCurrentResponse",
    "HarmonicSourceResponse",
    "InfiniteTimeFrequencyResponse",
    "KuboBastinSpectral",
    "KuboBastinTrace",
    "KuboGreenwood",
    "SpectralFrequencyResponse",
    "StaticKuboBastinResponse",
    "StationaryFrequencyResponse",
)
VALIDATION_NAMES = ("FiniteToys", "TwoLevelExplicit", "TwoSiteDimer")


def main() -> int:
    errors: list[str] = []
    required = [FERMIONIC / "Transport.lean", FERMIONIC / "Validation.lean"]
    required += [TRANSPORT / f"{name}.lean" for name in TRANSPORT_NAMES]
    required += [VALIDATION / f"{name}.lean" for name in VALIDATION_NAMES]
    # Path-owned declaration namespaces are checked from compiled metadata.
    require_files(errors, required, root=ROOT, description="fermionic transport/validation owner")
    return finish_audit(
        errors,
        failure_heading="Fermionic transport/validation boundary audit failed:",
        success_message="Fermionic transport/validation boundary audit passed.",
    )


if __name__ == "__main__":
    raise SystemExit(main())
