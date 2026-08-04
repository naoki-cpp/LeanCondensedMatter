from pathlib import Path

root = Path(".")


def read(rel: str) -> str:
    return (root / rel).read_text()


def write(rel: str, content: str) -> None:
    (root / rel).write_text(content)


for rel in [
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CreationAnnihilation.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CCR.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/ExchangeAlgebra.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean",
]:
    content = read(rel)
    marker = "namespace SecondQuantization\nnamespace Bosonic\n\n"
    replacement = marker + "noncomputable section\n\n"
    if replacement not in content:
        if marker not in content:
            raise SystemExit(f"namespace marker missing in {rel}")
        content = content.replace(marker, replacement, 1)
    write(rel, content)

rel = "LeanCondensedMatter/QuantumTheory/DensityOperator/Basic.lean"
content = read(rel)
old = """  have htrace := ρ.spectralTrace_eq_one
  change (∑' b : EigenvectorIndex ρ.op, b.1.1) = 1 at htrace
"""
new = """  have htrace := ρ.spectralTrace_eq_one
  rw [ρ.spectralTraceClass.trace_eq_spectralTrace] at htrace
  change (∑' b : EigenvectorIndex ρ.op, b.1.1) = 1 at htrace
"""
if old not in content:
    raise SystemExit("density trace proof marker missing")
write(rel, content.replace(old, new, 1))

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Thermal/QuantumLinkedCluster.lean"
content = read(rel)
old = """  rw [hfilter]

/-! ## The occupation projector"""
new = """  rw [hfilter]
  rfl

/-! ## The occupation projector"""
if old not in content:
    raise SystemExit("occupation singleton proof marker missing")
write(rel, content.replace(old, new, 1))

print("final local compatibility fixes applied")
