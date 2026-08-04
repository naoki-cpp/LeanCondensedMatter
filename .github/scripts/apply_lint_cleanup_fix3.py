from pathlib import Path

root = Path(".")


def read(rel: str) -> str:
    return (root / rel).read_text()


def write(rel: str, content: str) -> None:
    (root / rel).write_text(content)


rel = "LeanCondensedMatter/Analysis/Operator/TraceClass/Bundled.lean"
content = read(rel)
content = content.replace(
    "@[simp]\ntheorem trace_eq_spectralTrace",
    "omit [CompleteSpace H] in\n@[simp]\ntheorem trace_eq_spectralTrace",
)
content = content.replace(
    """    0 ≤ h.trace := by
  simpa using ContinuousLinearMap.trace_nonneg hpos""",
    """    0 ≤ h.trace := by
  rw [h.trace_eq_spectralTrace]
  exact ContinuousLinearMap.trace_nonneg hpos""",
)
content = content.replace(
    """    HasSum (fun i => diagonalExpectationValue T h.isSelfAdjoint (d i)) h.trace := by
  simpa using
    ContinuousLinearMap.hasSum_diagonalExpectationValue_eq_spectralTrace""",
    """    HasSum (fun i => diagonalExpectationValue T h.isSelfAdjoint (d i)) h.trace := by
  rw [h.trace_eq_spectralTrace]
  exact ContinuousLinearMap.hasSum_diagonalExpectationValue_eq_spectralTrace""",
)
content = content.replace(
    """      ∑' i, diagonalExpectationValue T h.isSelfAdjoint (d i) ≤ h.trace := by
  simpa using
    ContinuousLinearMap.sum_diagonalExpectationValue_le_spectralTrace""",
    """      ∑' i, diagonalExpectationValue T h.isSelfAdjoint (d i) ≤ h.trace := by
  rw [h.trace_eq_spectralTrace]
  exact ContinuousLinearMap.sum_diagonalExpectationValue_le_spectralTrace""",
)
content = content.replace(
    """    hadd.trace = hT.trace + hT'.trace := by
  simpa using ContinuousLinearMap.spectralTrace_add""",
    """    hadd.trace = hT.trace + hT'.trace := by
  rw [hadd.trace_eq_spectralTrace, hT.trace_eq_spectralTrace, hT'.trace_eq_spectralTrace]
  exact ContinuousLinearMap.spectralTrace_add""",
)
content = content.replace(
    """    hTT'.trace = hT'T.trace := by
  simpa using ContinuousLinearMap.spectralTrace_comp_comm""",
    """    hTT'.trace = hT'T.trace := by
  rw [hTT'.trace_eq_spectralTrace, hT'T.trace_eq_spectralTrace]
  exact ContinuousLinearMap.spectralTrace_comp_comm""",
)
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Algebra/Occupation.lean"
content = read(rel).replace(
    "\n@[simp]\ntheorem particleNumber_vacuum",
    "\nomit [DecidableEq Mode] in\n@[simp]\ntheorem particleNumber_vacuum",
    1,
)
write(rel, content)

for rel in [
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CreationAnnihilation.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CCR.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/ExchangeAlgebra.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/NumberOperator.lean",
]:
    content = read(rel).replace(
        "variable {Mode : Type*} [DecidableEq Mode]",
        "variable {Mode : Type*}\n\nlocal instance : DecidableEq Mode := Classical.decEq Mode",
        1,
    )
    write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean"
content = read(rel)
content = content.replace(
    "variable {Mode : Type*}",
    "variable {Mode : Type*}\n\nlocal instance : DecidableEq Mode := Classical.decEq Mode",
    1,
)
content = content.replace("omit in\n", "")
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Thermal/QuantumLinkedCluster.lean"
content = read(rel).replace(
    "variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]",
    "variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]",
    1,
)
write(rel, content)

print("second compatibility pass applied")
