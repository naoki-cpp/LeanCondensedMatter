from pathlib import Path

root = Path(".")


def read(rel: str) -> str:
    return (root / rel).read_text()


def write(rel: str, content: str) -> None:
    (root / rel).write_text(content)


def replace(rel: str, old: str, new: str, count: int = 1) -> None:
    content = read(rel)
    if content.count(old) < count:
        raise SystemExit(f"replacement marker missing in {rel}: {old[:100]!r}")
    write(rel, content.replace(old, new, count))


for rel in [
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CreationAnnihilation.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CCR.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/ExchangeAlgebra.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean",
]:
    content = read(rel)
    old = "\nend Bosonic\nend SecondQuantization"
    new = "\nend\n\nend Bosonic\nend SecondQuantization"
    if new not in content:
        if old not in content:
            raise SystemExit(f"section end marker missing in {rel}")
        content = content.replace(old, new, 1)
    write(rel, content)

rel = "LeanCondensedMatter/QuantumTheory/DensityOperator/Basic.lean"
content = read(rel)
marker = """  spectralTraceClass : SpectralTraceClass op
  spectralTrace_eq_one : spectralTraceClass.trace = 1

/-- A density operator's underlying operator is symmetric. -/
"""
insert = """  spectralTraceClass : SpectralTraceClass op
  spectralTrace_eq_one : spectralTraceClass.trace = 1

/-- The totalized spectral trace of a density operator is one. -/
@[simp]
theorem DensityOperator.spectralTrace_op_eq_one (ρ : DensityOperator H) :
    spectralTrace ρ.op = 1 := by
  rw [← ρ.spectralTraceClass.trace_eq_spectralTrace]
  exact ρ.spectralTrace_eq_one

/-- A density operator's underlying operator is symmetric. -/
"""
if marker not in content:
    raise SystemExit("density structure marker missing")
content = content.replace(marker, insert, 1)
content = content.replace(
    """  have htrace := ρ.spectralTrace_eq_one
  rw [ρ.spectralTraceClass.trace_eq_spectralTrace] at htrace
  change (∑' b : EigenvectorIndex ρ.op, b.1.1) = 1 at htrace
""",
    """  have htrace := ρ.spectralTrace_op_eq_one
  change (∑' b : EigenvectorIndex ρ.op, b.1.1) = 1 at htrace
""",
    1,
)
write(rel, content)

rel = "LeanCondensedMatter/QuantumTheory/Gibbs/State.lean"
content = read(rel)
content = content.replace(
    "trace_nonneg hsummable (gibbsOp_isPositive Hop β).toLinearMap",
    "trace_nonneg (gibbsOp_isPositive Hop β).toLinearMap",
    1,
)
old = """  exact {
    op := r • gibbsOp Hop β
    pos := hpos
    spectralTraceClass := SpectralTraceClass.ofPositive
      (hcompact.smul _) hpos hsummableScaled
    spectralTrace_eq_one := by
      change spectralTrace (r • gibbsOp Hop β) = 1
      rw [spectralTrace_smul hrne hsummable hsummableScaled]
"""
new = """  let htraceClass : SpectralTraceClass (r • gibbsOp Hop β) :=
    SpectralTraceClass.ofPositive (hcompact.smul _) hpos hsummableScaled
  exact {
    op := r • gibbsOp Hop β
    pos := hpos
    spectralTraceClass := htraceClass
    spectralTrace_eq_one := by
      rw [htraceClass.trace_eq_spectralTrace]
      rw [spectralTrace_smul hrne hsummable hsummableScaled]
"""
if old not in content:
    raise SystemExit("Gibbs constructor marker missing")
write(rel, content.replace(old, new, 1))

rel = "LeanCondensedMatter/QuantumTheory/Entropy/Basic.lean"
replace(
    rel,
    """    _ = ρ.spectralTraceClass.trace := rfl
    _ = 1 := ρ.spectralTrace_eq_one
""",
    """    _ = spectralTrace ρ.op := rfl
    _ = 1 := ρ.spectralTrace_op_eq_one
""",
)

rel = "LeanCondensedMatter/QuantumTheory/DensityOperator/Expectation.lean"
content = read(rel)
old = "simpa [SpectralTraceClass.trace, spectralTrace] using ρ.spectralTrace_eq_one"
new = "simpa [spectralTrace] using ρ.spectralTrace_op_eq_one"
if content.count(old) != 2:
    raise SystemExit(f"expected two expectation normalization uses, found {content.count(old)}")
write(rel, content.replace(old, new))

rel = "LeanCondensedMatter/QuantumTheory/DensityOperator/Pure.lean"
old = """noncomputable def pure (ψ : State H) : DensityOperator H where
  op := InnerProductSpace.rankOne ℂ ψ.1 ψ.1
  pos := InnerProductSpace.isPositive_rankOne_self ψ.1
  spectralTraceClass := SpectralTraceClass.ofPositive
    (isCompactOperator_rankOne ψ.1 ψ.1)
    (InnerProductSpace.isPositive_rankOne_self ψ.1)
    (rankOne_hasSummableRealEigenvalues ψ.2)
  spectralTrace_eq_one := rankOne_spectralTrace_eq_one ψ.2
"""
new = """noncomputable def pure (ψ : State H) : DensityOperator H := by
  let htraceClass : SpectralTraceClass
      (InnerProductSpace.rankOne ℂ ψ.1 ψ.1 : H →L[ℂ] H) :=
    SpectralTraceClass.ofPositive
      (isCompactOperator_rankOne ψ.1 ψ.1)
      (InnerProductSpace.isPositive_rankOne_self ψ.1)
      (rankOne_hasSummableRealEigenvalues ψ.2)
  exact {
    op := InnerProductSpace.rankOne ℂ ψ.1 ψ.1
    pos := InnerProductSpace.isPositive_rankOne_self ψ.1
    spectralTraceClass := htraceClass
    spectralTrace_eq_one := by
      rw [htraceClass.trace_eq_spectralTrace]
      exact rankOne_spectralTrace_eq_one ψ.2 }
"""
replace(rel, old, new)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Thermal/QuantumLinkedCluster.lean"
replace(
    rel,
    """  rw [hfilter]
  rfl

/-! ## The occupation projector""",
    """  exact congrArg (fun z : ℂ => z / Common.weightSum w)
    (Finset.sum_congr hfilter (fun _ _ => rfl))

/-! ## The occupation projector""",
)

rel = "LeanCondensedMatter/QuantumTheory/DensityOperator/Purity.lean"
replace(
    rel,
    """      have htrace := ρ.spectralTrace_eq_one
      change (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 at htrace
""",
    """      have htrace := ρ.spectralTrace_op_eq_one
      change (∑' a : EigenvectorIndex ρ.op, a.1.1) = 1 at htrace
""",
)

for rel in [
    "LeanCondensedMatter/QuantumTheory/Gibbs/FreeEnergy.lean",
    "LeanCondensedMatter/QuantumTheory/Gibbs/Uniqueness.lean",
]:
    content = read(rel)
    content = content.replace(
        """  have hq_summable_and_le : Summable q ∧ ∑' a, q a ≤ Z := by
    simpa [Z, hq_def, hGibbs, SpectralTraceClass.trace] using
      hGibbs.sum_diagonalExpectationValue_le_trace
        (gibbsOp_isPositive Hop β).toLinearMap hd_orth
""",
        """  have hq_summable_and_le : Summable q ∧ ∑' a, q a ≤ Z := by
    have hbound := hGibbs.sum_diagonalExpectationValue_le_trace
      (gibbsOp_isPositive Hop β).toLinearMap hd_orth
    rw [hGibbs.trace_eq_spectralTrace] at hbound
    simpa [Z, hq_def] using hbound
""",
        1,
    )
    content = content.replace("have heq := ρ.spectralTrace_eq_one", "have heq := ρ.spectralTrace_op_eq_one")
    content = content.replace("have hpsum := ρ.spectralTrace_eq_one", "have hpsum := ρ.spectralTrace_op_eq_one")
    write(rel, content)

rel = "LeanCondensedMatter/QuantumTheory/POVM/Born.lean"
replace(
    rel,
    "simpa [SpectralTraceClass.trace, spectralTrace] using ρ.spectralTrace_eq_one",
    "simpa [spectralTrace] using ρ.spectralTrace_op_eq_one",
)

print("density trace migration fixes applied")
