from pathlib import Path

root = Path(".")


def read(rel: str) -> str:
    return (root / rel).read_text()


def write(rel: str, content: str) -> None:
    (root / rel).write_text(content)


instance_names = {
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CreationAnnihilation.lean":
        "instDecidableEqCreationAnnihilation",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/CCR.lean":
        "instDecidableEqCCR",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/ExchangeAlgebra.lean":
        "instDecidableEqExchangeAlgebra",
    "LeanCondensedMatter/SecondQuantization/Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean":
        "instDecidableEqImaginaryTimeEvolution",
}
for rel, name in instance_names.items():
    content = read(rel)
    old = "local instance : DecidableEq Mode := Classical.decEq Mode"
    if old not in content:
        raise SystemExit(f"unnamed local instance missing in {rel}")
    write(rel, content.replace(
        old, f"local instance {name} : DecidableEq Mode := Classical.decEq Mode", 1))

rel = "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/NumberOperator.lean"
content = read(rel)
content = content.replace(
    "namespace Bosonic\n\nvariable {Mode : Type*}",
    "namespace Bosonic\n\nnoncomputable section\n\nvariable {Mode : Type*}\n\n"
    "local instance instDecidableEqNumberOperator : DecidableEq Mode := Classical.decEq Mode",
    1,
)
content = content.replace(
    "\nend Bosonic\nend SecondQuantization",
    "\nend\n\nend Bosonic\nend SecondQuantization",
    1,
)
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/BoltzmannWeightFactorization.lean"
content = read(rel)
content = content.replace(
    "namespace Bosonic\n\nvariable {Mode : Type*}",
    "namespace Bosonic\n\nnoncomputable section\n\nvariable {Mode : Type*}\n\n"
    "local instance instDecidableEqBoltzmannWeightFactorization : DecidableEq Mode := "
    "Classical.decEq Mode",
    1,
)
content = content.replace("\nomit in\n", "\n")
content = content.replace(
    "\nend Bosonic\nend SecondQuantization",
    "\nend\n\nend Bosonic\nend SecondQuantization",
    1,
)
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Thermal/QuantumLinkedCluster.lean"
content = read(rel)
content = content.replace(
    "variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode]",
    "noncomputable section\n\nvariable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]\n\n"
    "local instance instDecidableEqQuantumLinkedCluster : DecidableEq Mode := Classical.decEq Mode",
    1,
)
content = content.replace(
    """  have hfilter : (Finset.univ : Finset (Occupation Mode)).filter
      (({i} : Finset Mode) ⊆ ·) = (Finset.univ : Finset (Occupation Mode)).filter
      (i ∈ ·) := by
    ext n; simp [Finset.subset_iff]
  exact congrArg (fun z : ℂ => z / Common.weightSum w)
    (Finset.sum_congr hfilter (fun _ _ => rfl))""",
    """  congr 1
  apply Finset.sum_congr
  · ext n
    simp [Finset.subset_iff]
  · intro n hn
    rfl""",
    1,
)
content = content.replace(
    "\nend Fermionic\nend SecondQuantization",
    "\nend\n\nend Fermionic\nend SecondQuantization",
    1,
)
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Thermal/FreeEntropy.lean"
content = read(rel)
content = content.replace(
    "variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]",
    "variable {Mode : Type*} [LinearOrder Mode] [Fintype Mode]\n\n"
    "local instance instDecidableEqFreeEntropy : DecidableEq Mode := Classical.decEq Mode",
    1,
)
write(rel, content)

rel = "LeanCondensedMatter/QuantumTheory/Gibbs/FreeEnergy.lean"
content = read(rel)
content = content.replace(
    """theorem spectralTrace_gibbsOp_pos (Hop : Observable H) (β : ℝ)
    (hsummable : HasSummableRealEigenvalues (gibbsOp Hop β))
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :""",
    """theorem spectralTrace_gibbsOp_pos (Hop : Observable H) (β : ℝ)
    (hZ : spectralTrace (gibbsOp Hop β) ≠ 0) :""",
    1,
)
content = content.replace(
    "spectralTrace_gibbsOp_pos Hop β hsummable hZ",
    "spectralTrace_gibbsOp_pos Hop β hZ",
)
write(rel, content)
for rel in [
    "LeanCondensedMatter/QuantumTheory/Gibbs/Variational.lean",
    "LeanCondensedMatter/QuantumTheory/Gibbs/Uniqueness.lean",
]:
    content = read(rel).replace(
        "spectralTrace_gibbsOp_pos Hop β hsummable hZ",
        "spectralTrace_gibbsOp_pos Hop β hZ",
    )
    write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Perturbation/DysonVertexMoment.lean"
content = read(rel)
content = content.replace(
    "{α : Type*} [DecidableEq α] (ε : Mode → ℝ) (β : ℝ)",
    "{α : Type*} (ε : Mode → ℝ) (β : ℝ)",
    2,
)
content = content.replace(
    """    dysonVertexMoment ε β V (∅ : Finset α) = 1 := by
  simp [dysonVertexMoment]""",
    """    dysonVertexMoment ε β V (∅ : Finset α) = 1 := by
  classical
  simp [dysonVertexMoment]""",
    1,
)
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/DysonDiagramExpansion/Pairing.lean"
content = read(rel)
content = content.replace(
    """theorem dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairing {α : Type*}
    [DecidableEq α] (ε : Mode → ℝ)""",
    """theorem dysonVertexMoment_quarticInteraction_eq_sum_vertexLabel_pairing {α : Type*}
    (ε : Mode → ℝ)""",
    1,
)
content = content.replace(
    """                        (quarticLegOperatorForSequence ε q τ pr.2)))) := by
  have hkey :=
""",
    """                        (quarticLegOperatorForSequence ε q τ pr.2)))) := by
  classical
  have hkey :=
""",
    1,
)
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/TwoPointDiagramExpansion/Flattening.lean"
content = read(rel).replace(
    "variable {Mode : Type*} [DecidableEq Mode] [LinearOrder Mode]",
    "variable {Mode : Type*} [LinearOrder Mode]",
    1,
)
write(rel, content)

print("final typeclass and unused-argument cleanup applied")
