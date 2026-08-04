from pathlib import Path

root = Path(".")


def read(rel: str) -> str:
    return (root / rel).read_text()


def write(rel: str, content: str) -> None:
    (root / rel).write_text(content)


def repl(rel: str, old: str, new: str, count: int | None = None) -> None:
    content = read(rel)
    found = content.count(old)
    if found == 0:
        raise SystemExit(f"not found in {rel}: {old[:80]!r}")
    if count is not None and found != count:
        raise SystemExit(f"count {found} != {count} in {rel}")
    write(rel, content.replace(old, new))


rel = "LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/ReassembleDecompose.lean"
content = read(rel)
content = content.replace(
    """      (Subtype.ext (a1 := (⟨vertexOfLeg (legOfVertexLocal v i), hleg0⟩ :
          {x : ↥S // (x : Fin N) ∈ B.1}))""",
    """      (Subtype.ext (a1 := (⟨vertexOfLeg (legOfVertexLocal v i), by
            simpa only [vertexOfLeg_legOfVertexLocal] using hv⟩ :
          {x : ↥S // (x : Fin N) ∈ B.1}))""",
)
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/WickDiagram/ComponentPairProduct.lean"
content = read(rel)
old = """  simpa using
    (orderedQuarticPairValue_componentOrderedLeg
      ε β d orders shuffle τ B pr.1.1 pr.1.2)"""
new = """  rw [d.componentPairEquiv_apply orders shuffle B pr]
  exact orderedQuarticPairValue_componentOrderedLeg
    ε β d orders shuffle τ B pr.1.1 pr.1.2"""
if old not in content:
    raise SystemExit("component pair proof not found")
write(rel, content.replace(old, new, 1))

repl(
    "LeanCondensedMatter/Analysis/Operator/TraceClass/Basic.lean",
    """theorem trace_nonneg {T : H →L[ℂ] H} (h : HasSummableRealEigenvalues T)
    (hpos : (T : H →ₗ[ℂ] H).IsPositive) : 0 ≤ spectralTrace T :=
""",
    """theorem trace_nonneg {T : H →L[ℂ] H}
    (hpos : (T : H →ₗ[ℂ] H).IsPositive) : 0 ≤ spectralTrace T :=
""",
    1,
)
repl(
    "LeanCondensedMatter/QuantumTheory/Gibbs/FreeEnergy.lean",
    "ContinuousLinearMap.trace_nonneg hsummable (gibbsOp_isPositive Hop β).toLinearMap",
    "ContinuousLinearMap.trace_nonneg (gibbsOp_isPositive Hop β).toLinearMap",
    1,
)

rel = "LeanCondensedMatter/Analysis/Operator/TraceClass/Bundled.lean"
content = read(rel)
content = content.replace(
    """noncomputable def trace (h : SpectralTraceClass T) : ℝ :=
  ContinuousLinearMap.spectralTrace T
""",
    """noncomputable def trace (h : SpectralTraceClass T) : ℝ :=
  match h with
  | ⟨_, _, _⟩ => ContinuousLinearMap.spectralTrace T

@[simp]
theorem trace_eq_spectralTrace (h : SpectralTraceClass T) :
    h.trace = ContinuousLinearMap.spectralTrace T := by
  cases h
  rfl
""",
)
content = content.replace(
    "simpa [trace] using ContinuousLinearMap.trace_nonneg h.summable hpos",
    "simpa using ContinuousLinearMap.trace_nonneg hpos",
)
content = content.replace(
    """simpa [trace] using
    ContinuousLinearMap.hasSum_diagonalExpectationValue_eq_spectralTrace""",
    """simpa using
    ContinuousLinearMap.hasSum_diagonalExpectationValue_eq_spectralTrace""",
)
content = content.replace(
    """simpa [trace] using
    ContinuousLinearMap.sum_diagonalExpectationValue_le_spectralTrace""",
    """simpa using
    ContinuousLinearMap.sum_diagonalExpectationValue_le_spectralTrace""",
)
content = content.replace(
    "simpa [trace] using ContinuousLinearMap.spectralTrace_add",
    "simpa using ContinuousLinearMap.spectralTrace_add",
)
content = content.replace(
    "simpa [trace] using ContinuousLinearMap.spectralTrace_comp_comm",
    "simpa using ContinuousLinearMap.spectralTrace_comp_comm",
)
write(rel, content)

rel = "LeanCondensedMatter/QuantumTheory/Postulates.lean"
content = read(rel)
content = content.replace(
    """namespace QuantumTheory

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **State space postulate.""",
    """namespace QuantumTheory

/-- **State space postulate.""",
)
content = content.replace(
    """def Observable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  { A : H →L[ℂ] H // IsSelfAdjoint A }

variable (A : Observable H) (ψ : State H)
""",
    """def Observable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  { A : H →L[ℂ] H // IsSelfAdjoint A }

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : Observable H) (ψ : State H)
""",
)
write(rel, content)

for rel in [
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/FockSpace.lean",
    "LeanCondensedMatter/SecondQuantization/Fermionic/Algebra/FockSpace.lean",
]:
    content = read(rel)
    content = content.replace("\nvariable {Mode : Type*}\n\n/-- ", "\n/-- ", 1)
    marker = "  Common.AlgebraicFock (Occupation Mode)\n"
    if marker not in content:
        raise SystemExit(f"alias marker missing {rel}")
    content = content.replace(marker, marker + "\nvariable {Mode : Type*}\n", 1)
    write(rel, content)

rel = "LeanCondensedMatter/Combinatorics/PerfectPairing/EraseZero.lean"
content = read(rel)
content = content.replace(
    """def Pairing.restrictedPartnerMap {n : ℕ} (pairing : Pairing (n + 1))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0)
    (x : deletedPositions n (pairing.partner 0)) :""",
    """def Pairing.restrictedPartnerMap {n : ℕ} (pairing : Pairing (n + 1))
    (x : deletedPositions n (pairing.partner 0)) :""",
)
content = content.replace(
    """def Pairing.restrictedPartner {n : ℕ} (pairing : Pairing (n + 1))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0) :
""",
    """def Pairing.restrictedPartner {n : ℕ} (pairing : Pairing (n + 1)) :
""",
)
content = content.replace("pairing.restrictedPartnerMap hzero", "pairing.restrictedPartnerMap")
content = content.replace(
    """theorem Pairing.restrictedPartner_partner_partner {n : ℕ} (pairing : Pairing (n + 1))
    (hzero : (0 : Fin (2 * (n + 1))) ≠ pairing.partner 0)
    (x : deletedPositions n (pairing.partner 0)) :
    pairing.restrictedPartner hzero (pairing.restrictedPartner hzero x) = x := by""",
    """theorem Pairing.restrictedPartner_partner_partner {n : ℕ} (pairing : Pairing (n + 1))
    (x : deletedPositions n (pairing.partner 0)) :
    pairing.restrictedPartner (pairing.restrictedPartner x) = x := by""",
)
content = content.replace("let r := pairing.restrictedPartner hzero", "let r := pairing.restrictedPartner")
content = content.replace(
    "e.symm (pairing.restrictedPartner hzero (e i))",
    "e.symm (pairing.restrictedPartner (e i))",
)
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/ComponentRestriction.lean"
content = read(rel)
content = content.replace(
    """theorem QuarticDiagram.legInBlock_partner_iff {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) (leg : Fin (2 * (2 * S.card))) :""",
    """theorem QuarticDiagram.legInBlock_partner_iff {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (leg : Fin (2 * (2 * S.card))) :""",
)
content = content.replace(
    """noncomputable def QuarticDiagram.restrictedPartner {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :""",
    """noncomputable def QuarticDiagram.restrictedPartner {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N)) :""",
)
content = content.replace(
    "(d.legInBlock_partner_iff hB leg).symm",
    "(d.legInBlock_partner_iff leg).symm",
)
content = content.replace(
    """theorem QuarticDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPartner hB leg : Fin (2 * (2 * S.card)))""",
    """theorem QuarticDiagram.restrictedPartner_val {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N))
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    (d.restrictedPartner B leg : Fin (2 * (2 * S.card)))""",
)
content = content.replace(
    """theorem QuarticDiagram.restrictedPartner_involutive {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts) :
    Function.Involutive (d.restrictedPartner hB)""",
    """theorem QuarticDiagram.restrictedPartner_involutive {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N)) :
    Function.Involutive (d.restrictedPartner B)""",
)
content = content.replace(
    """theorem QuarticDiagram.restrictedPartner_ne_self {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) {B : Finset (Fin N)}
    (hB : B ∈ d.componentPartition.parts)
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    d.restrictedPartner hB leg ≠ leg := fun h =>
  d.pairing.partner_ne_self leg (by rw [← d.restrictedPartner_val hB, h])""",
    """theorem QuarticDiagram.restrictedPartner_ne_self {S : Finset (Fin N)}
    (d : QuarticDiagram Label N S) (B : Finset (Fin N))
    (leg : {leg : Fin (2 * (2 * S.card)) // d.legInBlock B leg}) :
    d.restrictedPartner B leg ≠ leg := fun h =>
  d.pairing.partner_ne_self leg (by rw [← d.restrictedPartner_val B, h])""",
)
content = content.replace(
    "(d.blockLegEquiv hB).permCongr (d.restrictedPartner hB)",
    "(d.blockLegEquiv hB).permCongr (d.restrictedPartner B)",
)
content = content.replace("(d.restrictedPartner_involutive hB)", "(d.restrictedPartner_involutive B)")
content = content.replace("(d.restrictedPartner_ne_self hB)", "(d.restrictedPartner_ne_self B)")
content = content.replace(
    "d.blockLegEquiv hB (d.restrictedPartner hB leg)",
    "d.blockLegEquiv hB (d.restrictedPartner B leg)",
)
write(rel, content)

for rel in [
    "LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/ComponentConnected.lean",
    "LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/ReassembleDecompose.lean",
]:
    content = read(rel)
    content = content.replace("d.restrictedPartner hB ", "d.restrictedPartner B ")
    content = content.replace("d.restrictedPartner B.2 ", "d.restrictedPartner B.1 ")
    write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/ReassembleRestrictComponent.lean"
content = read(rel).replace(
    "(QuarticDiagram.reassemble π F).restrictedPartner_val,",
    "(QuarticDiagram.reassemble π F).restrictedPartner_val B,",
)
write(rel, content)

for path in (root / "LeanCondensedMatter/SecondQuantization/Fermionic").rglob("*.lean"):
    content = path.read_text()
    content = content.replace("[DecidableEq Mode] [LinearOrder Mode]", "[LinearOrder Mode]")
    content = content.replace(
        "omit [DecidableEq Mode] [LinearOrder Mode] [Fintype Mode] in",
        "omit [LinearOrder Mode] [Fintype Mode] in",
    )
    content = content.replace(
        "omit [DecidableEq Mode] [LinearOrder Mode] in",
        "omit [LinearOrder Mode] in",
    )
    content = content.replace(
        "omit [DecidableEq Mode] [Fintype Mode] [LinearOrder Mode] in",
        "omit [Fintype Mode] [LinearOrder Mode] in",
    )
    content = content.replace(
        "omit [DecidableEq Mode] [Fintype Mode] in",
        "omit [Fintype Mode] in",
    )
    content = content.replace("omit [DecidableEq Mode] in", "")
    path.write_text(content)

for rel in [
    "LeanCondensedMatter/SecondQuantization/Bosonic/Algebra/NumberOperator.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/ParticleNumberWeightSummable.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/FreeTwoPointCoefficient.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/ImaginaryTime/ImaginaryTimeEvolution.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Thermal/BoltzmannWeightFactorization.lean",
    "LeanCondensedMatter/SecondQuantization/Bosonic/Diagrammatics/QuarticInteraction.lean",
]:
    content = read(rel)
    content = content.replace(" [DecidableEq Mode]", "")
    content = content.replace("[DecidableEq Mode] ", "")
    content = content.replace("omit [DecidableEq Mode] in", "")
    write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Common/Diagrammatics/ReassembleDecompose.lean"
content = read(rel).replace(
    "(d.legInBlock_partner_iff B.2 (legOfVertexLocal v i)).mp hleg0",
    "(d.legInBlock_partner_iff (B := B.1) (legOfVertexLocal v i)).mp hleg0",
)
write(rel, content)

rel = "LeanCondensedMatter/SecondQuantization/Fermionic/Diagrammatics/WickDiagram/ComponentPairing.lean"
content = read(rel).replace(
    "d.restrictedPartner B.2 leg",
    "d.restrictedPartner (B : Finset (Fin N)) leg",
)
content = content.replace(
    "d.restrictedPartner_val B.2",
    "d.restrictedPartner_val (B : Finset (Fin N))",
)
write(rel, content)

print("lint cleanup fix batch applied")
