import LeanCondensedMatter.SecondQuantization.Fermionic.WickDiagram.Reassemble

set_option linter.style.header false

/-!
# Bridge lemmas towards `reassemble (decompose d) = d`

Per review: unfolding `bigLegEquiv`/`sigmaProdDistrib`/`sigmaCongrRight`/`equivSigmaParts`/
`blockLegEquiv`/`subtypeMemBlockEquiv` together at the point of use is unworkable. This file fixes
the two facts every later step should build on instead:

- `QuarticWickDiagram.componentPartition_part`: `d.componentPartition.part` agrees with
  `componentBlock`.
- `QuarticWickDiagram.bigLegEquiv_legOfVertexLocal`: `bigLegEquiv`'s value at a leg built from a
  vertex and local leg, in terms of `Finpartition.equivSigmaParts` alone.

The remaining bridge (`bigLegEquiv` agrees with `blockLegEquiv` on a fixed block, as a genuine
dependent-`Sigma` equality) and the `reassemble (decompose d) = d` direction itself are deferred:
that step needs the componentPartition-block's `Finset` equality substituted through before the
leg-level equality can be stated non-dependently, and is significant further work.
-/

namespace SecondQuantization

variable {Mode : Type*} {N : ℕ}

/-- **`d.componentPartition.part` agrees with `componentBlock`.** -/
theorem QuarticWickDiagram.componentPartition_part {S : Finset (Fin N)}
    (d : QuarticWickDiagram Mode N S) (v : ↥S) :
    d.componentPartition.part (v : Fin N) = d.componentBlock v :=
  d.componentPartition.part_eq_of_mem (d.componentBlock_mem_componentPartition v)
    (d.self_mem_componentBlock v)

/-- **`bigLegEquiv`'s value at a leg built from a vertex and local leg.** Once this is known,
`bigLegEquiv` itself never needs to be unfolded again. -/
theorem QuarticWickDiagram.bigLegEquiv_legOfVertexLocal {S : Finset (Fin N)} (π : Finpartition S)
    (v : ↥S) (i : Fin 4) :
    QuarticWickDiagram.bigLegEquiv π (legOfVertexLocal v i) =
      ⟨(π.equivSigmaParts v).1, legOfVertexLocal (π.equivSigmaParts v).2 i⟩ := by
  have hqv : quarticLegEquiv S (legOfVertexLocal v i) = (v, i) :=
    Equiv.apply_symm_apply (quarticLegEquiv S) (v, i)
  simp only [QuarticWickDiagram.bigLegEquiv, Equiv.trans_apply, hqv, Equiv.prodCongr_apply,
    Equiv.sigmaProdDistrib_apply, Equiv.sigmaCongrRight_apply]
  rfl

end SecondQuantization
