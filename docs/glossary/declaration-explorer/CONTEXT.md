# Declaration Explorer vocabulary

The Declaration Explorer presents the project's compiled Lean declarations and their dependency graph. Lean remains the authority for declaration meaning; the math view is a readable rendering of Lean's pretty-printed expression.

**Statement**:
The type of a declaration. For a theorem, this is its proposition; for a definition, it is the declared type. The Explorer shows it in the selected declaration's detail panel.

**Structured statement**:
A versioned catalog record derived from Lean's elaborated declaration type. It separates outer binders into type parameters, variables, proposition assumptions, and typeclass instances, and records the remaining conclusion or result type. Application nodes preserve full constant names and explicit arguments. Structure records also include field types for a value named `self`. No theorem proof or opaque body is exported by this presentation record.

The Explorer uses the record to display settings, variables, assumptions, and the conclusion separately. Universe levels and outer implicit binders remain in the original Lean statement disclosure. Application nodes omit implicit arguments, following the usual Lean pretty-printing convention. Names may be shortened for display; colliding names remain qualified, and a symbol key records the full names. Missing or unsupported structured data uses the existing Lean presentation.

**Setting summary**:
A shared display rule for recognized assumptions. The initial rule describes a type as a complex Hilbert space only when `NormedAddCommGroup`, `InnerProductSpace` over `Complex`, and `CompleteSpace` refer to that type and the latter two obtain their instance arguments through structure projections from the same normed-group binder. Merely mentioning that binder is insufficient. The underlying typeclass assumptions remain available in a disclosure. Unrecognized or unmatched assumptions stay visible individually; a declaration's name never supplies mathematical assumptions.

**Typed inclusion**:
The displayed map `ι : ℝ ↪ ℂ` for `Complex.ofReal` when its elaborated argument and result types are `Real` and `Complex`. A generic `Coe` application is insufficient: a custom instance need not be this inclusion. Other applications retain their declared names or Lean text. This rule does not infer a coercion's meaning from the `↑` character.

Structured records become available after the declaration catalog is regenerated and published to the `graph-data` branch. Existing catalog data continues to display Lean expressions until then.

**Math view**:
A best-effort display of a Lean pretty-printed expression as a mathematical formula. The rendering maps a supported set of Lean notation to mathematical symbols without changing the stored Lean expression. Unsupported syntax, or an unavailable formula renderer, is shown in Lean notation instead.

**Lean notation**:
The Lean text kept with a formula. Statements use Lean's pretty-printed type; definition bodies retain the original source expression.

**Definition body**:
The source body of a source-backed definition or abbreviation. The Explorer reads it from the public Lean source only when its collapsed disclosure is opened, then applies the same math view and Lean-notation fallback as for statements. Equation-style declarations that cannot be isolated are shown as Lean source.

**Opaque declaration**:
A declaration whose value is intentionally not exposed by the Explorer. Its type is shown as a statement; no body is read or published.

