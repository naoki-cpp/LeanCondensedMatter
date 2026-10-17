# Declaration Explorer vocabulary

The Declaration Explorer presents the project's compiled Lean declarations and their dependency graph. Lean remains the authority for declaration meaning; the math view is a readable rendering of Lean's pretty-printed expression.

**Statement**:
The type of a declaration. For a theorem, this is its proposition; for a definition, it is the declared type. The Explorer shows it in the selected declaration's detail panel.

**Math view**:
A best-effort display of a Lean pretty-printed expression as a mathematical formula. The rendering maps a supported set of Lean notation to mathematical symbols without changing the stored Lean expression. Unsupported syntax, or an unavailable formula renderer, is shown in Lean notation instead.

**Lean notation**:
The Lean text kept with a formula. Statements use Lean's pretty-printed type; definition bodies retain the original source expression.

**Definition body**:
The source body of a source-backed definition or abbreviation. The Explorer reads it from the public Lean source only when its collapsed disclosure is opened, then applies the same math view and Lean-notation fallback as for statements. Equation-style declarations that cannot be isolated are shown as Lean source.

**Opaque declaration**:
A declaration whose value is intentionally not exposed by the Explorer. Its type is shown as a statement; no body is read or published.

