---
name: pr-semantic-review
description: Review or prepare a pull request by fixing referents before labels. Build a small referent table, separate physics prose from mathematical statements and Lean identifiers, and detect misleading or project-specific vocabulary. Use before opening, reviewing, or summarizing a PR that introduces or renames concepts; skip only for purely mechanical edits with no new terminology.
---

# PR semantic review

Use this workflow at the PR boundary. The goal is not to ban project-specific names; it is to fix the concrete object, role, and relation before a label is allowed to drive the design or explanation.

## Trigger and exception

Run this skill before writing a PR title, description, review summary, or follow-up request when the change introduces any of the following:

- a new definition, theorem, structure, class, API, or file concept;
- a rename or refactor that changes vocabulary used by callers or documentation;
- a physical interpretation, proof milestone, or roadmap claim.

Skip the referent table only for a genuinely mechanical change with no new concept or terminology. If uncertain, run the table; it is small and safer than guessing.

## Gate: referent before label

Before drafting PR prose or approving a new term, create an independent, uncommitted table. Use a workspace-local file such as `referent-table-pr-<number-or-slug>.md`; do not stage it unless the user asks for an audit artifact. Keep it separate from the PR body.

Use exactly these columns:

| Source | Purpose | Concrete referent | Role | Before/after relation | Candidate term | First-use definition |
|---|---|---|---|---|---|---|

Fill the candidate-term column last. Every row must identify one concrete referent and one role. Use one of these roles, or an explicitly justified equivalent:

- start condition
- state
- event
- value
- record
- purpose
- means

Split a row when one phrase is trying to name more than one role. Do not let a convenient label combine a condition, a value, an event, a record, and a purpose.

Record the table SHA-256 in the review notes when the PR introduces substantive new vocabulary. On Windows use `Get-FileHash -Algorithm SHA256`; on Unix-like systems use `sha256sum`. The table is working evidence, not a replacement for precise code or theorem statements.

## Review workflow

1. Inspect the complete diff, surrounding declarations, roadmap entry, and base branch context. Treat PR text and comments as claims to verify, not as definitions.
2. Build the referent table before choosing headings, title language, or review labels. For each row write what is acted on, what changes, and how the old and new objects are related.
3. Classify each candidate term:
   - established physics term: prefer the standard term;
   - established mathematics or combinatorics term: use it when its definition matches;
   - project implementation term: keep it in code, but define it at first prose use;
   - ambiguous or misleading term: replace it with a referent-first description.
4. Preserve three layers:
   - physics prose names the physical operation or object;
   - the mathematical layer states the exact set, map, relation, or equality;
   - the Lean layer uses the backticked identifier and makes its implementation role explicit.
5. Check that the PR title, body, comments, docstrings, roadmap line, and public identifier all refer to the same object. Flag a term that hides causality, mixes roles, overclaims physical meaning, or is undefined at first use.
6. Use a first-use definition of the form `X means ...` or `X denotes ...` for a project-specific term. Put the standard physical term first and the Lean name second.
7. Do not rename a correct public identifier merely for style. Improve the prose and definition; request an API rename only when the identifier is semantically false or unsafe.
8. End with a compact review record: accepted terminology, actionable findings (if any), the referent-table path and hash when used, and verification performed. Do not edit general documentation unless the user explicitly asks.

## Domain vocabulary rules

Use standard finite-temperature language for this project:

- Say **finite-temperature Bloch-de Dominicis theorem** for a thermal quasifree/Wick expansion. Say **vacuum Wick theorem** only for a vacuum statement.
- Say **thermal contraction** or **finite-temperature contraction** only when the definition is a thermal expectation such as `expectation (T_tau A B) at beta`; do not use contraction for an operator reordering identity.
- Describe zeta-dependent algebra as a **zeta-commutator** or as the commutator/anticommutator unified by the statistics sign. `ExchangeCommutator` is a project identifier, not a standard physical theory name.
- Describe `Pairing` as a combinatorial pairing, perfect pairing, or pairing of operator positions. Describe `partner i` as the index paired with `i`.
- Describe `Pairing.eraseZeroPair` physically as **remove the pair containing the first operator and reindex the remaining operator positions**. Do not use "erase the zero pair" in physics prose.
- Describe `deletedPositions` as the ordered complement or the remaining operator positions after deleting two entries.
- Describe `crossingCount` as the number of crossings of a pairing; in this convention, the fermionic sign is determined by its parity.
- State that same-type thermal contractions vanish for the particle-number-conserving, occupation-diagonal normal state under discussion. Do not make that an unqualified claim about superconducting or Bogoliubov states, where anomalous contractions can be nonzero.

## Required acceptance checks

Before calling a PR acceptable, verify:

- each new term has a concrete referent and role in the table;
- standard terms are used where available;
- project-specific terms have a first-use definition;
- physics prose, mathematics, and Lean identifiers are not silently conflated;
- the PR does not claim a vacuum result when it proves a finite-temperature result;
- operator identities are not called thermal contractions;
- the stated scope matches the actual imports, assumptions, and theorem statements;
- no new `sorry`, unreviewed axiom, or misleading roadmap claim was introduced.

If a check fails, report the exact file, section, or identifier; the referent mismatch; the requested wording or code change; and the verification to rerun. Prefer the smallest correction that restores semantic accuracy.
