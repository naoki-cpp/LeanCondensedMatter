# Declarative architecture graphs

Files in this directory are architecture **specifications**, not checker implementations.

The goal is to describe a repository boundary by naming graph vertices and edges once, then let the
Python pre-build audit and Lean post-build audit interpret the same data at their respective levels.

## Layer graph

Each layer declares:

- `id`: stable graph vertex name;
- `modulePrefixes`: Lean modules classified into that vertex;
- `namespacePrefixes`: compiled declaration namespaces allowed for modules in that vertex;
- `forbiddenNameFragments`: semantic declaration-name fragments forbidden in that layer.

Edges are oriented **upstream -> downstream**. A direct source import from layer `A` to layer `B` is
valid exactly when `A = B` or `B` is an ancestor of `A` in the graph. The checker computes graph
reachability, so transitive dependencies do not need to be repeated as extra edges.

For `second_quantization.json`, the intended shape is:

```text
math ───────→ quantumTheory
  └─────────→ common ←──── quantumTheory
                 ├────→ fermionic
                 └────→ bosonic
```

Consequences follow from the graph rather than separate blacklists:

- `Common` cannot import `Fermionic` or `Bosonic`;
- `Analysis` / `Combinatorics` / `QuantumTheory` cannot import SecondQuantization layers downstream;
- `Fermionic` and `Bosonic` cannot import each other;
- both statistics-specific layers may consume `Common` and its upstream ancestors.

## One specification, two interpreters

Python owns source topology. It classifies source and imported modules through `modulePrefixes` and
checks direct imports against graph ancestry before the Lean build.

Lean owns compiled semantics. It reads the same JSON after the build, resolves each source-declared
constant to its compiled owner module, converts private names back with `privateToUserName`, and
checks the layer's `namespacePrefixes` and `forbiddenNameFragments`.

This deliberately avoids teaching Python how to parse Lean `namespace`, `section`, `end`, declaration
modifiers, or private-name syntax.

## Exceptions

`namespaceExceptions` are for small, intentional semantic crossings that cannot be represented by a
layer namespace alone. They are matched by compiled owner-module prefix plus user-facing declaration
prefix.

Keep this list small. An exception should describe a real architectural choice, not preserve an old
source location after a refactor.

The current SecondQuantization graph has one such exception: the combinatorial
`Combinatorics.Pairing.weight` declaration is implemented in the Common thermal tree while remaining
owned by the `Combinatorics` namespace.
