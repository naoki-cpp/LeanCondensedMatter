---
status: accepted
---

# Assign modules by semantic responsibility

Reusable mathematics belongs in Analysis or Combinatorics, quantum-state and response foundations in QuantumTheory, and second-quantized constructions in SecondQuantization. Within SecondQuantization, Common owns statistics-independent many-body constructions; Fermionic and Bosonic own their statistics-specific realizations.

This keeps a proof's first application from becoming the permanent owner of general theory. Upstream mathematics and QuantumTheory do not import SecondQuantization, and Common does not import either statistics-specific layer. Fermionic Algebra feeds the sibling Field and Lattice realizations, which feed Transport and terminal Validation consumers.

The trade-off is explicit adapters at representation boundaries instead of direct access to downstream conveniences. Move reusable results to the earliest layer that owns their meaning, and use canonical general declarations directly; do not preserve forwarding modules or specialized aliases merely for historical compatibility.

Evidence: [layer graph](../../scripts/architecture/second_quantization.json), [second-quantization architecture](../../notes/architecture/second-quantization.md), and [conventions](../../notes/conventions.md).
