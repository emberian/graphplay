# graphplay

Lean 4 formalization of a conservative but nontrivial reading of the
"quasi-infinite adjoint" graph construction:

- arbitrary indexed coproducts of simple graphs;
- heterogeneous and shared-palette color propagation;
- countable edge-union graphs with a hom universal property;
- inverse-limit thread graphs with coordinate projections;
- a formal obstruction to a naive reflector into `C`-colorable graphs.
- a four-color completion lemma connecting planar colorings to complete
  multipartite search host graphs.
- a complete cross-bag join construction, maximal among graphs colored by the
  bag tag projection.
- engineered template pullbacks and simultaneous multicolor constraints.
- engineered template joins, where a small quotient graph programs the allowed
  complete cross-fiber couplings.
- a bounded-dimensional equitable quotient argument for search Hamiltonians on
  the four-color completion.

Build the Lean artifact:

```sh
lake build
```

Build the note:

```sh
typst compile paper/quasi_infinite_adjoint.typ paper/quasi_infinite_adjoint.pdf
```

Fetched paper PDFs and extracted text live in `references/`.
