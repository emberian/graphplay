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

Build the Lean artifact:

```sh
lake build
```

Build the note:

```sh
typst compile paper/quasi_infinite_adjoint.typ paper/quasi_infinite_adjoint.pdf
```

Fetched paper PDFs and extracted text live in `references/`.
