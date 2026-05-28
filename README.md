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
- a prototype search-problem compiler for engineered template joins.

Build the Lean artifact:

```sh
lake build
```

Build the note:

```sh
typst compile paper/quasi_infinite_adjoint.typ paper/quasi_infinite_adjoint.pdf
```

Run the compiler on an example:

```sh
python3 tools/search_compiler.py examples/rook_3x3_equal_fiber.json \
  --report reports/rook_3x3_equal_fiber.md
```

Run all examples:

```sh
for f in examples/*.json; do
  b=$(basename "$f" .json)
  python3 tools/search_compiler.py "$f" --report "reports/$b.md" >/dev/null
done
```

Template constructors currently supported by the compiler:

- `explicit`
- `complete`
- `cycle`
- `path`
- `complete_bipartite`
- `hypercube`
- `complement`
- `cartesian_product`
- `surface_heawood`
- `cycle_power_law`

Fetched paper PDFs and extracted text live in `references/`.
