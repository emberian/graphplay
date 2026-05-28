# Search Compiler Report: hypercube Q3 template with equal fibers

## Host

- template vertices: 8
- host vertices: 96
- weighted host edge mass: 1728
- fibers: {'000': 12, '001': 12, '010': 12, '011': 12, '100': 12, '101': 12, '110': 12, '111': 12}
- marked counts: {'000': 1, '001': 0, '010': 0, '011': 0, '100': 0, '101': 0, '110': 0, '111': 0}

## Template Diagnostics

- weighted degrees: 3, 3, 3, 3, 3, 3, 3, 3
- regular template: True
- template adjacency eigenvalues: -3, -1, -1, -1, 1, 1, 1, 3
- CNO spectral ratio max(|lambda_i|)/lambda_1: 1
- CNO ratio passes strict < 1 check: False
- template Laplacian eigenvalues: 7.77156e-16, 2, 2, 2, 4, 4, 4, 6
- template Laplacian integral: True

## Fiber Quotient

- host weighted degrees by fiber: 36, 36, 36, 36, 36, 36, 36, 36
- regular host: True
- host quotient spectral ratio: 1
- quotient adjacency eigenvalues: -36, -12, -12, -12, 12, 12, 12, 36
- quotient Laplacian eigenvalues: 1.68043e-14, 24, 24, 24, 48, 48, 48, 72
- full host Laplacian integral: True
- full host Laplacian eigenvalues: 1.68043e-14, 24, 24, 24, 36, 36, 36, 36, 36, ..., 36, 36, 36, 36, 36, 48, 48, 48, 72

Adjacency quotient on uniform fiber states:

```text
                000       001       010       011       100       101       110       111
      000         0        12        12         0        12         0         0         0
      001        12         0         0        12         0        12         0         0
      010        12         0         0        12         0         0        12         0
      011         0        12        12         0         0         0         0        12
      100        12         0         0         0         0        12        12         0
      101         0        12         0         0        12         0         0        12
      110         0         0        12         0        12         0         0        12
      111         0         0         0        12         0        12        12         0
```

## Marked Quotient

- cells: {'000:M': 1, '000:U': 11, '001:U': 12, '010:U': 12, '011:U': 12, '100:U': 12, '101:U': 12, '110:U': 12, '111:U': 12}
- gamma factors searched: [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
- adjacency gamma: 0.027777778
- laplacian gamma: 0.11111111
- scan horizon: [0, 48.9898] with 2200 steps
- best adjacency-CTQW marked probability: 0.986847 at t=46.4278
- best laplacian-CTQW marked probability: 0.0104167 at t=0

Marked-cell adjacency quotient:

```text
              000:M     000:U     001:U     010:U     011:U     100:U     101:U     110:U     111:U
    000:M         0         0     3.464     3.464         0     3.464         0         0         0
    000:U         0         0     11.49     11.49         0     11.49         0         0         0
    001:U     3.464     11.49         0         0        12         0        12         0         0
    010:U     3.464     11.49         0         0        12         0         0        12         0
    011:U         0         0        12        12         0         0         0         0        12
    100:U     3.464     11.49         0         0         0         0        12        12         0
    101:U         0         0        12         0         0        12         0         0        12
    110:U         0         0         0        12         0        12         0         0        12
    111:U         0         0         0         0        12         0        12        12         0
```

Marked-cell adjacency search Hamiltonian:

```text
              000:M     000:U     001:U     010:U     011:U     100:U     101:U     110:U     111:U
    000:M        -1        -0  -0.09623  -0.09623        -0  -0.09623        -0        -0        -0
    000:U        -0        -0   -0.3191   -0.3191        -0   -0.3191        -0        -0        -0
    001:U  -0.09623   -0.3191        -0        -0   -0.3333        -0   -0.3333        -0        -0
    010:U  -0.09623   -0.3191        -0        -0   -0.3333        -0        -0   -0.3333        -0
    011:U        -0        -0   -0.3333   -0.3333        -0        -0        -0        -0   -0.3333
    100:U  -0.09623   -0.3191        -0        -0        -0        -0   -0.3333   -0.3333        -0
    101:U        -0        -0   -0.3333        -0        -0   -0.3333        -0        -0   -0.3333
    110:U        -0        -0        -0   -0.3333        -0   -0.3333        -0        -0   -0.3333
    111:U        -0        -0        -0        -0   -0.3333        -0   -0.3333   -0.3333        -0
```

