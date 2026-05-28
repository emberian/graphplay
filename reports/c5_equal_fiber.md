# Search Compiler Report: cycle C5 engineered template with equal fibers

## Problem

- domain: minimal cyclic mode fabric
- task: locate a marked mode in a five-sector cyclic host
- encoding: each sector is a fiber and the quotient only couples neighboring sectors
- compiler goal: small non-complete engineered template sanity check
- proof route: regular equal-fiber template passes the adjacency spectral-ratio route

## Host

- template vertices: 5
- host vertices: 100
- weighted host edge mass: 2000
- fibers: {'0': 20, '1': 20, '2': 20, '3': 20, '4': 20}
- marked counts: {'0': 1, '1': 0, '2': 0, '3': 0, '4': 0}

## Template Diagnostics

- weighted degrees: 2, 2, 2, 2, 2
- regular template: True
- template adjacency eigenvalues: -1.61803, -1.61803, 0.618034, 0.618034, 2
- CNO spectral ratio max(|lambda_i|)/lambda_1: 0.809017
- CNO ratio passes strict < 1 check: True
- template Laplacian eigenvalues: 8.32667e-17, 1.38197, 1.38197, 3.61803, 3.61803
- template Laplacian integral: False

## Fiber Quotient

- host weighted degrees by fiber: 40, 40, 40, 40, 40
- regular host: True
- host quotient spectral ratio: 0.809017
- quotient adjacency eigenvalues: -32.3607, -32.3607, 12.3607, 12.3607, 40
- quotient Laplacian eigenvalues: -7.97522e-15, 27.6393, 27.6393, 72.3607, 72.3607
- full host Laplacian integral: False
- full host Laplacian eigenvalues: -7.97522e-15, 27.6393, 27.6393, 40, 40, 40, 40, 40, 40, ..., 40, 40, 40, 40, 40, 40, 40, 72.3607, 72.3607

Adjacency quotient on uniform fiber states:

```text
                  0         1         2         3         4
        0         0        20         0         0        20
        1        20         0        20         0         0
        2         0        20         0        20         0
        3         0         0        20         0        20
        4        20         0         0        20         0
```

## Marked Quotient

- cells: {'0:M': 1, '0:U': 19, '1:U': 20, '2:U': 20, '3:U': 20, '4:U': 20}
- gamma factors searched: [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
- adjacency gamma: 0.025
- laplacian gamma: 0.05527864
- scan horizon: [0, 50] with 2400 steps
- best adjacency-CTQW marked probability: 0.990817 at t=47.3739
- best laplacian-CTQW marked probability: 0.01 at t=0

Marked-cell adjacency quotient:

```text
                0:M       0:U       1:U       2:U       3:U       4:U
      0:M         0         0     4.472         0         0     4.472
      0:U         0         0     19.49         0         0     19.49
      1:U     4.472     19.49         0        20         0         0
      2:U         0         0        20         0        20         0
      3:U         0         0         0        20         0        20
      4:U     4.472     19.49         0         0        20         0
```

Marked-cell adjacency search Hamiltonian:

```text
                0:M       0:U       1:U       2:U       3:U       4:U
      0:M        -1        -0   -0.1118        -0        -0   -0.1118
      0:U        -0        -0   -0.4873        -0        -0   -0.4873
      1:U   -0.1118   -0.4873        -0      -0.5        -0        -0
      2:U        -0        -0      -0.5        -0      -0.5        -0
      3:U        -0        -0        -0      -0.5        -0      -0.5
      4:U   -0.1118   -0.4873        -0        -0      -0.5        -0
```

