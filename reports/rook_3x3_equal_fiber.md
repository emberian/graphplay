# Search Compiler Report: rook 3x3 cartesian complete-template with equal fibers

## Host

- template vertices: 9
- host vertices: 90
- weighted host edge mass: 1800
- fibers: {'r0,c0': 10, 'r0,c1': 10, 'r0,c2': 10, 'r1,c0': 10, 'r1,c1': 10, 'r1,c2': 10, 'r2,c0': 10, 'r2,c1': 10, 'r2,c2': 10}
- marked counts: {'r0,c0': 1, 'r0,c1': 0, 'r0,c2': 0, 'r1,c0': 0, 'r1,c1': 0, 'r1,c2': 0, 'r2,c0': 0, 'r2,c1': 0, 'r2,c2': 0}

## Template Diagnostics

- weighted degrees: 4, 4, 4, 4, 4, 4, 4, 4, 4
- regular template: True
- template adjacency eigenvalues: -2, -2, -2, -2, 1, 1, 1, 1, 4
- CNO spectral ratio max(|lambda_i|)/lambda_1: 0.5
- CNO ratio passes strict < 1 check: True
- template Laplacian eigenvalues: 9.09537e-17, 3, 3, 3, 3, 6, 6, 6, 6
- template Laplacian integral: True

## Fiber Quotient

- host weighted degrees by fiber: 40, 40, 40, 40, 40, 40, 40, 40, 40
- regular host: True
- host quotient spectral ratio: 0.5
- quotient adjacency eigenvalues: -20, -20, -20, -20, 10, 10, 10, 10, 40
- quotient Laplacian eigenvalues: -1.06581e-14, 30, 30, 30, 30, 60, 60, 60, 60
- full host Laplacian integral: True
- full host Laplacian eigenvalues: -1.06581e-14, 30, 30, 30, 30, 40, 40, 40, 40, ..., 40, 40, 40, 40, 40, 60, 60, 60, 60

Adjacency quotient on uniform fiber states:

```text
              r0,c0     r0,c1     r0,c2     r1,c0     r1,c1     r1,c2     r2,c0     r2,c1     r2,c2
    r0,c0         0        10        10        10         0         0        10         0         0
    r0,c1        10         0        10         0        10         0         0        10         0
    r0,c2        10        10         0         0         0        10         0         0        10
    r1,c0        10         0         0         0        10        10        10         0         0
    r1,c1         0        10         0        10         0        10         0        10         0
    r1,c2         0         0        10        10        10         0         0         0        10
    r2,c0        10         0         0        10         0         0         0        10        10
    r2,c1         0        10         0         0        10         0        10         0        10
    r2,c2         0         0        10         0         0        10        10        10         0
```

## Marked Quotient

- cells: {'r0,c0:M': 1, 'r0,c0:U': 9, 'r0,c1:U': 10, 'r0,c2:U': 10, 'r1,c0:U': 10, 'r1,c1:U': 10, 'r1,c2:U': 10, 'r2,c0:U': 10, 'r2,c1:U': 10, 'r2,c2:U': 10}
- gamma factors searched: [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
- adjacency gamma: 0.025
- laplacian gamma: 0.016666667
- scan horizon: [0, 47.4342] with 2200 steps
- best adjacency-CTQW marked probability: 0.990222 at t=45.0182
- best laplacian-CTQW marked probability: 0.0111111 at t=0

Marked-cell adjacency quotient:

```text
            r0,c0:M   r0,c0:U   r0,c1:U   r0,c2:U   r1,c0:U   r1,c1:U   r1,c2:U   r2,c0:U   r2,c1:U   r2,c2:U
  r0,c0:M         0         0     3.162     3.162     3.162         0         0     3.162         0         0
  r0,c0:U         0         0     9.487     9.487     9.487         0         0     9.487         0         0
  r0,c1:U     3.162     9.487         0        10         0        10         0         0        10         0
  r0,c2:U     3.162     9.487        10         0         0         0        10         0         0        10
  r1,c0:U     3.162     9.487         0         0         0        10        10        10         0         0
  r1,c1:U         0         0        10         0        10         0        10         0        10         0
  r1,c2:U         0         0         0        10        10        10         0         0         0        10
  r2,c0:U     3.162     9.487         0         0        10         0         0         0        10        10
  r2,c1:U         0         0        10         0         0        10         0        10         0        10
  r2,c2:U         0         0         0        10         0         0        10        10        10         0
```

Marked-cell adjacency search Hamiltonian:

```text
            r0,c0:M   r0,c0:U   r0,c1:U   r0,c2:U   r1,c0:U   r1,c1:U   r1,c2:U   r2,c0:U   r2,c1:U   r2,c2:U
  r0,c0:M        -1        -0  -0.07906  -0.07906  -0.07906        -0        -0  -0.07906        -0        -0
  r0,c0:U        -0        -0   -0.2372   -0.2372   -0.2372        -0        -0   -0.2372        -0        -0
  r0,c1:U  -0.07906   -0.2372        -0     -0.25        -0     -0.25        -0        -0     -0.25        -0
  r0,c2:U  -0.07906   -0.2372     -0.25        -0        -0        -0     -0.25        -0        -0     -0.25
  r1,c0:U  -0.07906   -0.2372        -0        -0        -0     -0.25     -0.25     -0.25        -0        -0
  r1,c1:U        -0        -0     -0.25        -0     -0.25        -0     -0.25        -0     -0.25        -0
  r1,c2:U        -0        -0        -0     -0.25     -0.25     -0.25        -0        -0        -0     -0.25
  r2,c0:U  -0.07906   -0.2372        -0        -0     -0.25        -0        -0        -0     -0.25     -0.25
  r2,c1:U        -0        -0     -0.25        -0        -0     -0.25        -0     -0.25        -0     -0.25
  r2,c2:U        -0        -0        -0     -0.25        -0        -0     -0.25     -0.25     -0.25        -0
```

