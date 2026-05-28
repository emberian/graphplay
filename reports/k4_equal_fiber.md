# Search Compiler Report: four-color K4 template with equal fibers

## Problem

- domain: planar interaction skeleton
- task: search for one marked site after four-color decomposition
- encoding: four color classes become equal fibers over a K4 template
- compiler goal: baseline complete color-host search quotient
- proof route: regular equal-fiber complete template satisfies both spectral-ratio and Laplacian-integral routes

## Host

- template vertices: 4
- host vertices: 64
- weighted host edge mass: 1536
- fibers: {'red': 16, 'green': 16, 'blue': 16, 'yellow': 16}
- marked counts: {'red': 1, 'green': 0, 'blue': 0, 'yellow': 0}

## Template Diagnostics

- weighted degrees: 3, 3, 3, 3
- regular template: True
- template adjacency eigenvalues: -1, -1, -1, 3
- CNO spectral ratio max(|lambda_i|)/lambda_1: 0.333333
- CNO ratio passes strict < 1 check: True
- template Laplacian eigenvalues: 1.11022e-16, 4, 4, 4
- template Laplacian integral: True

## Fiber Quotient

- host weighted degrees by fiber: 48, 48, 48, 48
- regular host: True
- host quotient spectral ratio: 0.333333
- quotient adjacency eigenvalues: -16, -16, -16, 48
- quotient Laplacian eigenvalues: 1.77636e-15, 64, 64, 64
- full host Laplacian integral: True
- full host Laplacian eigenvalues: 1.77636e-15, 48, 48, 48, 48, 48, 48, 48, 48, ..., 48, 48, 48, 48, 48, 48, 64, 64, 64

Adjacency quotient on uniform fiber states:

```text
                red     green      blue    yellow
      red         0        16        16        16
    green        16         0        16        16
     blue        16        16         0        16
   yellow        16        16        16         0
```

## Marked Quotient

- cells: {'red:M': 1, 'red:U': 15, 'green:U': 16, 'blue:U': 16, 'yellow:U': 16}
- gamma factors searched: [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
- adjacency gamma: 0.020833333
- laplacian gamma: 0.0078125
- scan horizon: [0, 32] with 2000 steps
- best adjacency-CTQW marked probability: 0.994441 at t=12.4702
- best laplacian-CTQW marked probability: 0.015625 at t=0

Marked-cell adjacency quotient:

```text
              red:M     red:U   green:U    blue:U  yellow:U
    red:M         0         0         4         4         4
    red:U         0         0     15.49     15.49     15.49
  green:U         4     15.49         0        16        16
   blue:U         4     15.49        16         0        16
 yellow:U         4     15.49        16        16         0
```

Marked-cell adjacency search Hamiltonian:

```text
              red:M     red:U   green:U    blue:U  yellow:U
    red:M        -1        -0  -0.08333  -0.08333  -0.08333
    red:U        -0        -0   -0.3227   -0.3227   -0.3227
  green:U  -0.08333   -0.3227        -0   -0.3333   -0.3333
   blue:U  -0.08333   -0.3227   -0.3333        -0   -0.3333
 yellow:U  -0.08333   -0.3227   -0.3333   -0.3333        -0
```

