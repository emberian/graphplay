# Search Compiler Report: four-color completion with unequal color classes

## Problem

- domain: unbalanced planar decomposition
- task: search after a four-coloring with uneven color-class sizes
- encoding: color classes become unequal fibers over K4
- compiler goal: test what survives when equal-fiber regularity is lost
- proof route: Laplacian-integral complete multipartite route remains available; simple adjacency spectral-ratio route does not

## Host

- template vertices: 4
- host vertices: 64
- weighted host edge mass: 1446
- fibers: {'red': 7, 'green': 13, 'blue': 19, 'yellow': 25}
- marked counts: {'red': 0, 'green': 0, 'blue': 1, 'yellow': 0}

## Template Diagnostics

- weighted degrees: 3, 3, 3, 3
- regular template: True
- template adjacency eigenvalues: -1, -1, -1, 3
- CNO spectral ratio max(|lambda_i|)/lambda_1: 0.333333
- CNO ratio passes strict < 1 check: True
- template Laplacian eigenvalues: 1.11022e-16, 4, 4, 4
- template Laplacian integral: True

## Fiber Quotient

- host weighted degrees by fiber: 57, 51, 45, 39
- regular host: False
- quotient adjacency eigenvalues: -22.1775, -15.2489, -8.3724, 45.7988
- quotient Laplacian eigenvalues: -1.77636e-15, 64, 64, 64
- full host Laplacian integral: True
- full host Laplacian eigenvalues: -1.77636e-15, 39, 39, 39, 39, 39, 39, 39, 39, ..., 57, 57, 57, 57, 57, 57, 64, 64, 64

Adjacency quotient on uniform fiber states:

```text
                red     green      blue    yellow
      red         0     9.539     11.53     13.23
    green     9.539         0     15.72     18.03
     blue     11.53     15.72         0     21.79
   yellow     13.23     18.03     21.79         0
```

## Marked Quotient

- cells: {'red:U': 7, 'green:U': 13, 'blue:M': 1, 'blue:U': 18, 'yellow:U': 25}
- gamma factors searched: [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
- adjacency gamma: 0.021834623
- laplacian gamma: 0.001953125
- scan horizon: [0, 32] with 2000 steps
- best adjacency-CTQW marked probability: 0.988545 at t=13.0145
- best laplacian-CTQW marked probability: 0.015625 at t=0

Marked-cell adjacency quotient:

```text
              red:U   green:U    blue:M    blue:U  yellow:U
    red:U         0     9.539     2.646     11.22     13.23
  green:U     9.539         0     3.606      15.3     18.03
   blue:M     2.646     3.606         0         0         5
   blue:U     11.22      15.3         0         0     21.21
 yellow:U     13.23     18.03         5     21.21         0
```

Marked-cell adjacency search Hamiltonian:

```text
              red:U   green:U    blue:M    blue:U  yellow:U
    red:U        -0   -0.2083  -0.05777   -0.2451   -0.2888
  green:U   -0.2083        -0  -0.07873    -0.334   -0.3936
   blue:M  -0.05777  -0.07873        -1        -0   -0.1092
   blue:U   -0.2451    -0.334        -0        -0   -0.4632
 yellow:U   -0.2888   -0.3936   -0.1092   -0.4632        -0
```

