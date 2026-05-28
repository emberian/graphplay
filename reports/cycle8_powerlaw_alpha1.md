# Search Compiler Report: cycle C8 power-law template alpha=1

## Problem

- domain: long-range tunneling memory ring
- task: find a marked memory sector on an eight-zone ring with power-law couplings
- encoding: each sector is a fiber; template weights decay with cyclic distance as 1/r
- compiler goal: test whether long-range weights improve the quotient spectral ratio over a sparse cycle
- proof route: regular weighted template passes the adjacency spectral-ratio route but is not Laplacian integral

## Host

- template vertices: 8
- host vertices: 80
- weighted host edge mass: 1566.67
- fibers: {'p0': 10, 'p1': 10, 'p2': 10, 'p3': 10, 'p4': 10, 'p5': 10, 'p6': 10, 'p7': 10}
- marked counts: {'p0': 1, 'p1': 0, 'p2': 0, 'p3': 0, 'p4': 0, 'p5': 0, 'p6': 0, 'p7': 0}

## Template Diagnostics

- weighted degrees: 3.91667, 3.91667, 3.91667, 3.91667, 3.91667, 3.91667, 3.91667, 3.91667
- regular template: True
- template adjacency eigenvalues: -1.41667, -1.19281, -1.19281, -0.75, -0.75, 0.692809, 0.692809, 3.91667
- CNO spectral ratio max(|lambda_i|)/lambda_1: 0.361702
- CNO ratio passes strict < 1 check: True
- template Laplacian eigenvalues: -4.08012e-16, 3.22386, 3.22386, 4.66667, 4.66667, 5.10948, 5.10948, 5.33333
- template Laplacian integral: False

## Fiber Quotient

- host weighted degrees by fiber: 39.1667, 39.1667, 39.1667, 39.1667, 39.1667, 39.1667, 39.1667, 39.1667
- regular host: True
- host quotient spectral ratio: 0.361702
- quotient adjacency eigenvalues: -14.1667, -11.9281, -11.9281, -7.5, -7.5, 6.92809, 6.92809, 39.1667
- quotient Laplacian eigenvalues: -7.92199e-15, 32.2386, 32.2386, 46.6667, 46.6667, 51.0948, 51.0948, 53.3333
- full host Laplacian integral: False
- full host Laplacian eigenvalues: -7.92199e-15, 32.2386, 32.2386, 39.1667, 39.1667, 39.1667, 39.1667, 39.1667, 39.1667, ..., 39.1667, 39.1667, 39.1667, 39.1667, 46.6667, 46.6667, 51.0948, 51.0948, 53.3333

Adjacency quotient on uniform fiber states:

```text
                 p0        p1        p2        p3        p4        p5        p6        p7
       p0         0        10         5     3.333       2.5     3.333         5        10
       p1        10         0        10         5     3.333       2.5     3.333         5
       p2         5        10         0        10         5     3.333       2.5     3.333
       p3     3.333         5        10         0        10         5     3.333       2.5
       p4       2.5     3.333         5        10         0        10         5     3.333
       p5     3.333       2.5     3.333         5        10         0        10         5
       p6         5     3.333       2.5     3.333         5        10         0        10
       p7        10         5     3.333       2.5     3.333         5        10         0
```

## Marked Quotient

- cells: {'p0:M': 1, 'p0:U': 9, 'p1:U': 10, 'p2:U': 10, 'p3:U': 10, 'p4:U': 10, 'p5:U': 10, 'p6:U': 10, 'p7:U': 10}
- gamma factors searched: [0.0625, 0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0, 16.0]
- adjacency gamma: 0.025531915
- laplacian gamma: 0.00234375
- scan horizon: [0, 44.7214] with 2600 steps
- best adjacency-CTQW marked probability: 0.994856 at t=42.0543
- best laplacian-CTQW marked probability: 0.0125 at t=0

Marked-cell adjacency quotient:

```text
               p0:M      p0:U      p1:U      p2:U      p3:U      p4:U      p5:U      p6:U      p7:U
     p0:M         0         0     3.162     1.581     1.054    0.7906     1.054     1.581     3.162
     p0:U         0         0     9.487     4.743     3.162     2.372     3.162     4.743     9.487
     p1:U     3.162     9.487         0        10         5     3.333       2.5     3.333         5
     p2:U     1.581     4.743        10         0        10         5     3.333       2.5     3.333
     p3:U     1.054     3.162         5        10         0        10         5     3.333       2.5
     p4:U    0.7906     2.372     3.333         5        10         0        10         5     3.333
     p5:U     1.054     3.162       2.5     3.333         5        10         0        10         5
     p6:U     1.581     4.743     3.333       2.5     3.333         5        10         0        10
     p7:U     3.162     9.487         5     3.333       2.5     3.333         5        10         0
```

Marked-cell adjacency search Hamiltonian:

```text
               p0:M      p0:U      p1:U      p2:U      p3:U      p4:U      p5:U      p6:U      p7:U
     p0:M        -1        -0  -0.08074  -0.04037  -0.02691  -0.02018  -0.02691  -0.04037  -0.08074
     p0:U        -0        -0   -0.2422   -0.1211  -0.08074  -0.06055  -0.08074   -0.1211   -0.2422
     p1:U  -0.08074   -0.2422        -0   -0.2553   -0.1277  -0.08511  -0.06383  -0.08511   -0.1277
     p2:U  -0.04037   -0.1211   -0.2553        -0   -0.2553   -0.1277  -0.08511  -0.06383  -0.08511
     p3:U  -0.02691  -0.08074   -0.1277   -0.2553        -0   -0.2553   -0.1277  -0.08511  -0.06383
     p4:U  -0.02018  -0.06055  -0.08511   -0.1277   -0.2553        -0   -0.2553   -0.1277  -0.08511
     p5:U  -0.02691  -0.08074  -0.06383  -0.08511   -0.1277   -0.2553        -0   -0.2553   -0.1277
     p6:U  -0.04037   -0.1211  -0.08511  -0.06383  -0.08511   -0.1277   -0.2553        -0   -0.2553
     p7:U  -0.08074   -0.2422   -0.1277  -0.08511  -0.06383  -0.08511   -0.1277   -0.2553        -0
```

