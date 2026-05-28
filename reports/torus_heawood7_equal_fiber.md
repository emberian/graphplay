# Search Compiler Report: torus Heawood-7 surface envelope with equal fibers

## Problem

- domain: surface-embedded interaction fabric
- task: compile a nonplanar toroidal interaction skeleton into a bounded color-sector search host
- encoding: Heawood's torus bound gives a seven-color complete template; each color is a physical fiber
- compiler goal: use surface genus as a color and spectral-gap budget
- proof route: complete K7 template is regular, Laplacian integral, and has strong spectral-ratio separation

## Host

- template vertices: 7
- host vertices: 56
- weighted host edge mass: 1344
- fibers: {'c0': 8, 'c1': 8, 'c2': 8, 'c3': 8, 'c4': 8, 'c5': 8, 'c6': 8}
- marked counts: {'c0': 1, 'c1': 0, 'c2': 0, 'c3': 0, 'c4': 0, 'c5': 0, 'c6': 0}

## Template Diagnostics

- weighted degrees: 6, 6, 6, 6, 6, 6, 6
- regular template: True
- template adjacency eigenvalues: -1, -1, -1, -1, -1, -1, 6
- CNO spectral ratio max(|lambda_i|)/lambda_1: 0.166667
- CNO ratio passes strict < 1 check: True
- template Laplacian eigenvalues: 1.11022e-16, 7, 7, 7, 7, 7, 7
- template Laplacian integral: True

## Fiber Quotient

- host weighted degrees by fiber: 48, 48, 48, 48, 48, 48, 48
- regular host: True
- host quotient spectral ratio: 0.166667
- quotient adjacency eigenvalues: -8, -8, -8, -8, -8, -8, 48
- quotient Laplacian eigenvalues: -1.77636e-15, 56, 56, 56, 56, 56, 56
- full host Laplacian integral: True
- full host Laplacian eigenvalues: -1.77636e-15, 48, 48, 48, 48, 48, 48, 48, 48, ..., 48, 48, 48, 56, 56, 56, 56, 56, 56

Adjacency quotient on uniform fiber states:

```text
                 c0        c1        c2        c3        c4        c5        c6
       c0         0         8         8         8         8         8         8
       c1         8         0         8         8         8         8         8
       c2         8         8         0         8         8         8         8
       c3         8         8         8         0         8         8         8
       c4         8         8         8         8         0         8         8
       c5         8         8         8         8         8         0         8
       c6         8         8         8         8         8         8         0
```

## Marked Quotient

- cells: {'c0:M': 1, 'c0:U': 7, 'c1:U': 8, 'c2:U': 8, 'c3:U': 8, 'c4:U': 8, 'c5:U': 8, 'c6:U': 8}
- gamma factors searched: [0.125, 0.25, 0.5, 1.0, 2.0, 4.0, 8.0]
- adjacency gamma: 0.020833333
- laplacian gamma: 0.14285714
- scan horizon: [0, 33.6749] with 2200 steps
- best adjacency-CTQW marked probability: 0.994854 at t=11.6691
- best laplacian-CTQW marked probability: 0.0178571 at t=0

Marked-cell adjacency quotient:

```text
               c0:M      c0:U      c1:U      c2:U      c3:U      c4:U      c5:U      c6:U
     c0:M         0         0     2.828     2.828     2.828     2.828     2.828     2.828
     c0:U         0         0     7.483     7.483     7.483     7.483     7.483     7.483
     c1:U     2.828     7.483         0         8         8         8         8         8
     c2:U     2.828     7.483         8         0         8         8         8         8
     c3:U     2.828     7.483         8         8         0         8         8         8
     c4:U     2.828     7.483         8         8         8         0         8         8
     c5:U     2.828     7.483         8         8         8         8         0         8
     c6:U     2.828     7.483         8         8         8         8         8         0
```

Marked-cell adjacency search Hamiltonian:

```text
               c0:M      c0:U      c1:U      c2:U      c3:U      c4:U      c5:U      c6:U
     c0:M        -1        -0  -0.05893  -0.05893  -0.05893  -0.05893  -0.05893  -0.05893
     c0:U        -0        -0   -0.1559   -0.1559   -0.1559   -0.1559   -0.1559   -0.1559
     c1:U  -0.05893   -0.1559        -0   -0.1667   -0.1667   -0.1667   -0.1667   -0.1667
     c2:U  -0.05893   -0.1559   -0.1667        -0   -0.1667   -0.1667   -0.1667   -0.1667
     c3:U  -0.05893   -0.1559   -0.1667   -0.1667        -0   -0.1667   -0.1667   -0.1667
     c4:U  -0.05893   -0.1559   -0.1667   -0.1667   -0.1667        -0   -0.1667   -0.1667
     c5:U  -0.05893   -0.1559   -0.1667   -0.1667   -0.1667   -0.1667        -0   -0.1667
     c6:U  -0.05893   -0.1559   -0.1667   -0.1667   -0.1667   -0.1667   -0.1667        -0
```

