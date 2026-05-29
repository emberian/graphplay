-- This module is the root of the `Graphplay` library.
-- See `paper/graphplay_pitch.typ` and `README.md` for orientation.

-- Upstream-bound infrastructure staging (PR-ready, Mathlib-general)
import Graphplay.ForMathlib.Basic
import Graphplay.ForMathlib.HilbertSchmidt

-- Core spine (Towers 1-2)
import Graphplay.Basic
import Graphplay.Weighted
import Graphplay.Loopy
import Graphplay.Loopy.Laplacian
import Graphplay.Equitable
import Graphplay.Spectral

-- Constructive engine + primitives
import Graphplay.Product
import Graphplay.Product.PST
import Graphplay.Bundle
import Graphplay.PST
import Graphplay.Mixing
import Graphplay.Search
import Graphplay.Search.CNO
import Graphplay.Loopy.Search

-- Chiral / operator-algebra (Tower 2 chiral, Tower 3)
import Graphplay.Chiral
import Graphplay.QuantumGraph
import Graphplay.OperatorSystem

-- Graphons (Tower 4)
import Graphplay.Graphon
import Graphplay.Graphon.Equitable
import Graphplay.Graphon.PST
import Graphplay.Graphon.Limit
import Graphplay.Graphon.Spectrum
import Graphplay.Graphon.LimitReverse
import Graphplay.Graphon.Lindblad

-- Categorical (Tower 5)
import Graphplay.Categorical
import Graphplay.Categorical.Topos

-- Higher towers
import Graphplay.Tower6
import Graphplay.Tower7

-- Computable substrate + surface embeddings + demo
import Graphplay.Computable
import Graphplay.Computable.Float
import Graphplay.CombinatorialMap
import Graphplay.Examples.Torus
import Graphplay.Examples.KleinBottle
import Graphplay.Examples.HeawoodOnTorus
import Graphplay.Demo

-- k-ary relational
import Graphplay.Relational

-- Conservation, topology, information, conservation laws
import Graphplay.ConservationLaw
import Graphplay.TopologicalProtection
import Graphplay.Information
import Graphplay.LovaszTheta
import Graphplay.CarusoSpeedup
import Graphplay.QuantumCSP
import Graphplay.ManyBody
import Graphplay.DiscreteTime

-- PST foundations (γ-loops L1, L2, L3)
import Graphplay.PST.Cospectrality
import Graphplay.PST.GodsilRatio
import Graphplay.PST.QuotientIff
import Graphplay.PST.DiagonalShift

-- Algorithms (γ-loops L4, L6 + β)
import Graphplay.Algorithm.WLRefinement
import Graphplay.Algorithm.WLOrbit
import Graphplay.Algorithm.Coloring
import Graphplay.Algorithm.ChiralOpt
import Graphplay.Algorithm.StdLibMatch
import Graphplay.Algorithm.PrimitiveDSL

-- Stdlib of known PST/mixing families
import Graphplay.StdLib.Path
import Graphplay.StdLib.Hypercube
import Graphplay.StdLib.HypercubeProduct
import Graphplay.StdLib.Hamming
import Graphplay.StdLib.Cayley
import Graphplay.StdLib.CompleteMultipartite
import Graphplay.StdLib.Cycle
import Graphplay.StdLib.Computable

-- Dowsing-rod theorems (open Tamon-corpus extensions)
import Graphplay.Dowsing.ChiralBundlePST
import Graphplay.Dowsing.BundlePSTLift
import Graphplay.Dowsing.ChiralGraphon
import Graphplay.Dowsing.CoherentAlgebra
import Graphplay.Dowsing.NonCommutativeCoherent
import Graphplay.Dowsing.FractionalRevivalNC
import Graphplay.Dowsing.HypergraphPST
import Graphplay.Dowsing.NoiseEquitable
import Graphplay.Dowsing.FilteredColimitPST
import Graphplay.Dowsing.Conjecture93

-- Cross-framework integrations
import Graphplay.Integrations.TQFT
import Graphplay.Integrations.RMT
import Graphplay.Integrations.TensorNetworks
import Graphplay.Integrations.OptimalTransport
import Graphplay.Integrations.MeanFieldGames
import Graphplay.Integrations.Hodge
import Graphplay.Integrations.LatticeGauge
import Graphplay.Integrations.WLRefinement

-- Engineering toolkit
import Graphplay.Toolkit
import Graphplay.Toolkit.Spec
import Graphplay.Toolkit.Bundle
import Graphplay.Toolkit.Report
import Graphplay.Toolkit.Hardware
import Graphplay.Toolkit.Noise
import Graphplay.Toolkit.Scheduler

-- Applied spectral disassembly case studies
import Graphplay.Applications.IBMHeavyHex
import Graphplay.Applications.MajoranaOne
