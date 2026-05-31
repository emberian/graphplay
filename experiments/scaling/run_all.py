#!/usr/bin/env python3
"""Run all four scaling experiments in sequence.

    source experiments/.venv/bin/activate
    python experiments/scaling/run_all.py

Produces figures/ and exp*_results.json; see SCALING_CLAIMS.md for the fitted
exponents and the precise expanded claims.
"""
import subprocess, sys, os

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPTS = [
    "exp1_kn_search.py",
    "exp2_hypercube_search.py",
    "exp3_lattice_threshold.py",
    "exp4_attention_linear.py",
]

for s in SCRIPTS:
    print("\n" + "=" * 70 + f"\n  {s}\n" + "=" * 70)
    rc = subprocess.call([sys.executable, os.path.join(HERE, s)])
    if rc != 0:
        print(f"!! {s} exited with code {rc}")
        sys.exit(rc)
print("\nAll experiments complete. See SCALING_CLAIMS.md.")
