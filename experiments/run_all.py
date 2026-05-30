"""Run the whole E2-minimal go/no-go suite end to end.

  python run_all.py

Runs:
  1. run_e2_minimal  — trains the 4 tiny tasks, probes A*, writes
     figures/e2_minimal.png and e2_summary.json.
  2. run_gqa_defect  — verifies SmolLM2-135M GQA head-axis defect ≡ 0 and the
     (large) token-axis defect; writes gqa_defect.json. Skips gracefully if the
     model can't be fetched (offline).

Then prints the combined go/no-go verdict.
"""

from __future__ import annotations

import json
import os

import run_e2_minimal
import run_gqa_defect

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    print("########## E2-minimal (tiny tasks) ##########")
    matches, lines = run_e2_minimal.main()

    print("\n########## GQA defect anchor (SmolLM2-135M) ##########")
    gqa = run_gqa_defect.main()

    print("\n################ COMBINED VERDICT ################")
    print(f"E2-minimal match-metric: {matches}/{len(lines)} tasks have the "
          f"needed-structure residual small & top-tier")
    gd = gqa.get("head_axis_max_defect")
    print(f"GQA head-axis defect: "
          f"{'≡ 0 (PASS)' if gqa.get('gqa_defect_zero') else gd}")
    with open(os.path.join(HERE, "combined_verdict.json"), "w") as f:
        json.dump({"e2_matches": matches, "e2_n": len(lines),
                   "e2_tasks": lines,
                   "gqa_defect_zero": gqa.get("gqa_defect_zero"),
                   "gqa_max_defect": gd,
                   "gqa_status": gqa.get("status")}, f, indent=2)


if __name__ == "__main__":
    main()
