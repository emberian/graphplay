#!/usr/bin/env bash
# Thin wrapper: activate the qiskit venv and run the end-to-end pipeline.
#
#   ./run.sh                # full pipeline on the already-emitted ./hosts/*.json
#   ./run.sh --regen-hosts  # print the catgrad cargo command (does not run it)
#
# To regenerate the host-JSONs from the real catgrad Llama model first:
#   (cd ~/hellas/catgrad/catgrad-backend-graphplay && cargo run --example emit_hosts)
#   cp ~/hellas/catgrad/catgrad-backend-graphplay/hosts/attn_layer_*.json hosts/
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VENV="$HERE/../.venv/bin/activate"

if [[ ! -f "$VENV" ]]; then
  echo "venv not found at $VENV — create it / install qiskit qiskit-aer scipy matplotlib" >&2
  exit 1
fi

# shellcheck disable=SC1090
source "$VENV"
exec python "$HERE/run_pipeline.py" "$@"
