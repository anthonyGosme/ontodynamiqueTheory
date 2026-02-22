#!/bin/bash
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$SCRIPT_DIR"

echo "============================================"
echo "Ontodynamique — MDSINE2 Empirical Validation"
echo "============================================"

mkdir -p output

echo ""
echo "--- Phase 1: Raw metrics (exploratory) ---"
python3 scripts/01_phase1_raw_metrics.py
echo ""

echo "--- Phase 2: Corrected analysis (publishable) ---"
python3 scripts/02_phase2_corrected.py
echo ""

echo "--- Phase 3: Interaction matrix (non concluant) ---"
python3 scripts/03_phase3_interaction_matrix.py
echo ""

echo "============================================"
echo "Done. Figures in output/"
echo "============================================"
ls -la output/*.png
