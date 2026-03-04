#!/usr/bin/env bash
# Verify the project: build, check for sorry, list axioms.
set -euo pipefail

echo "=== Building project ==="
if lake build 2>&1; then
  echo "Build: PASS"
else
  echo "Build: FAIL"
  exit 1
fi

echo ""
echo "=== Sorry audit ==="
# Find actual sorry tactic uses (not comments or string mentions)
sorry_lines=$(grep -rn '^\s*sorry' FixedPoint/ --include='*.lean' || true)

if [ -z "$sorry_lines" ]; then
  echo "No sorry found in proof terms."
else
  echo "$sorry_lines"
  count=$(echo "$sorry_lines" | wc -l | tr -d ' ')
  echo ""
  echo "Total: $count sorry"
fi

echo ""
echo "=== Axiom audit ==="
axiom_lines=$(grep -rn '^axiom ' FixedPoint/ --include='*.lean' || true)

if [ -z "$axiom_lines" ]; then
  echo "No custom axioms."
else
  echo "$axiom_lines"
fi

echo ""
echo "=== Summary ==="
total_lines=$(find FixedPoint -name '*.lean' | xargs wc -l | tail -1 | awk '{print $1}')
file_count=$(find FixedPoint -name '*.lean' | wc -l | tr -d ' ')
sorry_count=$(grep -rc '^\s*sorry' FixedPoint/ --include='*.lean' 2>/dev/null | awk -F: '{s+=$2} END {print s}')
axiom_count=$(grep -rc '^axiom ' FixedPoint/ --include='*.lean' 2>/dev/null | awk -F: '{s+=$2} END {print s}')

echo "$file_count files, $total_lines lines, $sorry_count sorry, $axiom_count axiom(s)"
