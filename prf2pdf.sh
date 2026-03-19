#!/usr/bin/env bash
# prf2pdf.sh — extract one proof graph from a .dotstar file and render to PDF
#
# Usage: prf2pdf.sh <dotstar> <theorem> [output]
#
#   dotstar   Path to a .dotstar file, or '.' to use the most recent one in ltresults/
#   theorem   Theorem identifier in any of these forms:
#               425   4.25   *4.25   *425   201   2.01   *2.01   *201
#   output    PDF output path or directory (default: current directory)
#
# Examples:
#   ./prf2pdf.sh . 425
#   ./prf2pdf.sh . 4.25 ~/Desktop/
#   ./prf2pdf.sh ltresults/202603181403.dotstar '*4.25' .
#   ./prf2pdf.sh . 201 /tmp/my-proof.pdf

set -euo pipefail

REPO_DIR="$(cd "$(dirname "$0")" && pwd)"
RESULTS_DIR="$REPO_DIR/ltresults"

usage() {
    cat <<EOF
Usage: $(basename "$0") <dotstar> <theorem> [output]

  dotstar   Path to .dotstar file, or '.' for the latest in ltresults/
  theorem   Theorem id: 425  4.25  *4.25  *425  201  2.01  *2.01  etc.
  output    PDF output path or directory (default: current directory)

Examples:
  $(basename "$0") . 425
  $(basename "$0") . 4.25 ~/Desktop/
  $(basename "$0") ltresults/202603181403.dotstar '*4.25' .
  $(basename "$0") . 201 /tmp/my-proof.pdf
EOF
    exit 1
}

[ $# -lt 2 ] && usage

DOTSTAR="$1"
THM_RAW="$2"
OUTPUT="${3:-.}"

# --- Resolve dotstar: '.' → most recent file in ltresults/ ---
if [ "$DOTSTAR" = "." ]; then
    DOTSTAR=$(ls -t "$RESULTS_DIR"/*.dotstar 2>/dev/null | head -1 || true)
    [ -z "$DOTSTAR" ] && { echo "Error: no .dotstar files found in $RESULTS_DIR"; exit 1; }
    echo "Using: $DOTSTAR"
fi
[ -f "$DOTSTAR" ] || { echo "Error: file not found: $DOTSTAR"; exit 1; }

# --- Normalize theorem id to dotted form, e.g. "425" → "4.25" ---
# Strip a leading * if present
THM="${THM_RAW#\*}"
# If no dot, insert before the last two digits: "425"→"4.25", "201"→"2.01"
if [[ "$THM" != *.* ]]; then
    n="${#THM}"
    if [ "$n" -gt 2 ]; then
        THM="${THM:0:$((n-2))}.${THM:$((n-2))}"
    fi
fi
LABEL="*${THM}"       # e.g. "*4.25"  — must match the dotstar separator line
STEM="${THM//./}"     # e.g. "425"    — used for the temp filename

# --- Extract the digraph block ---
TMP_DOT="/tmp/lt-proof-${STEM}.dot"

awk -v label="$LABEL" '
    BEGIN { found=0; cap=0 }
    $0 == "// Problem " label { found=1; next }
    found && /^digraph / { cap=1 }
    cap { print }
    cap && /^\}$/ { exit }
' "$DOTSTAR" > "$TMP_DOT"

if [ ! -s "$TMP_DOT" ]; then
    echo "Error: theorem $LABEL not found in $(basename "$DOTSTAR")"
    echo "Available theorems:"
    grep '^// Problem ' "$DOTSTAR" | sed 's|// Problem ||'
    exit 1
fi
echo "Extracted: $TMP_DOT"

# --- Resolve output path ---
# Strip trailing slash for consistency
OUTPUT="${OUTPUT%/}"
if [ -d "$OUTPUT" ] || [ "$OUTPUT" = "." ]; then
    PDF="${OUTPUT}/lt-proof-${STEM}.pdf"
else
    PDF="$OUTPUT"
    # Create parent directory if needed
    mkdir -p "$(dirname "$PDF")"
fi

# --- Render ---
dot -Tpdf "$TMP_DOT" -o "$PDF" && echo "Rendered:  $PDF"
