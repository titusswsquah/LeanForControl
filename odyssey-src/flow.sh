#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

FORMAT="pdf"   # pdf | md
OUT=""
NAME="odyssey"   # Set the default name
STRIP_SUFFIX=0    # md mode: 0 = keep -vN in file markers, 1 = strip it
while [[ $# -gt 0 ]]; do
  case "$1" in
    --md) FORMAT="md"; shift ;;
    --pdf) FORMAT="pdf"; shift ;;
    --strip-suffix) STRIP_SUFFIX=1; shift ;;
    -o|--out) OUT="$2"; shift 2 ;;
    --name=*) NAME="${1#*=}"; shift ;;     # Handles: --name=v8 or --name='v8'
    -n|--name) NAME="$2"; shift 2 ;;       # Handles: --name v8 or -n v8
    -h|--help)
      echo "Usage: $0 [--md|--pdf] [--strip-suffix] [-o out] [--name=NAME]"
      echo "  --md            concatenate sources into <name>.md (no pandoc)"
      echo "  --pdf           render to <name>.pdf via pandoc + xelatex (default)"
      echo "  --strip-suffix  md mode: drop the trailing -vN from the name written"
      echo "                  into each <!-- BEGIN/END FILE: ... --> marker"
      echo "  -n, --name      Set the output filename base (default: costogo)"
      exit 0 ;;
    *) echo "Unknown arg: $1" >&2; exit 1 ;;
  esac
done

# Use $NAME instead of the hardcoded string
if [[ -z "$OUT" ]]; then
  OUT="$SCRIPT_DIR/$NAME.$FORMAT"
fi

# If the user passed a relative OUT, resolve it relative to their cwd
# (not the script dir we're about to cd into).
case "$OUT" in /*) ;; *) OUT="$PWD/$OUT" ;; esac

cd "$SCRIPT_DIR"

FILES=(
00-problem.md
01-structure.md
02-criterion.md
03-supremal.md
04-evolution.md
05-lowsqueeze.md
06-sufficiency.md
07-necessity.md
08-main.md
09-payoff.md
a00-facts.md
a01-frame.md
a02-machinery.md
a03-formula.md
a04-subspace.md
)

if [[ "$FORMAT" == "md" ]]; then
  # Faithful concatenation with a blank line between files. No preprocessing of
  # the source content -- but each file is wrapped in
  #   <!-- BEGIN FILE: name -->  ...  <!-- END FILE: name -->
  # HTML-comment markers (invisible when rendered) so rflow.sh can split the
  # compiled .md back into per-file sources. With --strip-suffix the trailing
  # -vN is removed from the name placed in the marker.
  awk -v strip="$STRIP_SUFFIX" '
    function basename(p,   n, a) { n = split(p, a, "/"); return a[n] }
    function markname(f,   b) {
      b = basename(f)
      if (strip) sub(/-v[0-9]+\.md$/, ".md", b)
      return b
    }
    FNR == 1 {
      if (NR > 1) {
        print "<!-- END FILE: " prev " -->"
        print ""
      }
      cur = markname(FILENAME)
      print "<!-- BEGIN FILE: " cur " -->"
      prev = cur
    }
    { print }
    END {
      if (NR > 0) print "<!-- END FILE: " prev " -->"
    }
  ' "${FILES[@]}" > "$OUT"
else
  # Concatenate (blank line between files) and strip blank lines inside
  # \[ ... \] display-math blocks — markdown would otherwise end the math early.
  awk '
    FNR == 1 && NR > 1 { print "" }
    {
      line = $0
      if (in_math) {
        if (line ~ /^[ \t]*$/) next
      }
      print line
      n_open  = gsub(/\\\[/, "&", line)
      n_close = gsub(/\\\]/, "&", line)
      in_math += n_open - n_close
      if (in_math < 0) in_math = 0
    }
  ' "${FILES[@]}" \
    | pandoc \
        --from=markdown+tex_math_single_backslash \
        --pdf-engine=xelatex \
        --metadata=title:"Discrete dual estimation — attraction to the strong DARE solution" \
        -V geometry:margin=1in \
        -V header-includes:'\usepackage{mathtools}' \
        -V header-includes:'\usepackage{newunicodechar}\newunicodechar{∎}{\ensuremath{\blacksquare}}' \
        -o "$OUT"
fi

echo "Wrote $OUT"
