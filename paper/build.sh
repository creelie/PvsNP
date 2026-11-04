#!/bin/sh
# Assemble the flat main.tex from the parts.
cd "$(dirname "$0")"
python3 tools/make_bib.py >/dev/null
cat part0_preamble.tex part1_intro.tex part2_survey.tex part3_networks.tex part4_lower.tex part5_appendix.tex part6_declarations.tex part7_bib.tex > main.tex
printf '\n\\end{document}\n' >> main.tex
