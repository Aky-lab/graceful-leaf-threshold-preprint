# Polynomial thresholds for graceful leaf extensions of arbitrary trees

Working preprint from Aky-lab, 25 November 2026. [Read the paper](fixed_core.pdf).

For every tree on n vertices and every prescribed distribution of new leaves among its vertices, a final edge count of at least 3,955,201 n^7 suffices for gracefulness. The PDF gives an elementary proof with a degree-eleven bound. The stronger bound is stated for the actual finite graph in [the Lean proof](lean/Next/TreeEncodingPolynomialParityPacket.lean).

Superdock (2014), [Corollary 5.10](https://arxiv.org/abs/1403.1564), treats arbitrarily many leaves at one prescribed vertex of a fixed tree. [Lapierre and McGuinness](https://faculty.tru.ca/smcguinness/graceful5.pdf) give attachment constructions with additional labeling and attachment hypotheses. The theorem here quantifies over all distributions and uses only the original tree order in the cutoff. We have not identified an earlier publication explicitly posing this precise quantitative question. The general Graceful Tree Conjecture remains open.

AI assistance was substantive: research agents developed labeling constructions and quantitative bounds, Dot produced Lean formalizations, and Codex maintained the manuscripts, reviewed statements, and replayed computational checks. This is a working preprint. The original project recorded a pinned focused Lean build and axiom audit. The extracted public source bundle has not had a fresh independent end-to-end build.

To check the strongest theorem, use Lean 4.30.0 and the supplied Mathlib manifest. From lean/ run `lake exe cache get`, then `lake build +Next.TreeEncodingPolynomialParityPacket +Next.ParityPacketRegression`. From the top directory run `python poly-parity-coupled-replay-20261125.py` to check the numerical arithmetic. Run pdflatex twice on fixed_core.tex to regenerate the paper.
