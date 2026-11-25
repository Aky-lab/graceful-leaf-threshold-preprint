# Polynomial thresholds for graceful leaf extensions of arbitrary trees

Working preprint from Aky-lab, 25 November 2026. [Read the paper](fixed_core.pdf).

For every tree on n vertices and every prescribed distribution of new leaves among its vertices, a final edge count of at least 3,955,201 n^7 suffices for gracefulness. The paper derives this bound from two labeling constructions and a common parity count. Both the prescribed-extension theorem and its internal-vertex corollary are formalized [for finite graphs in Lean](lean/Next/TreeEncodingPolynomialParityPacket.lean).

Superdock (2014), [Corollary 5.10](https://arxiv.org/abs/1403.1564), treats arbitrarily many leaves at one prescribed vertex of a fixed tree. [Lapierre and McGuinness](https://faculty.tru.ca/smcguinness/graceful5.pdf) give attachment constructions with additional labeling and attachment hypotheses. The theorem here quantifies over all distributions and uses only the original tree order in the cutoff. We have not identified an earlier publication explicitly posing this precise quantitative question. The general Graceful Tree Conjecture remains open.

AI assistance was substantive: research agents developed labeling constructions and quantitative bounds, Dot produced Lean formalizations, and Codex maintained the manuscripts, reviewed statements, and replayed computational checks. This is a working preprint.

## Verify the degree-seven bound

Install Git and [Elan](https://github.com/leanprover/elan), then run these commands. Elan selects Lean 4.30.0 from the checked-in toolchain file. Lake reads the pinned dependency revisions from the manifest.

```sh
git clone --branch v1.1 --depth 1 https://github.com/Aky-lab/graceful-leaf-threshold-preprint.git
cd graceful-leaf-threshold-preprint/lean
lake exe cache get
lake build
```

The cache supplies compiled Mathlib dependencies. Lake compiles the paper's proof modules from the checkout. The [default build target](lean/DegreeSeven.lean) imports the regression examples, prints the types of the following graph theorems, and fails if either depends on an axiom outside `propext`, `Classical.choice`, and `Quot.sound` (including `sorryAx`).

- `FixedCore.TreeEncoding.poly_degree_seven_parity_packet` proves gracefulness when the **final edge count** is at least `3955201 * n^7`, where `n` counts vertices of the original tree. This is the first alternative in its hypothesis.
- `FixedCore.TreeEncoding.poly_parity_packet_final_nonleaf` proves gracefulness directly for a tree with at least `3955201 * h^7` edges, where `h` counts its internal vertices.

For the separate finite arithmetic replay, run `python poly-parity-coupled-replay-20261125.py` from the repository root. It checks 143,780 exact cutoffs and 122,886 reserve and capacity cases. To regenerate the PDF, run `pdflatex fixed_core.tex` twice from that directory.
