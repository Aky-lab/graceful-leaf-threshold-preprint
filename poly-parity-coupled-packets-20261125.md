# Parity-coupled two-bank margins and the uniform edge cutoff

Lean entry point: `Next.TreeEncodingPolynomialParityPacket`.

For a tree of order `n`, the final named leaf extension is graceful if it has at least
`3,955,201 * n^7` edges, or independently if any two distinct sites each have demand
at least `ParityPacket.trigger n q 0`, where `q` counts the positive demands. The exact
public theorems are `FixedCore.TreeEncoding.poly_degree_seven_parity_packet` and
`FixedCore.TreeEncoding.poly_parity_packet_two_sites`. The same edge coefficient applies
to the number of intrinsic nonleaves via `poly_parity_packet_final_nonleaf`.

The named-pair theorem `poly_parity_packet_two_sites_adaptive` uses
`ParityPacket.trigger n q o` instead, where `o` counts odd demands outside the first
named bank. For `2 ≤ q ≤ n` and `o < q`, this is exactly

```text
(q - 1)^2 * (1236*n + 1200*q - 3764 - 1200*max(0,o-1)).
```

At order six with three positive demands, the independent per-site threshold is
29,008 rather than 57,808, or 24,208 when both off-root demands are odd. The
uniform edge guarantee at order six decreases from 2,182,157,387,136 to
1,107,203,147,136. These are sufficient bounds, not assertions of optimality or
of a new labeling runtime. The dedicated exactly-two-active-site result is unchanged.

## Why the two bounds can be coupled

For first bank `u`, second bank `v`, and `o = offSiteReserve c u`, the Lean
reserve identity is `total (reserve c u v) + o = 2*(q-2) + c v % 2`. The bit at
`v` is at most `o`, so the two-bank enlarged edge count is at most
`j = n + 2q - 5 - max(0,o-1)`. This is a count of actual edges, not a change to
the construction. The charged-packet width is computed from `j`; the existing
balanced modular trial, both bank orientations, credit restoration, and bare
double-broom alternative still apply.

If no second demand meets the adaptive threshold at a maximum, use the erased-site
one-bank completion on exact prepared order `S = n + o`. Evenness of the threshold
bounds each other even residual by the threshold minus two. The packing term is
controlled by the product `S^3 * (3636*n - 2564 - 1200*S)`, proved monotone on
the range used for `n ≥ 6`. The endpoint uses `S = 2*n - 1` and yields packing
at most `200*(2*n-1)^4*(n-1)^2*(1236*n-1364)`. A polynomial with nonnegative
coefficients in `n-32` absorbs the checked seed allowance. The remaining small
cases are closed with kernel reduction.

## Verification

The regression module checks exact reserve bits, odd named pairs in both
orientations, an all-even pair, a one-bank fallback with five odd secondary
demands, support one, and the arithmetic at order `2^500`.
The adjacent Python replay independently checked 143,780 exact cutoffs and 122,886
reserve/capacity cases, including orders near powers of two through `2^500`.

Original development audit (before the public source was trimmed): 3,244 Lake jobs. Rejecting axiom audit: 133 declarations across all
8 new modules and 6,938 declarations across 270 project modules in the import
closure. Only `propext`, `Classical.choice`, and `Quot.sound` were allowed.
The source-verified closure manifest SHA-256 is
`e37ee200e586ab8b3b712bf11c375a037f5b4ef032db2aa7232c73cb65a558d9`.
Lean 4.30.0 (`d024af099ca4bf2c86f649261ebf59565dc8c622`), with mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`.
