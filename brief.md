# Rank windows and the cost of the next pass

Among ranks 10 through 17 exactly four occupy even slots in the final array. If six occupy even slots at a checkpoint, subsequent even gaps preserve that count. A parity-changing movement must repair the discrepancy.

For window length $L$ and modulus $d$, compare current and target counts by slot residue. An elementary exchange changes the residues of at most two keys, and none if $d$ divides the gap. Each key belongs to at most $L$ windows. Accounting for this overlap turns observed discrepancies into a lower bound on remaining shifts.

Trace a slot backwards through a predetermined prefix $w$. At each pass include every slot on the relevant gap chain as a possible source, continuing to the original input. Suppose every output slot has at most $B$ sources and every original slot occurs in at most $B$ source sets. For $B\ge1$, $g\ge1$ and $8gB^3\le n$, Lean gives the uniform-input bound
$$\mathbb E C_{\rm next}\ge\mathbb E I_g\ge n^2/(128gB).$$
The proof bounds inversion probabilities for selected slot pairs with disjoint sources, sums them along the next chains, and charges each successful shift one comparison. Pass count and movement budget alone do not immediately supply the two source bounds. Inferring simultaneous discrepancies in many rank windows from short-prefix comparison records requires a further analytical argument.

[PaidResidueWindows.lean](https://github.com/EternalYMZ/Rank-windows-in-Shellsort/blob/a8795aae4f3a2619844bcfcd6b74896544a7a048/Shellsort/PaidResidueWindows.lean) · [SixSlotExample.lean](https://github.com/EternalYMZ/Rank-windows-in-Shellsort/blob/a8795aae4f3a2619844bcfcd6b74896544a7a048/SixSlotExample.lean) · [PrefixRankSymmetrization.lean](https://github.com/EternalYMZ/Rank-windows-in-Shellsort/blob/a8795aae4f3a2619844bcfcd6b74896544a7a048/Shellsort/PrefixRankSymmetrization.lean)
