# Project S · P11 · Rank windows in Shellsort

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

For appropriate bounded read and influence sets of a fixed prefix, the conditional next-pass theorem gives a lower bound on mean inversions and comparisons. These lemmas are related to prefix structure. They do not certify the full analytical rank-window claim.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

Additional executable check: after the build, run `lake env lean SixSlotExample.lean`. See [SixSlotExample.lean](SixSlotExample.lean).

## Proof guide

[Read the proof idea in Chinese](brief.md). The guide explains the mathematical claim and the scope of the Lean results linked above.
