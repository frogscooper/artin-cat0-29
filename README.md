# A 29-generator Artin group with no geometric CAT(0) action

This is an edited version of OpenAI's preprint *An Artin group with no geometric CAT(0) action* (September 23, 2026), from the [openai/math](https://github.com/openai/math) repo. Their paper builds an Artin group on 116 generators that admits no geometric action on any CAT(0) space, which refutes the CAT(0) conjecture for Artin groups.

The change here is small but it shrinks the example a lot. The original proof glues a 40-strand braid group onto each edge of a little triangle group, because its argument needs that many strands to push a certain length ratio above 1/2. A shorter argument gets the same bound with 11 strands. Nothing else in the construction depends on the block size, so the group drops from 116 generators to 29.

Everything else (the six-sector obstruction, the centralizer trick, the assembly) is OpenAI's and is untouched.

**Paper:** [paper/artin-cat0-29.pdf](paper/artin-cat0-29.pdf)

## The new argument

This is the proof of Proposition 3.1 in the paper. In the braid group B_l, let Z_r be the full twist on the first r strands, let D be the translation length of s_1^2, and put Q_r = <s_1^2, Z_r> / D^2. The paper already shows

    Q_r = 1 + (r-2) x + C(r-2, 2) c_0,     where x = Q_3 - 1,

for some constant c_0. Two positivity facts are enough to pin down x:

1. Z_l has nonnegative squared length, so Q_l >= 0.
2. Z_{l-1} and Z_l commute, so W = Z_{l-1}^l Z_l^{-(l-2)} also has nonnegative squared length. Expanding gives l Q_{l-1} - (l-2) Q_l >= 0.

Add the first inequality to (l-2)/4 times the second. The c_0 terms cancel and you're left with x >= -2/(l-2), so the squared ratio the paper needs is at least (l-4) / (3(l-2)). That's bigger than 1/4 exactly when l >= 11. At l = 11 it's 7/27.

At l = 10 the bound is exactly 1/4, which isn't enough, and both constraints are tight at the same point, so this method can't go lower than 11.

## Lean

`lean/` is a cut-down copy of the openai/math Lean project containing just the Artin formalization, adapted to the 29-generator matrix. It builds the whole theorem, not only the new lemma. Running `#print axioms` on `OAI.ArtinCAT0.main` reports only `propext`, `Classical.choice` and `Quot.sound`. The statement in `ComparatorChallenges/ArtinCAT0.lean` is OpenAI's challenge statement with only the matrix size changed.

To check it yourself (needs [elan](https://github.com/leanprover/elan)):

```
cd lean
lake exe cache get
lake build
lake env lean Check.lean
```

One thing to know: when I built this, the Mathlib cache server wasn't reachable, so I replaced `import Mathlib` with an explicit list of Mathlib modules to keep the build small. `patches/lean.patch` is the same change written against the upstream repo with `import Mathlib` kept. I haven't built that exact version myself. It should behave the same, but it hasn't been tested.

## Other files

- `scripts/verify_braid_bound.py` checks the algebra above in exact arithmetic for l up to 59, and checks the braid identities it relies on in the Burau representation. Plain Python, no dependencies.
- `patches/` has diffs against openai/math for the paper source and the Lean code.
- `paper/src/` is the LaTeX source.

## Caveats

OpenAI's paper hasn't been peer reviewed. The Lean proof covers the full theorem, but only as stated, so it's worth reading the definitions in `Model.lean` (CAT(0), geometric action, Artin group) and making sure they say what you think they say. I'm also not claiming 29 is the smallest possible; it's just the smallest this method gives.

## Credit and license

The original paper and formalization are by OpenAI and released under the Apache License 2.0. This repo uses the same license (see `LICENSE`). Files I changed have a note at the top saying what was changed. The new argument and the Lean port were worked out with help from Claude (Anthropic).

Questions or corrections: stemboy@posteo.com, or see [frogscooper.dev](https://frogscooper.dev).
