# An Infinite Family of Apéry-like Recurrences for Euler’s Constant

[arXiv](https://arxiv.org/abs/2610.13919)

Rotem Kalisch, Tali Monderer, Elyasheev Leibtag, Shachar Weinbaum, Michael Shalyt and Ido Kaminer

This package contains the notebook used to generate all examples in the examples section,
as well as some other examples that are not showcased in the paper.
The notebook is also hosted on [Google Colab](https://colab.research.google.com/drive/189rWd7_7M1i2d5E03OoMwGTWVuG1V75l#scrollTo=FJyoutk_qQj8).

The package also contains a Lean formalization of the Mellin–Barnes
asymptotics used in the paper.

## Notebook: constructions and numerical examples

[examples.ipynb](examples.ipynb) begins with a short `ramanujantools` tutorial:
matrix walks, conversion to linear recurrences using the cyclic vector method,
and numerical evaluation of limits, approximation errors, and delta values.

The examples then explore:

- The order-3 recurrence from Section 8.1, from its conservative matrix field
  and trajectory through the recurrence, initial values, and convergence to γ.
- Three trajectories that fail to converge to γ, with asymptotic analysis and
  a comparison of their errors against a converging trajectory.
- A family of order-3 recurrences, including proven and conjectured convergent
  cases, compared numerically with the constructions of Aptekarev et al. and Rivoal.
- An explicit gauge equivalence between the `(0, 0; 1, 1, 1)` trajectory and
  Rivoal's construction, checked symbolically.
- Higher-order examples of orders 4 and 5, whose convergence is supported
  numerically but is not proved in the paper.

The notebook includes result tables and the code generating the convergence
comparison figures.

## Lean formalization

The sources in [lean/](lean/) prove this work's equal-slope Mellin–Barnes
asymptotics: growth estimates, complex linear independence, and strong
recessiveness of the vector-valued integral sequences for every rank `r ≥ 3`,
and Neuschel's supporting uniform Laplace theorem, Theorem 3.1 of
[*A uniform version of Laplace's method for contour integrals*](https://doi.org/10.1524/anly.2012.1147).

The lean formalization was generated using GPT-6.1-Sol which prompted to generate those given the preprint.

| Result | Entry point | Final theorem |
| --- | --- | --- |
| Rank-three specialization | [ThisWork.lean](lean/ThisWork.lean) | [`ThisWork.lemma8`](lean/ThisWork/Lemma8.lean) |
| Equal-slope Mellin–Barnes asymptotics | [HigherRank.lean](lean/ThisWork/HigherRank.lean) | [`ThisWork.HigherRank.equalSlope_mellinBarnes_asymptotics`](lean/ThisWork/HigherRank/MellinBarnesAsymptotics.lean) |
| Neuschel, Theorem 3.1 | [Neuschel.lean](lean/Neuschel.lean) | [`Neuschel.neuschel_theorem_3_1_published`](lean/Neuschel/PublishedTheorem.lean) |

The rank-three theorem is stated for every real `z > 0`. The integrals `branchIntegral α₁ α₂ z`
include the full Mellin–Barnes factor `z^(n-x)`. Their common growth scale is
`H(n) z^n`, with limiting saddles `(α₁ α₂ z)^(1/3) ρⱼ` and an
`O(n^(1/3))` error in the exponent. Constants and thresholds may depend on `z`.
The theorem includes complex linear independence of the three integral sequences.
The specialization `ThisWork.lemma8_one` recovers the result at `z = 1`.

[`ThisWork.lemma8_with_strongRecessiveness`](lean/ThisWork/Recessiveness.lean)
also proves that branch three is strongly recessive relative to the span of
branches one and two: every nontrivial fixed complex combination of these two
branches is eventually nonzero, and the ratio of
branch three's vector norm to its norm decays faster than every inverse power
of `n`. [`ThisWork.Trajectory.equal_stronglyRecessive`](lean/ThisWork/Trajectory/Recessiveness.lean)
extends this conclusion to all equal lower slopes `(b,b,b)`, `b ≥ 1`, with
symbolic `z > 0`.

The equal-slope Mellin–Barnes theorem covers every integer `r ≥ 3`, equal lower slope
`b ≥ 1`, positive real upper gaps `A₁,…,Aᵣ₋₁`, and real `z > 0`.
Writing `c = (z ∏ Aᵢ)^(1/r)`, its exponential term is
`−r c Re(ρ) n^(1−1/r)`, with error `O(n^(1−2/r))`, for each `r`th root
of unity `ρ`. The common scale is `z^(bn) ∏ Γ(Aᵢ n+1)`.
It proves independence of all `r` integral sequences and strong recessiveness
of the positive-real-saddle branch against every nontrivial fixed combination
of the other branches. Even ranks include the saddle on the negative real
axis, handled by reflection and a finite Fourier identity.

The trajectory corollary
[`ThisWork.HigherRank.TStar.mellinBarnes_asymptotics`](lean/ThisWork/HigherRank/Trajectories.lean)
explicitly assumes membership in `𝒯ᵣ*`: signed integer upper coordinates
`aᵢ ≤ 0` and equal positive integer lower coordinates `b`.
It applies the analytic theorem with `Aᵢ = b − aᵢ`, proving growth,
independence, and strong recessiveness for those integral sequences.

With [elan](https://github.com/leanprover/elan) installed, verify the proofs with:

```bash
cd lean
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean and Mathlib are pinned to version 4.35.0; `lake-manifest.json` records the
dependency revisions. The audit checks every declaration in both libraries,
including the final theorems, and permits only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` axioms. No `sorry` or added axioms are used.
