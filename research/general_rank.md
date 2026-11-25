# Equal lower slopes in arbitrary rank

The analytic extension is proved in `lean/ThisWork/MellinBarnesAsymptotics.lean`:
`ThisWork.equalSlope_mellinBarnes_asymptotics`.
The entry point has a stable descriptive name independent of paper numbering.
The arbitrary-rank proof lives directly under `lean/ThisWork/`; `RankThree.lean`
contains specialization corollaries rather than an independent analytic proof.
`Trajectories.lean` defines signed integer trajectories and `TStar r` explicitly;
`TStar.mellinBarnes_asymptotics` derives all three conclusions for every
member, with its common positive lower slope `b` and gaps `A_i = b-a_i`.
The analytic theorem covers every fixed integer `r ≥ 3`, equal lower slope
`b ≥ 1`, upper gaps `A_i > 0`, and fixed real `z > 0`. Its lower-slope
parameter can also be zero, whereas membership in `TStar` requires `b > 0`. The parameter `z` remains symbolic
throughout. Constants may depend on `r,b,A,z`; no uniformity as rank grows or
`z` tends to zero is asserted. Recurrences and CMFs are outside this theorem.

## Statement and indexing

For `k = 0,…,r−1`, the implementation uses the balanced Fourier labels

\[
 j_k=\lfloor r/2\rfloor-k,\qquad
 \theta_k=-2\pi j_k/r,\qquad \rho_k=e^{i\theta_k}.
\]

These give every `r`th root of unity once. The corresponding actual kernel is

\[
 K_j(n,x)=\Gamma(x)^r\prod_{i=1}^{r-1}\Gamma(A_i n-x+1)
          e^{2\pi i jx}z^{bn-x}.
\]

The vector `I_j(n)` has components

\[
 \frac1{2\pi i}\int_H(bn-x)^hK_j(n,x)\,dx,\qquad 0\le h<r,
\]

on the reference left Hankel contour, with right edge `1/2` and banks at
imaginary heights `±1`. All three defining contour pieces are absolutely
convergent. Put

\[
 c=(z\prod_i A_i)^{1/r},\quad R=n^{1-1/r},\quad
 \varepsilon=n^{-1/r},\quad H_r=z^{bn}\prod_i\Gamma(A_i n+1).
\]

The proved estimates are

\[
 \|I_{j_k}(n)\|=H_r(n)\exp\{-rc\Re(\rho_k)R+E_k(n)\},
 \qquad |E_k(n)|\le C_k n^{1-2/r}
\]

for all sufficiently large `n`. The `r` vector sequences are complex
linearly independent. The `j=0` branch is strongly recessive: every fixed
nonzero combination `S` of the other branches is eventually nonzero and

\[
 n^N\frac{\|I_0(n)\|}{\|S(n)\|}\longrightarrow0\quad(N\in\mathbb N).
\]

The public coefficient type `NonrecessiveBranch r` excludes `j=0`; the
statement does not include an extra recessive coefficient in `S`.

## Off-cut branches

For `−π < θ < π` and `rθ = −2πj`, the limiting phase is

\[
 \phi(s)=s\{r[\log(s/c)-i\theta]-r\}.
\]

Its nonzero saddle is `c exp(iθ)`, with phase value `−rc exp(iθ)`.
Choose `a>0,b` with `(a+ib)^2=c exp(iθ)`. The parabola
`P(t)=(a+it)^2` has a strict global phase maximum at `t=b`, including
angles corresponding to purely imaginary saddles. A small translation
places it through the exact moving saddle. Compact phase gaps control its
finite complement outside a local window.

`FullParabolicContour.lean` proves the exact equality between the reference
Hankel integral and the translated finite parabolic arc plus two horizontal
infinite tails. The tail cutoff is chosen using `ConeTailDecay.lean`, whose
constants are independent of an artificial height cap. This avoids a circular
choice of parabolic cutoff and horizontal-tail threshold.

The local curved Neuschel estimates include the contour Jacobian.
`ParabolicWindowIdentity.lean` identifies these with the actual local
parabolic window; `OffCutGlobalRemainder.lean` controls everything outside
that window by an exponentially smaller remainder.
`OriginalMomentLimits.lean` then proves limits for the original defining
integrals, with one common scalar normalizer per branch:

\[
 \beta_j(n)T_nI_j(n)\longrightarrow
 (1,c\rho_j,\ldots,(c\rho_j)^{r-1}).
\]

At zero polynomial center, `T_n` is diagonal with entries `(-R)^{-h}`.
The limits are for the original index `n`, not merely a shifted subsequence.
Actual saddle-kernel bounds and polynomial conditioning of `T_n` give the
zero-center logarithmic growth (`OffCutGrowth.lean`).
`BranchCenterGrowth.lean` transfers that rate to general `b` using the same
argument as for the boundary branch. `GrowthRates.lean` converts logarithmic
control to the exponential norm estimate in one common lemma.

## Polynomial recentering

The exact kernel relation and the binomial theorem give

\[
 I_b(n)=z^{bn}P(bn)I_0(n),\qquad
 I_0(n)=z^{-bn}P(-bn)I_b(n),
\]

where `P(w)` is the lower triangular Pascal translation matrix. Here the
subscript denotes polynomial center, not Fourier label.
`MomentTranslation.lean` and `PascalTranslation.lean` prove these identities
using absolute convergence and finite-sum Hankel linearity. The bound
`‖P(w)‖ ≤ (1+|w|)^(r−1)` gives only logarithmic losses in norm growth.
`BranchCenterGrowth.lean` applies this to any proved branch rate, including
the even-rank boundary branch.

## Even-rank boundary branch

For even `r=2h`, the balanced label `j=h` has angle `−π`. No principal
logarithm or off-cut saddle theorem is used at that point. Reflection gives
an auxiliary kernel

\[
 B(x)=\pi(\cot(\pi x)+i)Q(x),\quad
 Q(x)=\Gamma(1-x)^{-r}\prod_i\Gamma(A_i n-x+1)z^{bn-x}.
\]

The reflected kernel `Q` is positive on the real axis `x<1`. On the fixed
banks of height one, the lower-bank main term is `2πi Q` and both reflection
errors are small compared with the positive real integral. Real-window
Laplace bounds and global derivative bounds prove growth `+rcR+O(Rε)` for
the auxiliary zeroth moment (`BoundaryGrowth.lean`).

`WeightedIntegralBounds.lean` and `BoundaryMomentUpper.lean` extend the
upper bounds to every polynomial moment: finite windows cost a polynomial
in `R`, and the real exponential tails absorb the polynomial weights.
The fixed finite contour pieces are polynomial relative to `H_r`.
Consequently the entire auxiliary vector has the same growth, with its
zeroth component providing the lower bound (`BoundaryVectorGrowth.lean`).

The exact, integrated finite Fourier identity is

\[
 (2\pi i)^{r-1}\mathbf B
 =\sum_{k=0}^{r-1}(-1)^k\binom{r-1}{k}\mathbf I_{h-k}.
\]

Every term except `I_h` is off-cut and has strictly smaller growth because
its root has real part greater than `−1`.
`EvenBoundaryBranch.lean` recovers the original `I_h` with growth `+rcR`.
No boundary moment limit or unproved contour prescription is assumed.

## Independence and noncancellation

The shared `ThisWork/Noncancellation.lean` gives a uniform lower bound for
matrices converging to a nonsingular Vandermonde matrix. It accepts an
arbitrary vector-space domain, so the first `r−1` moments can be used for
`r−1` off-cut branches of an `r`-component vector.

For any `d≤r` distinct off-cut branches, the actual moment limits imply
sequence independence and the quantitative bound

\[
 |a_j|\|I_j(n)\|\le K n^{3(r-1)}
             \left\|\sum_i a_iI_i(n)\right\|,
\]

uniformly over all coefficient vectors (even coefficients varying with `n`).
At zero center the proof gives the smaller degree `r−1`; recentering adds
only polynomial losses. See `OffCutNoncancellation.lean` and
`CenterNoncancellation.lean`.

In odd rank all branches are off-cut. In even rank, independence of the
`r−1` off-cut branches extends by strict dominance of the remaining boundary
branch (`CanonicalIndependence.lean`). For strong recessiveness, a fixed
combination with nonzero boundary coefficient has the boundary growth rate;
if that coefficient vanishes, the off-cut quantitative bound prevents
cancellation. The positive-real root uniquely maximizes the real part, so
its branch is separated from every such combination.

`GrowthRates.lean` proves the general fact that `exp(−aR+O(Rε))` absorbs every
fixed polynomial for `a>0`. `CanonicalRecessiveness.lean` combines this with
the preceding lower bounds; `MellinBarnesAsymptotics.lean` exposes the complete theorem.
