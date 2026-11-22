# Equal lower slopes in rank four

This investigation extends the analytic question behind Lemma 8, with arbitrary
fixed real `z > 0`. It does not assert a higher-rank Lean asymptotics theorem yet.
The existing rank-three theorem and proof are unchanged.

## Proposed statement

For rank `r`, take equal lower slopes `(m,...,m)`, `m >= 1`, and upper gaps
`A_i = m-a_i > 0`, `1 <= i <= r-1`. Write

\[
 H_r(n,z)=z^{mn}\prod_{i=1}^{r-1}\Gamma(A_i n+1),\qquad
 c=\left(z\prod_i A_i\right)^{1/r},\qquad R=n^{(r-1)/r}.
\]

The kernel and moment vectors are

\[
 K_j(n,x)=\Gamma(x)^r\prod_i\Gamma(A_i n-x+1)
             e^{2\pi i jx}z^{mn-x},\qquad
 I_j^{(h)}=\frac1{2\pi i}\int_H(mn-x)^hK_j(n,x)\,dx.
\]

Here `H` is the existing left Hankel contour. Integer labels are meaningful
independently of whether a corresponding vertical contour converges. The
limiting saddles are `c rho`, `rho^r = 1`. The target norm statement for a
suitable basis indexed by these saddles is

\[
 \log\|I_\rho(n,z)\|=\log H_r(n,z)
 -rc\operatorname{Re}(\rho)n^{(r-1)/r}+O(n^{(r-2)/r}).
\]

All constants may depend on the fixed positive real parameters; no uniformity
as `z -> 0` or `z -> infinity` is claimed. Rational values of `z` are only
computational samples, not a restriction on the analytic statement.

Equal slopes `m > 1` reduce exactly to `m = 1`: replace `n` by `mn` and every
`A_i` by `A_i/m`. This is now proved in Lean for arbitrary rank.

## Rank-four predictions and independent checks

Put `S_1 = sum_i 1/A_i` and `S_2 = sum_i 1/A_i^2`. The predicted scalar
exponent, through the last diverging correction, is

\[
 -4c\rho n^{3/4}
 +\frac{S_1c^2\rho^2}{2}n^{1/2}
 +\left(\frac{S_2}{6}-\frac{S_1^2}{8}\right)c^3\rho^3 n^{1/4}.
\]

The scalar saddle prefactor has power `n^(-9/8)`. The norm of the vector of
moments of degrees zero through three has power `n^(15/8)`, because its last
component contributes `(mn)^3`. Constants multiplying these expressions have
not been proved here.

For the base trajectory `(0,0,0;1,1,1,1)`, the formal scalar recurrence modes,
up to constant factors and relative corrections, are

\[
 \frac{z^n(n!)^3}{n^{9/8}}
 \begin{cases}
 \exp(-4z^{1/4}n^{3/4}+\tfrac32z^{1/2}n^{1/2}
                         -\tfrac58z^{3/4}n^{1/4}),\\
 \exp(-\tfrac32z^{1/2}n^{1/2}
          \mathbin{\pm} i(4z^{1/4}n^{3/4}-\tfrac58z^{3/4}n^{1/4})),\\
 \exp(+4z^{1/4}n^{3/4}+\tfrac32z^{1/2}n^{1/2}
                         +\tfrac58z^{3/4}n^{1/4}).
 \end{cases}
\]

The scripts in `rank_four/` use ramanujantools 0.0.8 and exact, raw trajectory
matrices. They never apply `as_polynomial()`, which would change the common
growth factor. Its recurrence convention is backward shifts: the coefficients
returned from matrix companionization are shifted by `n -> n-4` before
asymptotic analysis. Omitting that adjustment adds 12 to the base example's
reported power of `n`, without changing the stretched exponentials.

`study.py` tests the base example at `z = 1/16, 1, 16`, an unequal upper-slope
example, and equal lower slope two. Precision failures are recorded, not
discarded. The reducer did not resolve the lower-slope-two example at the
tested precisions; exact reindexing and the separate numerical checks cover
that example without interpreting a failed reducer as mathematical evidence.

`validate.py` independently computes initial Barnes residues and propagates
them by exact rational matrix walks. At depths `10, 40, 100, 200`, the positive
series below agrees with propagation to approximately 400 digits for three
trajectory/argument pairs, including unequal upper slopes and `m = 2`.
The canonical initial residues and propagation also agree with a direct
Meijer G evaluation at depth ten to approximately 380 digits. These are
numerical checks, not substitutes for a proof.

## Two changes to the contour proof

**Imaginary saddles.** The principal-log limiting phase has
`phi''(s) = 4/s`. At `s = +/- i c` its second derivative is purely imaginary.
A horizontal segment therefore has no quadratic decay. In fact, along
`s = u-ic` the derivative of the real phase is
`4 log(sqrt(u^2+c^2)/c)`, so that saddle is not a local maximum on the horizontal
line. The current horizontal-tail geometry cannot simply be reused.

Local descent directions can be chosen at angle `pi/4` for `s = -ic` and
`-pi/4` for `s = +ic`. The canonical saddle uses a vertical segment. Neuschel's
general contour machinery supports these directions, but the connecting
segments and global bounds still need to be proved.

**Negative-real saddle.** The fourth saddle, `-c`, lies on the logarithmic cut
and on the ray containing the Gamma poles. Rotating the logarithm does not
justify a pole-free saddle neighborhood. The boundary Fourier label `j = 2`
also fails vertical-contour convergence: seven Gamma factors give
`exp(-7 pi |Im x|/2)`, while its twist grows by `exp(4 pi |Im x|)` on one end.
The fixed-height Hankel contour still converges, but a direct principal-log
saddle proof does not apply.

## A positive series for the fourth mode

There is a way to avoid both boundary difficulties for that mode. Replace
three factors `Gamma(x)` by reciprocal Gamma factors, using reflection, and
insert `exp(i pi x)`. Away from the poles, the exact integrand identity is

\[
 B_n(x):=
 \frac{\Gamma(x)\prod_{i=1}^{3}\Gamma(A_i n-x+1)}{\Gamma(1-x)^3}
 e^{i\pi x}z^{mn-x}
 =\frac{K_2-3K_1+3K_0-K_{-1}}{(2\pi i)^3}.
\]

Closing the left Hankel contour gives the proposed exact series identity

\[
 F_+^{(h)}(n,z)=z^{mn}\sum_{\ell\ge0}(mn+\ell)^h z^\ell
       \frac{\prod_i\Gamma(A_i n+\ell+1)}{(\ell!)^4},
 \qquad 0\le h\le3.
\]

Each summand is positive. The signs from the residue of `Gamma(x)` and from
`exp(i pi x)` cancel at `x = -ell`. For each fixed `n`, closure on negative
half-integers is justified by inverse-factorial decay; the other Gamma poles
are to the right of the reference contour. This contour argument has not yet
been formalized.

For the scalar summands `t_ell`, the exact ratio is

\[
 \frac{t_{\ell+1}}{t_\ell}
 =\frac{z\prod_i(A_i n+\ell+1)}{(\ell+1)^4}
 =\frac{z}{\ell+1}\prod_i\left(1+\frac{A_i n}{\ell+1}\right).
\]

It decreases with `ell`, tends to zero, and crosses one near
`ell = c n^(3/4)`. Thus this is a positive discrete Laplace problem with a
unique peak, representing the missing saddle by the positive variable
`ell = -x`. Its predicted growth is `+4c n^(3/4)`, and its normalized `x`
moments tend to `(-c)^h`. Positivity, the exact ratio formula, and summability
of the scalar series are now proved in Lean for arbitrary positive real
`A_i,z`; the large-`n` asymptotics and moment limits are not yet proved.

The same construction is available in every even rank: replace `r-1` Gamma
factors and use `exp(i pi x)`. Its Fourier expansion uses integer labels, and
its positive series has denominator `(ell!)^r`. Odd rank has no negative-real
root among the relevant saddles and does not need this boundary replacement.

## Independence and the earlier cancellation gap

Use three contour modes with saddles `c,ic,-ic` and the positive series mode
with saddle `-c`. After applying the common binomial moment transform and
normalizing each mode, the target moment columns are

\[
 (1,s,s^2,s^3)^T,\qquad s\in\{c,ic,-ic,-c\}.
\]

Their Vandermonde matrix is invertible. The existing Lean theorem
`eventually_linearIndependent_of_moment_limits` already supports arbitrary
dimension. However, sequence independence alone is insufficient for strong
recessiveness. The quantitative bound from the bounded inverse of this
limiting moment matrix is now proved generically in `Noncancellation.lean`;
its application still requires the integral moment limits. The common moment transform
and its inverse have only polynomial growth, so this bound prevents
superpolynomial cancellation in fixed combinations of the other modes.

This supplies a specific route to proving that the canonical `+c` saddle is
strongly recessive. None of those higher-rank asymptotic conclusions are
being inferred solely from the formal recurrence output.

## Remaining proof work

1. Tilted polygonal contours and global phase bounds for the imaginary pair.
2. Hankel-to-positive-series identity, followed by discrete Laplace growth
   and normalized moments, including moments of degrees one through three.
3. The four-mode moment limits, independence, and a quantitative
   noncancellation bound.
4. Only after rank four works, generalize the contour construction and the
   even-rank series argument to arbitrary rank.

The Lean additions so far are under `ThisWork/HigherRank/`. They provide
definitions, exact equal-slope reindexing, exact rank-three compatibility,
and convergence of the positive series and all polynomial moments in arbitrary
rank. The rank-four series results are specializations of those generic proofs.
See [general_rank.md](general_rank.md) for the broader analytic development.
These results introduce no
new axioms or unproved assumptions. The existing rank-three results remain
the complete formalized asymptotics theorems.
