module

public import ThisWork.Trajectory.EqualSlopes
public import ThisWork.Trajectory.DoubleMinimum
public import ThisWork.Trajectory.ElementaryMode

/-! Lemma 8 for trajectories with lower slopes `(m,m,m+d)`.

* `equal_lemma8` proves growth and independence when `d=0` and `m ≥ 1`.
* `double_lemma8` proves growth and independence when `d ≥ 1` and `m ≥ 1`.

The upper-gap parameters `A₁,A₂` and the Meijer G argument `z` remain arbitrary
positive real parameters throughout the analytic development. In the double-minimum
regime the common factor is `doubleScale`, the saddle coefficient is
`sqrt(A₁*A₂*z/d)`, and the exponential coefficients are `+2,+2,-2` at scale `sqrt(n)`.
The error in the logarithmic growth estimates is `O(log n)`.

Independence also has a separate proof from the common initial Mellin–Barnes state,
which applies to all the trajectory sequences simultaneously. -/
