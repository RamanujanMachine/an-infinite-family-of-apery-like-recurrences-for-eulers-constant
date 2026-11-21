module

public import ThisWork.Trajectory.EqualSlopes
public import ThisWork.Trajectory.Recessiveness

/-! Lemma 8 for trajectories with equal lower slopes `(m,m,m)`.

`equal_lemma8` proves growth and linear independence for every `m ≥ 1`.
The upper-gap parameters `A₁,A₂` and the Meijer G argument `z` remain arbitrary
positive real parameters. The result follows from the original Lemma 8 by exact
reindexing, with independence proved using the normalized moment limits.
`equal_stronglyRecessive` proves superpolynomial separation from every
fixed combination with a nonzero dominant coefficient.
-/
