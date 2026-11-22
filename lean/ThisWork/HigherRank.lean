module

public import ThisWork.HigherRank.EqualSlopes
public import ThisWork.HigherRank.RankThree
public import ThisWork.HigherRank.RankFourPositive
public import ThisWork.HigherRank.PositivePeak
public import ThisWork.HigherRank.Phase
public import ThisWork.HigherRank.Saddles
public import ThisWork.Noncancellation
public import ThisWork.HigherRank.Reflection
public import ThisWork.HigherRank.ReflectedBoundary
public import ThisWork.HigherRank.BoundaryReflectionBounds
public import ThisWork.HigherRank.ReflectedSaddleEquation
public import ThisWork.HigherRank.SaddleEquation
public import ThisWork.HigherRank.ParabolicPhase
public import ThisWork.HigherRank.ParabolicCoordinates
public import ThisWork.HigherRank.ParabolicDeformation
public import ThisWork.HigherRank.ParabolicKernelApproximation
public import ThisWork.HigherRank.ParabolicGap
public import ThisWork.HigherRank.LocalSaddlePhase
public import ThisWork.HigherRank.QuadraticPhase
public import ThisWork.HigherRank.OffCutLocalData
public import ThisWork.HigherRank.HankelDeformation
public import ThisWork.HigherRank.IntegratedTails
public import ThisWork.HigherRank.AnchorTransfer
public import ThisWork.HigherRank.SaddleKernelGrowth
public import ThisWork.HigherRank.FixedBoundaryBanks
public import ThisWork.HigherRank.FixedCompactBounds
public import ThisWork.HigherRank.DominantExtension
public import ThisWork.HigherRank.BoundaryGrowth
public import ThisWork.HigherRank.FullParabolicContour
public import ThisWork.HigherRank.ParabolicTailBounds
public import ThisWork.HigherRank.ParabolicRemainderBounds
public import ThisWork.HigherRank.ParabolicWindowIdentity
public import ThisWork.HigherRank.Lemma8

/-! Arbitrary-rank Lemma 8 for equal lower slopes and symbolic positive `z`.
`HigherRank.lemma8` proves growth of every original Mellin–Barnes vector
integral, complex sequence independence, and strong recessiveness against
all nontrivial fixed combinations of the other branches. Off-cut branches
use full parabolic contour deformation and uniform Laplace estimates;
the even-rank boundary branch is recovered by reflection and a finite
Fourier identity. The existing rank-three theorem statements are preserved. -/
