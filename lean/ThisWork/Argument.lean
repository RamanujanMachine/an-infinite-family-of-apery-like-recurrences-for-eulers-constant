module

public import ThisWork.LimitingPhase

/-! The fixed positive real Meijer G argument used by the analytic development. -/

@[expose] public section
namespace ThisWork

class PositiveArgument where
  value : ℝ
  positive : 0 < value

end ThisWork
