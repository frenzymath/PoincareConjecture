import Mathlib

/-! # The standard three-sphere -/

namespace PoincareMT

abbrev ThreeSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

end PoincareMT
