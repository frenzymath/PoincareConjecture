import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring










set_option autoImplicit false

set_option maxSynthPendingDepth 8

namespace ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G H : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]



theorem norm_bilinear_transport_le (L : E →L[𝕜] F) (K : G →L[𝕜] H)
    (A : E →L[𝕜] E →L[𝕜] H) (B : F →L[𝕜] F →L[𝕜] G)
    (h : ∀ u v, A u v = K (B (L u) (L v))) :
    ‖A‖ ≤ ‖K‖ * ‖B‖ * ‖L‖ ^ 2 := by
  apply A.opNorm_le_bound₂ (by positivity)
  intro u v
  rw [h]
  calc
    _ ≤ ‖K‖ * ‖B (L u) (L v)‖ := K.le_opNorm _
    _ ≤ ‖K‖ * (‖B‖ * ‖L u‖ * ‖L v‖) :=
      mul_le_mul_of_nonneg_left (B.le_opNorm₂ _ _) (norm_nonneg _)
    _ ≤ ‖K‖ * (‖B‖ * (‖L‖ * ‖u‖) * (‖L‖ * ‖v‖)) := by
      gcongr
      · exact L.le_opNorm u
      · exact L.le_opNorm v
    _ = (‖K‖ * ‖B‖ * ‖L‖ ^ 2) * ‖u‖ * ‖v‖ := by ring



theorem norm_trilinear_transport_le (L : E →L[𝕜] F) (K : G →L[𝕜] H)
    (A : E →L[𝕜] E →L[𝕜] E →L[𝕜] H)
    (B : F →L[𝕜] F →L[𝕜] F →L[𝕜] G)
    (h : ∀ u v w, A u v w = K (B (L u) (L v) (L w))) :
    ‖A‖ ≤ ‖K‖ * ‖B‖ * ‖L‖ ^ 3 := by
  apply A.opNorm_le_bound (by positivity)
  intro u
  apply (A u).opNorm_le_bound₂ (by positivity)
  intro v w
  rw [h]
  calc
    _ ≤ ‖K‖ * ‖B (L u) (L v) (L w)‖ := K.le_opNorm _
    _ ≤ ‖K‖ * (‖B‖ * ‖L u‖ * ‖L v‖ * ‖L w‖) :=
      mul_le_mul_of_nonneg_left
        ((B (L u) (L v)).le_of_opNorm_le (B.le_opNorm₂ (L u) (L v)) (L w))
        (norm_nonneg _)
    _ ≤ ‖K‖ * (‖B‖ * (‖L‖ * ‖u‖) * (‖L‖ * ‖v‖) * (‖L‖ * ‖w‖)) := by
      gcongr
      · exact L.le_opNorm u
      · exact L.le_opNorm v
      · exact L.le_opNorm w
    _ = (‖K‖ * ‖B‖ * ‖L‖ ^ 3) * ‖u‖ * ‖v‖ * ‖w‖ := by ring

end ContinuousLinearMap
