import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRayChord
import PoincareConjecture.Proofs.M28.Mathlib.ChordConeDistance

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

universe u

namespace PoincareConjecture.M28

theorem metricEndRay_chordConeTriangle
    {X : Type u} [MetricSpace X]
    {E : UniformSpace.Completion X} {alpha : ℝ}
    [PseudoMetricSpace (MetricEndRay E alpha)]
    (hscaled : ∀ P Q : MetricEndRay E alpha, ∀ r s : ℝ, 0 < r → 0 < s → Tendsto
      (fun h : ℝ => dist (P.point (h * r)) (Q.point (h * s)) / h)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt ((r - s) ^ 2 + r * s * dist P Q ^ 2)))) :
    ∀ P Q R : MetricEndRay E alpha, ∀ r s t : ℝ, 0 < r → 0 < s → 0 < t →
      chordConeDistance r t (dist P R) ≤
        chordConeDistance r s (dist P Q) + chordConeDistance s t (dist Q R) := by
  intro P Q R r s t hr hs ht
  apply le_of_tendsto_of_tendsto (hscaled P R r t hr ht)
    ((hscaled P Q r s hr hs).add (hscaled Q R s t hs ht))
  filter_upwards [self_mem_nhdsWithin] with h hh
  simpa only [add_div] using div_le_div_of_nonneg_right
    (dist_triangle (P.point (h * r)) (Q.point (h * s)) (R.point (h * t))) hh.le

end PoincareConjecture.M28
