import PoincareLib.Geometry.RicciFlow.Extinction.Width.Transport.Event.Geometry
import PoincareLib.Geometry.Riemannian.Metric.Induced.Complete

/-!
# Pre-surgery metric calibration and comparison maps

The ordinary transport into the surgery parent preserves the pulled-back
metric. Composing it with an M57 smooth approximant therefore retains that
approximant's distance factor and gives the explicit filling transport used
in Morgan--Tian Claim 18.21, pp. 432--433.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT

variable {M P N : Type u}
  [TopologicalSpace M] [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  [TopologicalSpace P] [ChartedSpace LoopAmbient P] [IsManifold (𝓡 3) ∞ P]
  [TopologicalSpace N] [ChartedSpace LoopAmbient N] [IsManifold (𝓡 3) ∞ N]

/-- A metric-calibrated precomposition retains the comparison map's distance factor. -/
theorem m67_distance_bound_comp_of_pullback
    (g : RiemannianMetric 3 M) (p : RiemannianMetric 3 P) (h : RiemannianMetric 3 N)
    (e : ContinuousMap M P) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (hmetric : ∀ x v w, p.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
      (mfderiv (𝓡 3) (𝓡 3) e x w) = g.inner x v w)
    (f : ContinuousMap P N) {L : ℝ}
    (hbound : ∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal L * p.edist x y)
    (x y : M) :
    h.edist ((f.comp e) x) ((f.comp e) y) ≤ ENNReal.ofReal L * g.edist x y := by
  exact (hbound (e x) (e y)).trans
    (mul_le_mul_right (g.edist_map_le_of_metric_pullback p he
      (fun x v w => (hmetric x v w).symm) x y) _)

/-- The calibrated pre-time comparison gives actual disks with quadratic area loss. -/
theorem m67_filling_transport_comp_of_pullback [T2Space M] [T2Space N]
    (g : RiemannianMetric 3 M) (p : RiemannianMetric 3 P) (h : RiemannianMetric 3 N)
    (e : ContinuousMap M P) (he : ContMDiff (𝓡 3) (𝓡 3) ∞ e)
    (hmetric : ∀ x v w, p.inner (e x) (mfderiv (𝓡 3) (𝓡 3) e x v)
      (mfderiv (𝓡 3) (𝓡 3) e x w) = g.inner x v w)
    (f : ContinuousMap P N) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (post : M59LoopPostcomposition (f.comp e))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ x y, h.edist (f x) (f y) ≤ ENNReal.ofReal L * p.edist x y)
    (gamma : C1FreeLoopSpace (M := M)) (D : LipschitzSpanningDisk g gamma) :
    ∃ E : LipschitzSpanningDisk h (post.map gamma), E.area ≤ L ^ 2 * D.area :=
  m67_filling_transport_of_lipschitz g h (f.comp e) (hf.comp he) post hL
    (m67_distance_bound_comp_of_pullback g p h e he hmetric f hbound) gamma D

end PoincareMT
