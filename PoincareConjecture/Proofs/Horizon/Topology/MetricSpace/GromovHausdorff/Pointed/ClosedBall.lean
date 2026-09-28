





import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Distance
open Set Metric

namespace Poincare.GromovHausdorff

universe u


def closedBallModel (X : BasedMetricSpaceBundle.{u}) (r : ℝ) (hr : 0 ≤ r) :
    FiniteDiameterBasedMetricSpace.{u} :=
  { carrier := Metric.closedBall X.base r
    metric := inferInstance
    base := ⟨X.base, Metric.mem_closedBall_self hr⟩
    finite_diameter := by
      refine ⟨2 * r, ?_⟩
      intro p q
      change dist p.1 q.1 ≤ 2 * r
      have hp := Metric.mem_closedBall.mp p.2
      have hq := Metric.mem_closedBall.mp q.2
      calc
        dist p.1 q.1 ≤ dist p.1 X.base + dist X.base q.1 :=
          dist_triangle _ _ _
        _ ≤ r + r := add_le_add hp (by simpa [dist_comm] using hq)
        _ = 2 * r := by ring }



def closedBallModelInclusion
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    (closedBallModel X r hr).carrier → (closedBallModel X s hs).carrier :=
  fun p => ⟨p.1, le_trans p.2 hrs⟩

theorem closedBallModelInclusion_isometry
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    Isometry (closedBallModelInclusion X r s hr hs hrs) := by
  intro p q
  rfl

theorem closedBallModelInclusion_base
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    closedBallModelInclusion X r s hr hs hrs (closedBallModel X r hr).base =
      (closedBallModel X s hs).base := by
  apply Subtype.ext
  rfl

end Poincare.GromovHausdorff
