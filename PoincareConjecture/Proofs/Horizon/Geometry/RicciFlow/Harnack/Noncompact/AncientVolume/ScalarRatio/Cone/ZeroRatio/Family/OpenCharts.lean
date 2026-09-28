import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Family.Embedding
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
  {r : ℝ} (hr : 0 < r)

include hr in
private theorem smallBall_subset_coordinateBall :
    Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4) ⊆ Metric.closedBall 0 r :=
  (Metric.ball_subset_ball (by linarith : r / 4 ≤ r)).trans Metric.ball_subset_closedBall

def uniformBallRestriction {B : Type*} (e : MetricCoordinateBall g r → B) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4) → B :=
  fun x => e ⟨x.val, smallBall_subset_coordinateBall hr x.property⟩

theorem uniformBallRestriction_dist {B : Type*} [MetricSpace B]
    (e : MetricCoordinateBall g r → B) (he : Isometry e)
    (x y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)) :
    dist (g.uniformBallRestriction hr e x) (g.uniformBallRestriction hr e y) =
      (g.edist x.val y.val).toReal :=
  he.dist_eq _ _

theorem uniformBallRestriction_edist {B : Type*} [MetricSpace B]
    (e : MetricCoordinateBall g r → B) (he : Isometry e)
    (x y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (r / 4)) :
    EDist.edist (g.uniformBallRestriction hr e x) (g.uniformBallRestriction hr e y) =
      g.edist x.val y.val := by
  rw [edist_dist, g.uniformBallRestriction_dist hr e he,
    ENNReal.ofReal_toReal (g.edist_ne_top _ _)]

private theorem coordinateBall_dist_bounds
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ g.tangentNorm x v ∧ g.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (x y : MetricCoordinateBall g r) :
    ‖y.val - x.val‖ / 2 ≤ dist x y ∧ dist x y ≤ 3 * ‖y.val - x.val‖ / 2 := by
  obtain ⟨hlo, hhi⟩ := g.edist_bounds_of_uniform_tangentNorm_bounds hbound x.val y.val
  constructor
  · simpa only [MetricCoordinateBall.dist_eq,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ ‖y.val - x.val‖ / 2)] using
      ENNReal.toReal_mono (g.edist_ne_top _ _) hlo
  · simpa only [MetricCoordinateBall.dist_eq,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 3 * ‖y.val - x.val‖ / 2)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hhi

theorem isOpenEmbedding_uniformBallRestriction {B : Type*} [MetricSpace B]
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ g.tangentNorm x v ∧ g.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (e : MetricCoordinateBall g r → B) (he : Isometry e)
    (hcover : Metric.ball (e ⟨0, Metric.mem_closedBall_self hr.le⟩) r ⊆ range e) :
    Topology.IsOpenEmbedding (g.uniformBallRestriction hr e) := by
  have hemb : Topology.IsEmbedding (g.uniformBallRestriction hr e) :=
    he.isEmbedding.comp ((MetricCoordinateBall.toClosedBallHomeomorph g r).symm.isEmbedding.comp
      (Topology.IsEmbedding.inclusion (smallBall_subset_coordinateBall hr)))
  refine ⟨hemb, Metric.isOpen_iff.mpr ?_⟩
  rintro _ ⟨x, rfl⟩
  let x' : MetricCoordinateBall g r := ⟨x.val, smallBall_subset_coordinateBall hr x.property⟩
  let o : MetricCoordinateBall g r := ⟨0, Metric.mem_closedBall_self hr.le⟩
  have hx : ‖x.val‖ < r / 4 := by
    simpa only [Metric.mem_ball, dist_zero_right] using x.property
  have hdist : dist (e x') (e o) < r := by
    have h := (coordinateBall_dist_bounds g hbound o x').2
    simp only [o, x', sub_zero] at h
    rw [he.dist_eq, dist_comm]
    linarith
  let δ := min ((r - dist (e x') (e o)) / 2) ((r / 4 - ‖x.val‖) / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hzdist : dist z (e x') < δ := hz
  have hδ₁ : δ ≤ (r - dist (e x') (e o)) / 2 := min_le_left _ _
  have hδ₂ : δ ≤ (r / 4 - ‖x.val‖) / 4 := min_le_right _ _
  have hzcover : z ∈ Metric.ball (e o) r := by
    rw [Metric.mem_ball]
    have htriangle := dist_triangle z (e x') (e o)
    linarith
  obtain ⟨y, hy⟩ := hcover hzcover
  have hyclose : ‖y.val - x.val‖ / 2 ≤ dist z (e x') := by
    have h := (coordinateBall_dist_bounds g hbound x' y).1
    rw [← he.dist_eq, hy, dist_comm] at h
    exact h
  have hynorm : ‖y.val‖ < r / 4 := by
    have htriangle := norm_add_le (y.val - x.val) x.val
    rw [sub_add_cancel] at htriangle
    linarith
  refine ⟨⟨y.val, ?_⟩, ?_⟩
  · simpa only [Metric.mem_ball, dist_zero_right] using hynorm
  · exact hy

theorem ball_subset_range_uniformBallRestriction {B : Type*} [MetricSpace B]
    (hbound : ∀ x v : EuclideanSpace ℝ (Fin n),
      ‖v‖ / 2 ≤ g.tangentNorm x v ∧ g.tangentNorm x v ≤ 3 * ‖v‖ / 2)
    (e : MetricCoordinateBall g r → B) (he : Isometry e)
    (hcover : Metric.ball (e ⟨0, Metric.mem_closedBall_self hr.le⟩) r ⊆ range e) :
    Metric.ball (e ⟨0, Metric.mem_closedBall_self hr.le⟩) (r / 8) ⊆
      range (g.uniformBallRestriction hr e) := by
  intro z hz
  obtain ⟨y, hy⟩ := hcover (Metric.ball_subset_ball (by linarith : r / 8 ≤ r) hz)
  let o : MetricCoordinateBall g r := ⟨0, Metric.mem_closedBall_self hr.le⟩
  have h := (coordinateBall_dist_bounds g hbound o y).1
  simp only [o, sub_zero] at h
  rw [← he.dist_eq, hy, dist_comm] at h
  have hzdist : dist z (e o) < r / 8 := hz
  have hynorm : ‖y.val‖ < r / 4 := by linarith
  refine ⟨⟨y.val, ?_⟩, ?_⟩
  · simpa only [Metric.mem_ball, dist_zero_right] using hynorm
  · exact hy

end PoincareConjecture.RiemannianMetric
