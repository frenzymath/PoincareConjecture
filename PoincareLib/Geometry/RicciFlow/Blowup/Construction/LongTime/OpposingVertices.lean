import PoincareLib.Geometry.Riemannian.Soul.CompleteGeometry
import PoincareLib.Geometry.Riemannian.Compactness.IntrinsicMetric

/-!
# Three opposing points from one minimizing ray

The vertex selection used in Morgan--Tian Claim 11.14, p. 275, needs only
one sufficiently distant point. A ray gives the stronger distance equality
for that selected point, without the all-far-points assertion of Lemma 11.13.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M30

/-- One minimizing ray supplies opposing vertices beyond any prescribed
additive distance error (the vertex step of Claim 11.14, p. 275). -/
theorem exists_opposing_vertices_of_metricComplete
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    (p : M) (L : ℝ) :
    ∃ d : ℝ, max 1 (2 * L) < d ∧ ∃ y z : M,
      (g.edist p y).toReal = d ∧
      (g.edist y z).toReal = d ∧
      (g.edist p z).toReal = 2 * d := by
  let : MetricSpace M := g.toMetricSpace
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  let : ProperSpace M := g.properSpace_of_complete hcomplete hdist
  obtain ⟨ray, hray, hbase, _himage⟩ :=
    Poincare.Riemannian.Soul.exists_ray_in_closed_set (K := (univ : Set M))
      isClosed_univ (noncompact_univ M) (p := p) (by
        intro q _
        obtain ⟨curve, h0, h1, hmin, _hgeo⟩ :=
          g.exists_smooth_metric_segment_of_complete hcomplete hdist p q
        exact ⟨curve, h0, h1, hmin, fun _ _ => mem_univ _⟩)
  let d := max 1 (2 * L) + 1
  have hd : 0 < d := by dsimp only [d]; linarith [le_max_left 1 (2 * L)]
  have h2d : 0 < 2 * d := mul_pos (by norm_num) hd
  refine ⟨d, lt_add_one _, ray d, ray (2 * d), ?_, ?_, ?_⟩
  · rw [← hdist, ← hbase, hray (show 0 ≤ (0 : ℝ) from le_rfl) hd.le,
      zero_sub, abs_neg, abs_of_pos hd]
  · rw [← hdist, hray hd.le h2d.le, show d - 2 * d = -d by ring,
      abs_neg, abs_of_pos hd]
  · rw [← hdist, ← hbase, hray (show 0 ≤ (0 : ℝ) from le_rfl) h2d.le,
      zero_sub, abs_neg, abs_of_pos h2d]

end PoincareMT.M30
