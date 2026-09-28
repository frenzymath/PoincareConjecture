import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.LimitTransport







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem eventually_relative_edist_le
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    (hmetric : ∀ k,
      (F (G.subsequence k)).metricAt 0 = (H (L.subsequence k)).metricAt 0)
    {r D : ℝ} (hr : 0 < r) (hD : 1 < D) :
    ∀ᶠ k in atTop,
      let f := fun x ↦ ((L.embedding k).inverse
        (0, ((G.embedding k).toFun (0, x)).2)).2
      ∀ x ∈ G.limitFlow.ballAt 0 r, ∀ y ∈ G.limitFlow.ballAt 0 r,
        (L.limitFlow.metricAt 0).edist (f x) (f y) ≤
          ENNReal.ofReal (D ^ 2) * (G.limitFlow.metricAt 0).edist x y := by
  have h3r : 0 < 3 * r := mul_pos (by norm_num) hr
  filter_upwards [eventually_relative_map_smooth C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource h3r,
    eventually_relative_tangentNorm_bounds C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource hmetric h3r hD] with k hk hnorm
  dsimp only at hk hnorm ⊢
  intro x hx y hy
  exact (G.limitFlow.metricAt 0).edist_image_le_mul_edist_of_tangentNorm_le_on_ball
    (L.limitFlow.metricAt 0) _ G.limitFlow.base hr (sq_pos_of_pos (zero_lt_one.trans hD))
    (fun z hz ↦ (hk.2.1 z hz).of_le (by simp))
    (fun z hz v ↦ (hnorm z hz v).1) hx hy

end PoincareConjecture.PointedGeometricConvergence
