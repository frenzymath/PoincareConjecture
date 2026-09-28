import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Distance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem eventually_relative_left_inverse
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ k in atTop,
      let f := fun x ↦ ((L.embedding k).inverse
        (0, ((G.embedding k).toFun (0, x)).2)).2
      let g := fun y ↦ ((G.embedding k).inverse
        (0, ((L.embedding k).toFun (0, y)).2)).2
      ∀ x ∈ G.limitFlow.ballAt 0 r, g (f x) = x := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    ((G.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hGcomplete
      G.limitFlow.base r)
  filter_upwards [eventually_relative_map_smooth C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource hr, eventually_ge_atTop j] with k hk hjk
  dsimp only at hk ⊢
  intro x hx
  rw [hk.2.2 x hx]
  have hxE : x ∈ G.exhaustion k := G.exhaustion_monotone hjk (hj (subset_closure hx))
  have htime : (G.embedding k).toFun (0, x) =
      (0, ((G.embedding k).toFun (0, x)).2) :=
    Prod.ext ((G.embedding k).time_preserving 0 x) rfl
  rw [← htime]
  exact congrArg Prod.snd ((G.embedding k).left_inverse (0, x) ⟨hGtime, hxE⟩)

theorem eventually_relative_edist_bounds
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
            ENNReal.ofReal (D ^ 2) * (G.limitFlow.metricAt 0).edist x y ∧
          (G.limitFlow.metricAt 0).edist x y ≤
            ENNReal.ofReal (D ^ 2) * (L.limitFlow.metricAt 0).edist (f x) (f y) := by
  filter_upwards [eventually_relative_edist_le C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource hmetric hr hD,
    eventually_relative_edist_le C H F L G hLtime hGtime hLcomplete hGcomplete
      (fun k r ↦ (hsource k r).symm) (fun k ↦ (hmetric k).symm)
      (mul_pos (by norm_num : (0 : ℝ) < 4) hr) hD,
    eventually_relative_map_smooth C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource hr,
    eventually_relative_left_inverse C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource hr] with k hforward hback hmap hinverse
  dsimp only at hforward hback hmap hinverse ⊢
  intro x hx y hy
  refine ⟨hforward x hx y hy, ?_⟩
  have hb := hback _ (hmap.1 hx) _ (hmap.1 hy)
  simpa only [hinverse x hx, hinverse y hy] using hb

end PoincareConjecture.PointedGeometricConvergence
