import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.CompleteGeometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.NormalChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem eq_singleton_of_isolated_of_every_geodesic
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) {S : Set M}
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    {q : M} (hq : q ∈ S) {U : Set M} (hU : U ∈ 𝓝 q)
    (hisolated : ∀ x ∈ S, x ∈ U → x = q) : S = {q} := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace g.edist_ne_top
  have hdist (x y : M) : dist x y = (g.edist x y).toReal := rfl
  apply Set.Subset.antisymm _ (singleton_subset_iff.mpr hq)
  intro y hy
  by_contra hyq
  have hneq : q ≠ y := fun h => hyq (mem_singleton_iff.mpr h.symm)
  have hd : 0 < dist q y := dist_pos.mpr hneq
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨curve, h0, h1, hmin, hgeo⟩ :=
    g.exists_smooth_metric_segment_of_complete hcomplete hdist q y
  let t : ℝ := min (δ / 2) (dist q y / 2)
  have htpos : 0 < t := lt_min (half_pos hδ) (half_pos hd)
  have htδ : t < δ := (min_le_left _ _).trans_lt (by linarith)
  have ht : t ∈ Icc 0 (dist q y) :=
    ⟨htpos.le, (min_le_right _ _).trans (by linarith)⟩
  have hzero : (0 : ℝ) ∈ Icc 0 (dist q y) := ⟨le_rfl, hd.le⟩
  have hmem : curve t ∈ S :=
    hconv curve 0 (dist q y) hgeo (h0.symm ▸ hq) (h1.symm ▸ hy) ht
  have hdt : dist (curve t) q = t := by
    simpa only [h0, sub_zero, abs_of_pos htpos] using hmin ht hzero
  have heq : curve t = q := hisolated (curve t) hmem (hball (by
    simpa only [mem_ball, hdt] using htδ))
  rw [heq, dist_self] at hdt
  exact htpos.ne' hdt.symm

theorem eq_singleton_of_zero_local_span_of_every_geodesic
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g) {S : Set M}
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    {q : M} (hq : q ∈ S)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hezero : e 0 = q) {r : ℝ} (hr : 0 < r)
    (hball : Metric.ball 0 r ⊆ e.source)
    (hspan : Submodule.span ℝ (Metric.ball 0 r ∩ e ⁻¹' S) = ⊥) : S = {q} := by
  have hqimage : q ∈ e '' Metric.ball 0 r := ⟨0, mem_ball_self hr, hezero⟩
  apply g.eq_singleton_of_isolated_of_every_geodesic hcomplete hconv hq
    ((e.isOpen_image_of_subset_source isOpen_ball hball).mem_nhds hqimage)
  intro x hx hximage
  obtain ⟨v, hv, rfl⟩ := hximage
  have hbot : v ∈ (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin n))) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨hv, hx⟩
  have heqzero : v = 0 := hbot
  rw [heqzero, hezero]

end PoincareConjecture.RiemannianMetric
