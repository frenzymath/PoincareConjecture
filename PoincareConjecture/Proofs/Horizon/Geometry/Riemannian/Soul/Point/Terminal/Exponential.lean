import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.MaximalDisk
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.LocalSpan
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.TwoGeodesics

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

@[simp] theorem globalExponential_zero (g : RiemannianMetric n M)
    (hc : MetricComplete g) (q : M) : g.globalExponential hc q 0 = q := by
  simpa only [zero_smul] using
    (g.globalExponential_smul_eq_globalGeodesic hc q 0 0).trans
      (g.globalGeodesic_spec hc q 0).2.1

namespace ContainedNormalDisk

variable {g : RiemannianMetric n M} {S S' : Set M}

theorem chart_eq_globalExponential (D : ContainedNormalDisk g S)
    (hc : MetricComplete g) {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ D.chart.source) :
    D.chart v = g.globalExponential hc D.center v := by
  have hvball : v ∈ Metric.ball 0 D.radius := D.source_eq ▸ hv
  exact (g.globalExponential_eq_radial_exponential hc D.center D.radius_pos
    (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin n))) D.chart D.map_zero
    D.derivative_zero D.radial_geodesic hvball).symm

theorem chart_eq_of_center_eq (D : ContainedNormalDisk g S)
    (D' : ContainedNormalDisk g S') (hc : MetricComplete g)
    (hcenter : D.center = D'.center) {v : EuclideanSpace ℝ (Fin n)}
    (hv : v ∈ D.chart.source) (hv' : v ∈ D'.chart.source) :
    D.chart v = D'.chart v := by
  rw [D.chart_eq_globalExponential hc hv, D'.chart_eq_globalExponential hc hv', hcenter]

theorem globalExponential_image_disk_subset (D : ContainedNormalDisk g S)
    (hc : MetricComplete g) :
    g.globalExponential hc D.center ''
      (Metric.ball 0 D.radius ∩ (D.plane : Set (EuclideanSpace ℝ (Fin n)))) ⊆ S := by
  rintro x ⟨v, hv, rfl⟩
  rw [← D.chart_eq_globalExponential hc (D.source_eq.symm ▸ hv.1)]
  exact D.contained ⟨v, hv, rfl⟩

theorem local_span_eq_globalExponential (D : ContainedNormalDisk g S)
    (hc : MetricComplete g) (T : Set M) {r : ℝ} (hr : r ≤ D.radius) :
    Submodule.span ℝ (Metric.ball 0 r ∩ D.chart ⁻¹' T) =
      Submodule.span ℝ (Metric.ball 0 r ∩ g.globalExponential hc D.center ⁻¹' T) := by
  apply congrArg (Submodule.span ℝ)
  ext v
  by_cases hv : v ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r
  · have hsource : v ∈ D.chart.source := D.source_eq.symm ▸ ball_subset_ball hr hv
    simp only [mem_inter_iff, mem_preimage, hv, true_and,
      D.chart_eq_globalExponential hc hsource]
  · simp only [mem_inter_iff, hv, false_and]

theorem local_span_eq_of_center_eq (D : ContainedNormalDisk g S)
    (D' : ContainedNormalDisk g S') (hc : MetricComplete g)
    (hcenter : D.center = D'.center) (T : Set M) {r : ℝ}
    (hr : r ≤ D.radius) (hr' : r ≤ D'.radius) :
    Submodule.span ℝ (Metric.ball 0 r ∩ D.chart ⁻¹' T) =
      Submodule.span ℝ (Metric.ball 0 r ∩ D'.chart ⁻¹' T) := by
  rw [D.local_span_eq_globalExponential hc T hr,
    D'.local_span_eq_globalExponential hc T hr', hcenter]

end ContainedNormalDisk

theorem globalExponential_smul_mem_of_every_geodesic
    (g : RiemannianMetric n M) (hc : MetricComplete g) {S : Set M}
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    {q : M} (hq : q ∈ S) {v : EuclideanSpace ℝ (Fin n)}
    (hv : g.globalExponential hc q v ∈ S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    g.globalExponential hc q (t • v) ∈ S := by
  rw [g.globalExponential_smul_eq_globalGeodesic]
  obtain ⟨hgeo, hzero, _⟩ := g.globalGeodesic_spec hc q v
  exact hconv (g.globalGeodesic hc q v) 0 1
    (fun u _ => hgeo u (mem_univ u)) (hzero.symm ▸ hq) hv ht

theorem span_ball_globalExponential_preimage_eq_of_pos
    (g : RiemannianMetric n M) (hc : MetricComplete g) {S : Set M}
    (hconv : ∀ (curve : ℝ → M) (a b : ℝ),
      g.IsGeodesicOn curve (Icc a b) →
      curve a ∈ S → curve b ∈ S → MapsTo curve (Icc a b) S)
    {q : M} (hq : q ∈ S) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Submodule.span ℝ (Metric.ball 0 r ∩ g.globalExponential hc q ⁻¹' S) =
      Submodule.span ℝ (Metric.ball 0 s ∩ g.globalExponential hc q ⁻¹' S) := by
  have hradial (R : ℝ) : ∀ v ∈ Metric.ball 0 R,
      g.globalExponential hc q v ∈ S →
      ∀ t ∈ Icc (0 : ℝ) 1, g.globalExponential hc q (t • v) ∈ S :=
    fun _ _ hv _ ht => g.globalExponential_smul_mem_of_every_geodesic hc hconv hq hv ht
  rcases le_total r s with hrs | hsr
  · exact Poincare.Riemannian.Soul.span_ball_preimage_eq_of_radial_contraction
      (g.globalExponential hc q) (hradial s) hr hrs
  · exact (Poincare.Riemannian.Soul.span_ball_preimage_eq_of_radial_contraction
      (g.globalExponential hc q) (hradial r) hs hsr).symm

end PoincareConjecture.RiemannianMetric
