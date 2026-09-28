import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Radius.Existence

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

namespace CompactKappaCoreRadius

variable {X : Type*} [MetricSpace X] [ProperSpace X]

theorem radius_le_max_distance_scale
    {f : X → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (p : X) {r : ℝ} (hr : 0 < r)
    (heq : sSup (f '' ball p r) = r⁻¹ ^ 2) (x : X) :
    r ≤ max (dist p x) (Real.sqrt (f x))⁻¹ := by
  by_cases hd : r ≤ dist p x
  · exact hd.trans (le_max_left _ _)
  have hx : x ∈ ball p r := by
    simpa only [mem_ball, dist_comm] using lt_of_not_ge hd
  have hscalar := le_csSup (scalar_image_ball_bddAbove hf p r) (mem_image_of_mem f hx)
  rw [heq] at hscalar
  have hsqrt : Real.sqrt (f x) ≤ r⁻¹ :=
    Real.sqrt_le_iff.mpr ⟨inv_nonneg.mpr hr.le, hscalar⟩
  have hscale : r ≤ (Real.sqrt (f x))⁻¹ := by
    simpa only [inv_inv] using inv_anti₀ (Real.sqrt_pos.mpr (hpos x)) hsqrt
  exact hscale.trans (le_max_right _ _)

theorem radius_le_center_scale
    {f : X → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (p : X) {r : ℝ} (hr : 0 < r)
    (heq : sSup (f '' ball p r) = r⁻¹ ^ 2) :
    r ≤ (Real.sqrt (f p))⁻¹ := by
  simpa only [dist_self, max_eq_right (inv_nonneg.mpr (Real.sqrt_nonneg _))] using
    radius_le_max_distance_scale hf hpos p hr heq p

theorem lipschitzWith_radius
    (hclosure : ∀ p : X, ∀ r : ℝ, 0 < r → closure (ball p r) = closedBall p r)
    {f : X → ℝ} (hf : Continuous f) (hpos : ∀ x, 0 < f x)
    (R : X → ℝ) (hR : ∀ p, 0 < R p ∧ sSup (f '' ball p (R p)) = (R p)⁻¹ ^ 2) :
    LipschitzWith 1 R := by
  apply LipschitzWith.of_le_add_mul 1
  intro p q
  obtain ⟨s, hs, hseq, x, hx, hscale⟩ := exists_sup_ball_inv_sq_witness hclosure f hf hpos q
  have hsR : s = R q := (exists_unique_sup_ball_inv_sq hclosure f hf hpos q).unique
    ⟨hs, hseq⟩ (hR q)
  rw [hsR] at hx hscale
  have hxq : dist q x ≤ R q := by simpa only [mem_closedBall, dist_comm] using hx
  have hb := radius_le_max_distance_scale hf hpos p (hR p).1 (hR p).2 x
  simp only [NNReal.coe_one, one_mul]
  apply hb.trans
  apply max_le
  · linarith [dist_triangle p q x]
  · rw [hscale]
    exact le_add_of_nonneg_right dist_nonneg

end CompactKappaCoreRadius

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T3Space M] [ConnectedSpace M]

noncomputable def scalarCoreRadius (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hscalar : ∀ x : M, 0 < D.scalarCurvature x) (p : M) : ℝ :=
  Classical.choose (exists_unique_scalar_core_radius g D hcomplete hscalar p).exists

theorem scalarCoreRadius_spec (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hscalar : ∀ x : M, 0 < D.scalarCurvature x) (p : M) :
    0 < scalarCoreRadius g D hcomplete hscalar p ∧
      scalarCurvatureSupOn g D (g.ball p (scalarCoreRadius g D hcomplete hscalar p)) =
        (scalarCoreRadius g D hcomplete hscalar p)⁻¹ ^ 2 :=
  Classical.choose_spec (exists_unique_scalar_core_radius g D hcomplete hscalar p).exists

theorem eq_scalarCoreRadius_of_spec (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hscalar : ∀ x : M, 0 < D.scalarCurvature x) (p : M) {r : ℝ}
    (hr : 0 < r) (heq : scalarCurvatureSupOn g D (g.ball p r) = r⁻¹ ^ 2) :
    r = scalarCoreRadius g D hcomplete hscalar p :=
  (exists_unique_scalar_core_radius g D hcomplete hscalar p).unique ⟨hr, heq⟩
    (scalarCoreRadius_spec g D hcomplete hscalar p)

private theorem scalar_sup_eq_metric_image (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (p : M) (r : ℝ) :
    letI := g.toMetricSpace
    scalarCurvatureSupOn g D (g.ball p r) = sSup (D.scalarCurvature '' Metric.ball p r) := by
  let := g.toMetricSpace
  rw [g.toMetricSpace_ball]
  unfold scalarCurvatureSupOn
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem scalarCoreRadius_le_center_scale (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hscalar : ∀ x : M, 0 < D.scalarCurvature x) (p : M) :
    scalarCoreRadius g D hcomplete hscalar p ≤ (Real.sqrt (D.scalarCurvature p))⁻¹ := by
  let : MetricSpace M := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  have hs := scalarCoreRadius_spec g D hcomplete hscalar p
  apply CompactKappaCoreRadius.radius_le_center_scale D.continuous_scalarCurvature hscalar p hs.1
  exact (scalar_sup_eq_metric_image g D p _).symm.trans hs.2

theorem lipschitzWith_scalarCoreRadius (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hscalar : ∀ x : M, 0 < D.scalarCurvature x) :
    letI := g.toMetricSpace
    LipschitzWith 1 (scalarCoreRadius g D hcomplete hscalar) := by
  let : MetricSpace M := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  apply CompactKappaCoreRadius.lipschitzWith_radius
    (fun x _ hr ↦ CompactKappaCoreRadius.closure_ball_eq_of_approximate_split
      (fun x y _ _ hr hε ↦ g.approximate_split_toMetricSpace x y hr hε) x hr)
    D.continuous_scalarCurvature hscalar
  intro p
  have hs := scalarCoreRadius_spec g D hcomplete hscalar p
  exact ⟨hs.1, (scalar_sup_eq_metric_image g D p _).symm.trans hs.2⟩

theorem continuous_scalarCoreRadius (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hscalar : ∀ x : M, 0 < D.scalarCurvature x) :
    Continuous (scalarCoreRadius g D hcomplete hscalar) := by
  let : MetricSpace M := g.toMetricSpace
  exact (lipschitzWith_scalarCoreRadius g D hcomplete hscalar).continuous

theorem scalarCoreRadius_abs_sub_le (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hscalar : ∀ x : M, 0 < D.scalarCurvature x) (p q : M) :
    |scalarCoreRadius g D hcomplete hscalar p - scalarCoreRadius g D hcomplete hscalar q| ≤
      (g.edist p q).toReal := by
  let : MetricSpace M := g.toMetricSpace
  have h := (lipschitzWith_scalarCoreRadius g D hcomplete hscalar).dist_le_mul p q
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul, RiemannianMetric.toMetricSpace_dist] using h

end PoincareConjecture
