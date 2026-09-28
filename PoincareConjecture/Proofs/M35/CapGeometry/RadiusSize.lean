import PoincareConjecture.Proofs.M35.CapGeometry.CoreBallVolume










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M35



theorem scalar_curvature_radius_sq_mul_scalar_le_one
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [ConnectedSpace M] (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hR : Continuous D.scalarCurvature) (y : M) {r : ℝ} (hr : 0 < r)
    (hscale : scalarCurvatureSupOn g D (g.ball y r) = r⁻¹ ^ 2) :
    r ^ 2 * D.scalarCurvature y ≤ 1 := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  have hy : y ∈ g.ball y r := by
    change g.edist y y < ENNReal.ofReal r
    rw [← Proofs.M09.selectedMetricSpace_edist g, edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hcompact := Proofs.M09.isCompact_closure_metric_ball g hcomplete y r
  have hbounded : BddAbove (range fun z : g.ball y r => D.scalarCurvature z.1) := by
    rw [← image_eq_range]
    exact (hcompact.bddAbove_image hR.continuousOn).mono (image_mono subset_closure)
  have hcenter : D.scalarCurvature y ≤ scalarCurvatureSupOn g D (g.ball y r) :=
    le_csSup hbounded ⟨⟨y, hy⟩, rfl⟩
  rw [hscale] at hcenter
  have h := mul_le_mul_of_nonneg_left hcenter (sq_nonneg r)
  rwa [← mul_pow, mul_inv_cancel₀ hr.ne', one_pow] at h



theorem scalar_curvature_radius_le_of_center_lower
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [ConnectedSpace M] (g : RiemannianMetric 3 M)
    (D : LeviCivitaData g) (hcomplete : MetricComplete g)
    (hR : Continuous D.scalarCurvature) (y : M) {r b : ℝ}
    (hr : 0 < r) (hb : 0 < b)
    (hscale : scalarCurvatureSupOn g D (g.ball y r) = r⁻¹ ^ 2)
    (hfloor : b⁻¹ ^ 2 ≤ D.scalarCurvature y) : r ≤ b := by
  have hcenter := scalar_curvature_radius_sq_mul_scalar_le_one g D hcomplete hR y hr hscale
  have hRpos : 0 < D.scalarCurvature y := (sq_pos_of_pos (inv_pos.mpr hb)).trans_le hfloor
  have hcross : 1 ≤ b ^ 2 * D.scalarCurvature y := by
    have h := mul_le_mul_of_nonneg_left hfloor (sq_nonneg b)
    rwa [← mul_pow, mul_inv_cancel₀ hb.ne', one_pow] at h
  have hsq : r ^ 2 ≤ b ^ 2 :=
    (mul_le_mul_iff_of_pos_right hRpos).mp (hcenter.trans hcross)
  nlinarith

end PoincareConjecture.M35

namespace PoincareConjecture.RepairedStandardCapExistenceData




theorem scalar_curvature_ball_volume_lower_of_large_scalar
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀)
    (N : StandardFlowNoncollapsingCertificate E.flow) {t r : ℝ}
    (ht : t ∈ Ico 0 E.flow.base.lifetime) (htlow : 1 / 2 ≤ t) (hr : 0 < r)
    (y : StandardCapSpace)
    (hscale : scalarCurvatureSupOn (E.flow.metric t) (E.flow.connection t)
      ((E.flow.metric t).ball y r) = r⁻¹ ^ 2)
    (hfloor : max (N.radius⁻¹ ^ 2) 2 ≤ (E.flow.connection t).scalarCurvature y) :
    ENNReal.ofReal (N.kappa / 8 * r ^ 3) ≤
      calibratedMetricVolume (E.flow.metric t) ((E.flow.metric t).ball y r) := by
  have hRcont : Continuous (E.flow.connection t).scalarCurvature :=
    (Proofs.M09.scalarCurvature_contMDiff P (E.flow.connection t)).continuous
  have hcomplete := E.complete t ht
  have hradius := M35.scalar_curvature_radius_le_of_center_lower
    (E.flow.metric t) (E.flow.connection t) hcomplete hRcont y hr N.radius_pos
    hscale ((le_max_left _ _).trans hfloor)
  have hsize := M35.scalar_curvature_radius_sq_mul_scalar_le_one
    (E.flow.metric t) (E.flow.connection t) hcomplete hRcont y hr hscale
  have htwo := mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hfloor) (sq_nonneg r)
  exact E.scalar_curvature_ball_volume_lower P N ht hr hradius (by nlinarith) y hscale

end PoincareConjecture.RepairedStandardCapExistenceData
