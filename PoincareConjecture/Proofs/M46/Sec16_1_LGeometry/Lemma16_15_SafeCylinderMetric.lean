import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_CylinderMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

theorem compatibleCylinder_half_terminalMetric_le
    {X : Type u} [TopologicalSpace X] {time : X → ℝ}
    {I : SpacetimeInterval} (G : GeneralizedLGeometryTransport 3 X time I)
    (hM04 : RicciFlowCurvatureTheory.{u}) (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {C : Type u} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) C] [IsManifold (𝓡 3) ∞ C]
    (K : SpacetimeInterval)
    (e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C)
    (M : SpacetimeCylinderMetric e) {s T rho : ℝ}
    (hs : s ∈ K.domain) (hT : T ∈ K.domain) (hst : s ≤ T) (hrho : 0 < rho)
    (hduration : T - s ≤ rho ^ 2 * Real.log 2 / 8)
    (hcurvature : ∀ r : (G.timeIntervals.interval K).Point, r.val ∈ Icc s T →
      ∀ z : C, horizontalCurvatureNorm G.leafwise (e.toSpacetime (r, z)) ≤ rho⁻¹ ^ 2)
    (z : C) (v : TangentSpace (𝓡 3) z) :
    (1 / 2 : ℝ) * (M.metric T).inner z v v ≤ (M.metric s).inner z v v := by
  have hmetric := (compatibleCylinder_metric_comparison G hM04 hM12 K e M
    hs hT hst (sq_nonneg (rho⁻¹)) hcurvature z v).2
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hexponent : 6 * rho⁻¹ ^ 2 * (T - s) ≤ Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left hduration
      (by positivity : 0 ≤ 6 * rho⁻¹ ^ 2)
    have hcancel : 6 * rho⁻¹ ^ 2 * (rho ^ 2 * Real.log 2 / 8) =
        (3 / 4 : ℝ) * Real.log 2 := by
      field_simp [hrho.ne']
      ring
    rw [hcancel] at h
    exact h.trans (by nlinarith)
  have hexp : Real.exp (6 * rho⁻¹ ^ 2 * (T - s)) ≤ 2 := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using
      Real.exp_le_exp.mpr hexponent
  have hnonneg : 0 ≤ (M.metric s).inner z v v := by
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact ((M.metric s).pos z v hv).le
  have hupper := hmetric.trans (mul_le_mul_of_nonneg_right hexp hnonneg)
  linarith

end PoincareConjecture.Proofs.M46
