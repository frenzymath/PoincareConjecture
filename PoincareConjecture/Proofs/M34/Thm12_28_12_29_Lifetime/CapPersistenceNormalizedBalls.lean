import PoincareConjecture.Proofs.M34.Mathlib.CapPersistenceNormalizedRadius
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M09.RiemannianProper











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric




theorem exists_normalized_ball_of_continuous
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [ConnectedSpace M]
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    {f : M → ℝ} (hf : Continuous f) (x : M) (hfx : 0 < f x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (Real.sqrt (f x))⁻¹ ∧
      sSup (f '' g.ball x r) = r⁻¹ ^ 2 ∧ IsCompact (closure (g.ball x r)) := by
  let : MetricSpace M := Proofs.M09.selectedMetricSpace g
  let : ProperSpace M := Proofs.M09.selectedMetricSpace_proper g hcomplete
  obtain ⟨r, hr, hrR, hnorm⟩ :=
    Metric.exists_pos_sSup_image_ball_eq_inv_sq_of_approximate_radial_projection x
      (Proofs.M09.selectedMetricSpace_radial_projection g x) hf hfx
  have hball : g.ball x r = Metric.ball x r := by
    have he : g.ball x r = Metric.eball x (ENNReal.ofReal r) := by
      ext y
      change g.edist x y < ENNReal.ofReal r ↔ EDist.edist y x < ENNReal.ofReal r
      rw [← Proofs.M09.selectedMetricSpace_edist g x y, PseudoEMetricSpace.edist_comm]
    exact he.trans Metric.eball_ofReal
  refine ⟨r, hr, hrR, ?_, Proofs.M09.isCompact_closure_metric_ball g hcomplete x r⟩
  rwa [hball]



theorem exists_scalar_normalized_ball
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T3Space M] [ConnectedSpace M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (x : M) (hR : 0 < D.scalarCurvature x) :
    ∃ r : ℝ, 0 < r ∧ r ≤ (Real.sqrt (D.scalarCurvature x))⁻¹ ∧
      scalarCurvatureSupOn g D (g.ball x r) = r⁻¹ ^ 2 ∧
      IsCompact (closure (g.ball x r)) := by
  obtain ⟨r, hr, hrR, hnorm, hcompact⟩ := g.exists_normalized_ball_of_continuous hcomplete
    (M34.contMDiff_scalarCurvature D).continuous x hR
  refine ⟨r, hr, hrR, ?_, hcompact⟩
  simpa only [scalarCurvatureSupOn, image_eq_range] using hnorm

end PoincareConjecture.RiemannianMetric
