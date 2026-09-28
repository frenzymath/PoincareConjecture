import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Ray
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Weak.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

open Poincare.Riemannian

private theorem abs_ray_busemannApprox_le_base_distance
    {M : Type*} [MetricSpace M] {ray : ℝ → M} (hray : Soul.IsRay ray)
    {t : ℝ} (ht : 0 ≤ t) (x : M) :
    |Soul.busemannApprox ray t x| ≤ dist (ray 0) x := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · simpa only [dist_comm] using Soul.neg_dist_le_busemannApprox hray x ht
  · simpa only [Soul.busemannApprox, sub_zero] using
      Soul.busemannApprox_antitone hray x self_mem_Ici ht ht

private theorem tendsto_integral_ray_busemannApprox_mul_compact_test
    {n : ℕ} {M : Type*} [MetricSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {ray : ℝ → M} (hray : Soul.IsRay ray)
    {ψ : M → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun t : ℝ => ∫ x, Soul.busemannApprox ray t x * ψ x ∂g.volumeMeasure)
      atTop (𝓝 (∫ x, Soul.busemann ray x * ψ x ∂g.volumeMeasure)) := by
  have hd : Continuous (fun x : M => dist (ray 0) x) := continuous_const.dist continuous_id
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => dist (ray 0) x * ‖ψ x‖)
  · exact Eventually.of_forall fun t =>
      (((continuous_const.dist continuous_id).sub continuous_const).mul hψ).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (abs_ray_busemannApprox_le_base_distance hray ht x)
        (norm_nonneg _)
  · exact (hd.mul hψ.norm).integrable_of_hasCompactSupport hc.norm.mul_left
  · exact Eventually.of_forall fun x => (Soul.tendsto_busemannApprox hray x).mul_const (ψ x)

theorem ray_busemann_distributional_superharmonic
    {m : ℕ} {M : Type*} [MetricSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M]
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : D.NonnegativeRicciCurvature)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : Soul.IsRay ray)
    (φ : M → ℝ) (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    (∫ x, Soul.busemann ray x * D.laplacian φ x ∂g.volumeMeasure) ≤ 0 := by
  have hlapc := D.hasCompactSupport_laplacian hc
  have hlapi : Integrable (D.laplacian φ) g.volumeMeasure :=
    (D.continuous_laplacian hφ).integrable_of_hasCompactSupport hlapc
  have hlap0 : (∫ x, D.laplacian φ x ∂g.volumeMeasure) = 0 := by
    have h := D.integral_mul_laplacian_comm_of_hasCompactSupport_left
      hφ (contMDiff_const (c := (1 : ℝ))) hc
    simpa [LeviCivitaData.laplacian, LeviCivitaData.hessian,
      LeviCivitaData.hessianOnFields, mvfderiv_const] using h.symm
  have happ (t : ℝ) :
      (∫ x, Soul.busemannApprox ray t x * D.laplacian φ x ∂g.volumeMeasure) =
        ∫ x, (g.edist (ray t) x).toReal * D.laplacian φ x ∂g.volumeMeasure := by
    simp only [Soul.busemannApprox, hdist, sub_mul]
    rw [integral_sub
      (D.integrable_mul_laplacian_of_hasCompactSupport_right
        (g.continuous_toReal_edist (ray t)) hφ hc)
      (hlapi.const_mul t), integral_const_mul, hlap0, mul_zero, sub_zero]
  obtain ⟨R, hR⟩ := hc.bddAbove_image
    (show Continuous (fun x : M => dist (ray 0) x) from
      continuous_const.dist continuous_id).continuousOn
  have hbound (A : ℝ) (hA : 0 < A) :
      (∫ x, Soul.busemann ray x * D.laplacian φ x ∂g.volumeMeasure) ≤
        (m : ℝ) / A * ∫ x, φ x ∂g.volumeMeasure := by
    apply le_of_tendsto
      (tendsto_integral_ray_busemannApprox_mul_compact_test g hray
        (D.continuous_laplacian hφ) hlapc)
    filter_upwards [eventually_ge_atTop (max 0 (A + R))] with t ht
    rw [happ]
    apply D.integral_distance_mul_laplacian_le hm hcomplete hRic (ray t) A hA φ hφ hc hφ0
    intro x hx
    rw [← hdist]
    have ht0 : 0 ≤ t := (le_max_left _ _).trans ht
    have hd : dist (ray 0) (ray t) = t := by
      simpa only [zero_sub, abs_neg, abs_of_nonneg ht0] using hray le_rfl ht0
    have hxR := hR (mem_image_of_mem _ hx)
    have htriangle := dist_triangle (ray 0) x (ray t)
    rw [hd, dist_comm x (ray t)] at htriangle
    have hAR : A + R ≤ t := (le_max_right _ _).trans ht
    linarith
  have hI : 0 ≤ ∫ x, φ x ∂g.volumeMeasure := integral_nonneg hφ0
  apply le_of_forall_pos_le_add
  intro ε hε
  let A := (m : ℝ) * (∫ x, φ x ∂g.volumeMeasure) / ε + 1
  have hA : 0 < A := by dsimp [A]; positivity
  have hquot : (m : ℝ) / A * (∫ x, φ x ∂g.volumeMeasure) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hA]
    dsimp [A]
    have hcancel : ((m : ℝ) * (∫ x, φ x ∂g.volumeMeasure) / ε) * ε =
        (m : ℝ) * (∫ x, φ x ∂g.volumeMeasure) := div_mul_cancel₀ _ hε.ne'
    nlinarith
  simpa only [zero_add] using (hbound A hA).trans hquot

theorem ray_busemann_integral_differential_nonneg
    {m : ℕ} {M : Type*} [MetricSpace M] [T3Space M] [PreconnectedSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M]
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g)
    (hm : 0 < m) (hcomplete : MetricComplete g)
    (hRic : D.NonnegativeRicciCurvature)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : Soul.IsRay ray)
    (φ : M → ℝ) (hφ : ContMDiff (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ φ)
    (hc : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x) :
    Integrable (fun x => mvfderiv (𝓡 (m + 1))
      (Soul.busemann ray) x (D.gradient φ x)) g.volumeMeasure ∧
      0 ≤ ∫ x, mvfderiv (𝓡 (m + 1))
        (Soul.busemann ray) x (D.gradient φ x) ∂g.volumeMeasure := by
  have hLip (x y : M) :
      |Soul.busemann ray x - Soul.busemann ray y| ≤ (g.edist x y).toReal := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, hdist] using
      (Soul.lipschitz_busemann hray).dist_le_mul x y
  obtain ⟨hi, hgreen⟩ := D.integral_mul_laplacian_of_distance_lipschitz hLip hφ hc
  refine ⟨hi, ?_⟩
  have hweak := g.ray_busemann_distributional_superharmonic D hm hcomplete hRic
    hdist hray φ hφ hc hφ0
  rw [hgreen] at hweak
  linarith

end PoincareConjecture.RiemannianMetric
