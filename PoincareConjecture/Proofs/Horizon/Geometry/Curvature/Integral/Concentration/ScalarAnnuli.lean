import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.GeometricAnnuli
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.PuncturedIntegral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Singleton








noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData



theorem integral_scalarCurvature_posPart_outside_ball_le_of_scale_annuli
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (p : M)
    {a r₀ R C : ℝ} {m : ℕ} (ha : 0 < a) (hr₀ : 0 < r₀)
    (hR : R < 19 * r₀ / 16) (hC : 0 ≤ C) (hm : 1 ≤ m)
    (hbound : ∀ r : ℝ, 2 * a ≤ r → r ≤ r₀ →
      (∫ x in {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C * r ^ m) :
    (∫ x in g.ball p R \ g.ball p (4 * a),
      max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
        C * r₀ ^ m / (1 - (227 / 228 : ℝ) ^ m) := by
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  let K := Metric.closedBall p R \ Metric.ball p (4 * a)
  let h : M → ℝ := fun x => max 0 (D.scalarCurvature x)
  have hK : IsCompact K := (isCompact_closedBall p R).diff Metric.isOpen_ball
  have hcont : Continuous h := continuous_const.max D.continuous_scalarCurvature
  have hKi : IntegrableOn h K g.volumeMeasure := hcont.continuousOn.integrableOn_compact hK
  have hsub : K ⊆ {x | (19 / 16 : ℝ) * (2 * a) < dist p x ∧
      dist p x < (19 / 16 : ℝ) * r₀} := by
    intro x hx
    have hlo : 4 * a ≤ dist p x := by
      simpa only [Metric.mem_ball, not_lt, dist_comm] using hx.2
    have hhi : dist p x ≤ R := by
      simpa only [Metric.mem_closedBall, dist_comm] using hx.1
    constructor <;> linarith
  have hri (j : ℕ) : r₀ * (227 / 228 : ℝ) ^ j ≤ r₀ := by
    exact mul_le_of_le_one_right hr₀.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hAnnulusI (r : ℝ) :
      IntegrableOn h {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)}
        g.volumeMeasure := by
    have hi := g.integrableOn_ball_of_continuous hcomplete hcont p (19 * r / 16 + 1)
    apply hi.mono_set
    intro x hx
    rw [← g.toMetricSpace_ball, Metric.mem_ball, dist_comm]
    change dist p x ∈ Icc (113 * r / 96) (19 * r / 16) at hx
    linarith only [hx.2]
  have hOpenSub (r : ℝ) :
      {x : M | (113 / 96 : ℝ) * r < dist p x ∧ dist p x < (19 / 16 : ℝ) * r} ⊆
        {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)} := by
    intro x hx
    change dist p x ∈ Icc (113 * r / 96) (19 * r / 16)
    constructor <;> linarith only [hx.1, hx.2]
  have hKbound := Poincare.CurvatureIntegral.integral_le_of_geometric_annulus_bounds_above_scale
    hK p (A := 113 / 96) (B := 19 / 16) (by norm_num) (by norm_num) hr₀
    (q := 227 / 228) (by norm_num) (by norm_num) (by norm_num)
    hC hm (s := 2 * a) (by positivity)
    (h := h) (fun x => le_max_left _ _) hKi hsub
    (fun j => (hAnnulusI _).mono_set (hOpenSub _))
    (fun j hj => (setIntegral_mono_set (hAnnulusI _)
      (Filter.Eventually.of_forall (fun _ => le_max_left _ _))
      (Filter.Eventually.of_forall (hOpenSub _))).trans (hbound _ hj (hri j)))
  apply (setIntegral_mono_set hKi
    (Filter.Eventually.of_forall (fun _ => le_max_left _ _)) ?_).trans hKbound
  apply Filter.Eventually.of_forall
  intro x hx
  rw [← g.toMetricSpace_ball, ← g.toMetricSpace_ball] at hx
  exact ⟨Metric.ball_subset_closedBall hx.1, hx.2⟩



theorem integral_scalarCurvature_posPart_ball_le_of_all_scale_annuli
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) (hcomplete : MetricComplete g) (p : M)
    {r₀ R C : ℝ} {m : ℕ} (hr₀ : 0 < r₀)
    (hR : R < 19 * r₀ / 16) (hC : 0 ≤ C) (hm : 1 ≤ m)
    (hbound : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      (∫ x in {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C * r ^ m) :
    (∫ x in g.ball p R, max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
      C * r₀ ^ m / (1 - (227 / 228 : ℝ) ^ m) := by
  let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
  let := g.toMetricSpace
  let : NullSingletonClass g.volumeMeasure := g.volumeMeasure_nullSingletonClass hn
  apply Poincare.CurvatureIntegral.integral_le_of_compl_ball_bounds
    (by rw [← g.toMetricSpace_ball]; exact Metric.isOpen_ball.measurableSet)
    (g.integrableOn_ball_of_continuous hcomplete
      (continuous_const.max D.continuous_scalarCurvature) p R) p
  intro a ha
  have hb := D.integral_scalarCurvature_posPart_outside_ball_le_of_scale_annuli
    hcomplete p (a := a / 4) (by positivity) hr₀ hR hC hm
    (fun r hr hr' => hbound r (by linarith) hr')
  rw [show 4 * (a / 4) = a by ring, ← g.toMetricSpace_ball p a] at hb
  exact hb



theorem integral_scalarCurvature_posPart_outside_ball_le_of_nonneg_scale_annuli
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hn : 0 < n) (hcomplete : MetricComplete g) (p : M)
    {a r₀ R C : ℝ} {m : ℕ} (ha : 0 ≤ a) (hr₀ : 0 < r₀)
    (hR : R < 19 * r₀ / 16) (hC : 0 ≤ C) (hm : 1 ≤ m)
    (hbound : ∀ r : ℝ, 0 < r → 2 * a ≤ r → r ≤ r₀ →
      (∫ x in {x : M | (g.edist p x).toReal ∈ Icc (113 * r / 96) (19 * r / 16)},
        max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤ C * r ^ m) :
    (∫ x in g.ball p R \ g.ball p (4 * a),
      max 0 (D.scalarCurvature x) ∂g.volumeMeasure) ≤
        C * r₀ ^ m / (1 - (227 / 228 : ℝ) ^ m) := by
  rcases ha.eq_or_lt with rfl | ha
  · let : ConnectedSpace M := { toNonempty := ⟨p⟩ }
    let := g.toMetricSpace
    have hb := D.integral_scalarCurvature_posPart_ball_le_of_all_scale_annuli
      hn hcomplete p hr₀ hR hC hm (fun r hr hr' => hbound r hr (by simpa using hr.le) hr')
    simpa only [mul_zero, ← g.toMetricSpace_ball p 0, Metric.ball_zero, sdiff_empty] using hb
  · exact D.integral_scalarCurvature_posPart_outside_ball_le_of_scale_annuli
      hcomplete p ha hr₀ hR hC hm (fun r hr hr' => hbound r (by linarith) hr hr')

end PoincareConjecture.LeviCivitaData
