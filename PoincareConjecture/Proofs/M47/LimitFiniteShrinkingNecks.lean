import PoincareConjecture.Proofs.M47.LimitFiniteChartBuffer
import PoincareConjecture.Proofs.M47.LimitFiniteNeckObstruction









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [ConnectedSpace M]

omit [ConnectedSpace M] in
private theorem finite_neck_carrier_distance {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) {x : M} (hx : x ∈ N.carrier) :
    (g.edist N.center x).toReal ≤ N.scale * Real.sqrt (1 + N.epsilon) *
      (2 * N.epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1)) := by
  have heps := N.epsilon_pos
  have hscale := N.scale_pos
  have hcenter := N.central_sphere_subset N.center_on_central_sphere
  have hheightCenter := (N.coordinate_inverse_mem N.center hcenter).2
  have hheight := (N.coordinate_inverse_mem x hx).2
  have hdiff : |(N.coordinate_inverse x).2 - (N.coordinate_inverse N.center).2| ≤
      2 * N.epsilon⁻¹ := by
    apply abs_le.mpr
    constructor <;> linarith [hheight.1, hheight.2, hheightCenter.1, hheightCenter.2]
  have hbound := (edist_le_intrinsicEDist N.carrier N.center x).trans
    ((N.intrinsicEDist_le_axial_add hcenter hx).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (add_le_add hdiff le_rfl) (mul_nonneg N.scale_pos.le (Real.sqrt_nonneg _)))))
  simpa only [ENNReal.toReal_ofReal (by positivity :
      0 ≤ N.scale * Real.sqrt (1 + N.epsilon) *
        (2 * N.epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1)))] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] in
private theorem finite_metric_triangle (g : RiemannianMetric 3 M) (x y z : M) :
    (g.edist x z).toReal ≤ (g.edist x y).toReal + (g.edist y z).toReal := by
  let := g.toMetricSpace
  exact dist_triangle x y z

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] in
private theorem finite_metric_comm (g : RiemannianMetric 3 M) (x y : M) :
    (g.edist x y).toReal = (g.edist y x).toReal := by
  let := g.toMetricSpace
  exact dist_comm x y




theorem limitFinite_shrinking_necks_impossible
    (g0 : RiemannianMetric 3 M) (g : ℕ → RiemannianMetric 3 M)
    (N : ∀ n, EpsilonNeck (g n)) (hcomplete : ∀ n, MetricComplete (g n))
    (hsec : ∀ n, (N n).connection.NonnegativeSectionalCurvature)
    {epsilon : ℝ} (hsmall : epsilon ≤ 1 / 100)
    (hepsilon : ∀ n, (N n).epsilon = epsilon)
    (o y z : M) {D d : ℝ} (hD : 0 ≤ D) (hd : 10 * (D + 1) < d)
    (hoy : (g0.edist o y).toReal = d) (hyz : (g0.edist y z).toReal = d)
    (hoz : (g0.edist o z).toReal = 2 * d)
    (hcompare : ∀ n x w, (g0.edist x w).toReal ≤ ((g n).edist x w).toReal ∧
      ((g n).edist x w).toReal ≤ (g0.edist x w).toReal + D)
    (hcenter : Tendsto (fun n => ((g n).edist y (N n).center).toReal) atTop (𝓝 0))
    (hscale : Tendsto (fun n => (N n).scale) atTop (𝓝 0)) : False := by
  let := g0.toMetricSpace
  have hdpos : 0 < d := lt_trans (by positivity) hd
  have hyo : y ≠ o := by
    intro h
    have hzero : d = 0 := by
      rw [h] at hoy
      simpa only [← g0.toMetricSpace_dist, dist_self] using hoy.symm
    linarith
  have hyzNe : y ≠ z := by
    intro h
    have hzero : d = 0 := by
      rw [h] at hyz
      simpa only [← g0.toMetricSpace_dist, dist_self] using hyz.symm
    linarith
  obtain ⟨c, r, eta, hr, heta, htarget, ho, hz, hbuffer⟩ :=
    limitFinite_exists_chart_buffer g0 y o z hyo hyzNe
  let K := Real.sqrt (1 + epsilon) *
    (2 * epsilon⁻¹ + Real.sqrt 2 * (Real.pi + 1))
  have hwidth : Tendsto (fun n => ((g n).edist y (N n).center).toReal +
      (N n).scale * K) atTop (𝓝 0) := by
    simpa only [zero_mul, zero_add] using hcenter.add (hscale.mul_const K)
  obtain ⟨n, hnWidth, hnCenter⟩ := ((hwidth.eventually (gt_mem_nhds heta)).and
    (hcenter.eventually (gt_mem_nhds zero_lt_one))).exists
  have hcarrierBall : (N n).carrier ⊆ g0.ball y eta := by
    intro x hx
    have hneck := finite_neck_carrier_distance (N n) hx
    rw [hepsilon n, mul_assoc] at hneck
    have hdist : (g0.edist y x).toReal < eta :=
      (hcompare n y x).1.trans_lt (((finite_metric_triangle (g n) y (N n).center x).trans
        (add_le_add le_rfl hneck)).trans_lt hnWidth)
    rw [← g0.toMetricSpace_ball]
    simpa only [mem_ball, dist_comm, g0.toMetricSpace_dist] using hdist
  have hcapture : (N n).carrier ⊆ c.source := fun x hx =>
    (hbuffer (hcarrierBall hx)).1
  have hball : c '' (N n).carrier ⊆ ball 0 r := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hbuffer (hcarrierBall hx)).2
  have ha : ((g n).edist (N n).center o).toReal ≤ d + D + 1 := by
    have htri := finite_metric_triangle (g n) (N n).center y o
    rw [finite_metric_comm (g n) (N n).center y] at htri
    have hdist := (hcompare n y o).2
    rw [finite_metric_comm g0 y o, hoy] at hdist
    linarith
  have hb : ((g n).edist (N n).center z).toReal ≤ d + D + 1 := by
    have htri := finite_metric_triangle (g n) (N n).center y z
    rw [finite_metric_comm (g n) (N n).center y] at htri
    have hdist := (hcompare n y z).2
    rw [hyz] at hdist
    linarith
  have hc : 2 * d ≤ ((g n).edist o z).toReal := by
    simpa only [hoz] using (hcompare n o z).1
  have hsumNonnegative : 0 ≤ d + D + 1 := by positivity
  have haSquare := (sq_le_sq₀ ENNReal.toReal_nonneg hsumNonnegative).mpr ha
  have hbSquare := (sq_le_sq₀ ENNReal.toReal_nonneg hsumNonnegative).mpr hb
  have hcSquare := (sq_le_sq₀ (show 0 ≤ 2 * d by positivity)
    ENNReal.toReal_nonneg).mpr hc
  have hfactor : d + D + 1 ≤ (11 / 10 : ℝ) * d := by linarith
  have hfactorSquare := (sq_le_sq₀ hsumNonnegative (by positivity)).mpr hfactor
  have hwide : ((g n).edist (N n).center o).toReal ^ 2 +
      ((g n).edist (N n).center z).toReal ^ 2 ≤ ((g n).edist o z).toReal ^ 2 := by
    nlinarith [sq_nonneg d]
  exact limitFinite_captured_neck_impossible (N n) (hcomplete n) (hsec n)
    ((hepsilon n).symm ▸ hsmall) c hcapture hr htarget hball o z ho hz hwide

end PoincareConjecture.M47
