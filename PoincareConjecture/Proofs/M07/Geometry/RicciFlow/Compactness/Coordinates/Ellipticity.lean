import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.Uniform
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactDifferential
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison.Coordinates












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem tangentNorm_radial_of_normalized_exponential
    (g : RiemannianMetric n M) (p : M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (he0 : e 0 = p)
    (hL : ∀ u w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L u) (L w) = inner ℝ u w)
    (hed : HasFDerivAt (fun w => extChartAt (𝓡 n) p (e w))
      L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    g.tangentNorm (e (t • v))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖ := by
  obtain ⟨S, a, _, h0, ha, _, hdomain⟩ := exists_open_radial_variation_domain hv 0
  have hγ : g.IsGeodesicOn (fun s : ℝ => e (s • v)) (Ioo (-a) a) := by
    intro s hs
    apply hgeo v hv s
    simpa only [mem_ofPred_eq, smul_zero, add_zero] using hdomain 0 h0 s hs
  have hz : (0 : ℝ) ∈ Ioo (-a) a := by constructor <;> linarith
  have ht' : t ∈ Ioo (-a) a := by constructor <;> linarith [ht.1, ht.2]
  have hd : HasDerivAt (fun s : ℝ => extChartAt (𝓡 n) p (e (s • v))) (L v) 0 := by
    have hed' : HasFDerivAt (fun w => extChartAt (𝓡 n) p (e w))
        L.toContinuousLinearMap ((0 : ℝ) • v) := by simpa only [zero_smul] using hed
    simpa only [id_eq, zero_smul, one_smul, ContinuousLinearEquiv.coe_coe,
      Function.comp_def] using!
      hed'.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v)
  obtain ⟨c, hc⟩ := hγ.exists_constant_tangentNorm (by linarith)
  have hinit := hγ.tangentNorm_initial hz (by simpa only [zero_smul] using he0) hd
  rw [hL, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)] at hinit
  exact (hc t ht').trans ((hc 0 hz).symm.trans hinit)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses



theorem eventually_uniform_elliptic_exponential_charts
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A) :
    ∃ R r a b : ℝ, 0 < r ∧ 2 * r < R ∧ 0 < a ∧ 0 < b ∧
      ∀ᶠ k in atTop,
        let C := H.sequence.carrier k
        let F := H.sequence.flow k
        letI : TopologicalSpace C.carrier := C.topologicalSpace
        letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
        letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
        ∀ p ∈ F.zeroBall A,
          ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
          ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n)
              (EuclideanSpace ℝ (Fin n)) C.carrier ∞,
            Φ.source = Metric.ball 0 R ∧ Φ.target = (F.metricAt 0).ball p R ∧
            Φ 0 = p ∧
            (∀ u v, (F.metricAt 0).pullbackCoefficients
              (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p)
              (L u) (L v) = inner ℝ u v) ∧
            HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w))
              L.toContinuousLinearMap 0 ∧
            (∀ w ∈ Metric.ball 0 R,
              (F.metricAt 0).IsGeodesicOn (fun t => Φ (t • w))
                {t : ℝ | t • w ∈ Metric.ball 0 R}) ∧
            (∀ w ∈ Metric.ball 0 R,
              (F.metricAt 0).edist p (Φ w) = ENNReal.ofReal ‖w‖) ∧
            ∀ t ∈ Ioo T' T, ∀ x ∈ Metric.closedBall 0 (2 * r), ∀ v,
              a * ‖v‖ ^ 2 ≤ (F.metricAt t).pullbackCoefficients Φ x v v ∧
              (F.metricAt t).pullbackCoefficients Φ x v v ≤ b * ‖v‖ ^ 2 := by
  obtain ⟨R, hR, hcharts⟩ :=
    H.eventually_uniform_exponential_diffeomorph_on_controlled_centres hn hA
  obtain ⟨K, hK, hcurv⟩ :=
    H.all_time_curvature_control_on_zero_ball (A + R) (by positivity)
  obtain ⟨r, hr, hrR, hsmall⟩ :=
    RiemannianMetric.exists_uniform_radial_comparison_radius hR K
  let c : ℝ := (2 * (n : ℝ) ^ 3 * K) * (T - T')
  refine ⟨R, r, Real.exp (-c) / 4, 9 * Real.exp c / 4,
    hr, hrR, by positivity, by positivity, ?_⟩
  filter_upwards [hcharts, hcurv] with k hkcharts hkcurv
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : T2Space C.carrier := C.t2Space
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let g := F.metricAt 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  intro p hp
  obtain ⟨L, Φ, hsource, htarget, hzero, hL, hderiv, hgeo, hdist⟩ := hkcharts p hp
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Φ (Metric.ball 0 R) := by
    simpa only [hsource] using Φ.contMDiffOn
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal p
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)))
    hzero hderiv hL
  have hcontain : g.ball p R ⊆ F.zeroBall (A + R) := by
    intro q hq
    change g.edist F.base q < ENNReal.ofReal (A + R)
    rw [ENNReal.ofReal_add hA.le hR.le]
    exact Manifold.riemannianEDist_triangle.trans_lt (ENNReal.add_lt_add hp hq)
  have hΦmem (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 R) :
      Φ x ∈ F.zeroBall (A + R) := by
    apply hcontain
    rw [← htarget]
    exact Φ.map_source (hsource.symm ▸ hx)
  have hradial (v : EuclideanSpace ℝ (Fin n)) (hv : v ∈ Metric.ball 0 R) :
      g.IsGeodesicOn (fun t : ℝ => Φ (t • v))
          {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (Φ (t • v))
            (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => Φ (s • v)) t 1) = ‖v‖ ∧
          g.edist p (Φ (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t := by
    refine ⟨hgeo v hv, ?_⟩
    intro t ht
    refine ⟨g.tangentNorm_radial_of_normalized_exponential p L hzero hL hderiv hgeo hv ht, ?_⟩
    have htv : t • v ∈ Metric.ball 0 R := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt
        (by simpa only [one_mul, Metric.mem_ball, dist_zero_right] using hv)
    rw [hdist _ htv, norm_smul, Real.norm_of_nonneg ht.1, ENNReal.ofReal_mul ht.1, mul_comm]
  have hbounds := g.radial_exponential_uniform_bounds (F.flow.connection 0)
    hrR hsmall he hnorm hradial
    (fun q hq => hkcurv 0 H.time_bounds q (hcontain hq))
  refine ⟨L, Φ, hsource, htarget, hzero, hL, hderiv, hgeo, hdist, ?_⟩
  intro t ht x hx v
  have hzeroBounds := ((hbounds x hx).2 v).2
  have htimeBounds := F.flow.pullbackCoefficients_exp_bounds H.time_bounds Φ x hK
    (fun s hs => hkcurv s hs (Φ x)
      (hΦmem x (Metric.closedBall_subset_ball hrR hx))) ht v
  change Real.exp (-(2 * (n : ℝ) ^ 3 * K) * (T - T')) *
      g.pullbackCoefficients Φ x v v ≤ (F.metricAt t).pullbackCoefficients Φ x v v ∧
    (F.metricAt t).pullbackCoefficients Φ x v v ≤ Real.exp c *
      g.pullbackCoefficients Φ x v v at htimeBounds
  rw [neg_mul] at htimeBounds
  constructor
  · calc
      Real.exp (-c) / 4 * ‖v‖ ^ 2 = Real.exp (-c) * ((1 / 4 : ℝ) * ‖v‖ ^ 2) := by ring
      _ ≤ Real.exp (-c) * g.pullbackCoefficients Φ x v v :=
        mul_le_mul_of_nonneg_left hzeroBounds.1 (Real.exp_pos (-c)).le
      _ ≤ (F.metricAt t).pullbackCoefficients Φ x v v := htimeBounds.1
  · calc
      (F.metricAt t).pullbackCoefficients Φ x v v ≤
          Real.exp c * g.pullbackCoefficients Φ x v v := htimeBounds.2
      _ ≤ Real.exp c * ((9 / 4 : ℝ) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hzeroBounds.2 (Real.exp_pos c).le
      _ = 9 * Real.exp c / 4 * ‖v‖ ^ 2 := by ring

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
