import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Uniform
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Volume











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem exists_uniform_precompact_exponential_diffeomorph_of_center
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (p₀ p : M)
    {A R r K v : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K)
    (hA : 0 < A) (hr : 0 < r) (hv : 0 < v)
    (hAR : A ≤ R) (hAr : A + r ≤ R)
    (hp : p ∈ g.ball p₀ A)
    (hcompact : IsCompact (closure (g.ball p₀ (5 * R))))
    (hcurv : ∀ x ∈ g.ball p₀ (5 * R), D.curvatureTensorNorm x ≤ K)
    (hvol : ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p₀ r)) :
    let ρ := localInjectivityRadius n K R v
    0 < ρ ∧ ρ < R ∧
      ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n)
          (EuclideanSpace ℝ (Fin n)) M ∞,
        Φ.source = Metric.ball 0 ρ ∧ Φ.target = g.ball p ρ ∧ Φ 0 = p ∧
        (∀ a b, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
          (extChartAt (𝓡 n) p p) (L a) (L b) = inner ℝ a b) ∧
        HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w))
          L.toContinuousLinearMap 0 ∧
        (∀ w ∈ Metric.ball 0 R,
          g.IsGeodesicOn (fun t => Φ (t • w))
            {t : ℝ | t • w ∈ Metric.ball 0 R}) ∧
        ∀ w ∈ Metric.ball 0 ρ,
          g.edist p (Φ w) = ENNReal.ofReal ‖w‖ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  have hRpos : 0 < R := lt_of_lt_of_le hA hAR
  have hbase : g.ball p₀ r ⊆ g.ball p R := by
    intro x hx
    change g.edist p x < ENNReal.ofReal R
    have htriangle := Manifold.riemannianEDist_triangle
      (I := 𝓡 n) (x := p) (y := p₀) (z := x)
    have hp0p : g.edist p₀ p < ENNReal.ofReal A := by
      change g.edist p₀ p < ENNReal.ofReal A at hp
      exact hp
    have hpp0 : g.edist p p₀ < ENNReal.ofReal A := by
      simpa only [edist, Manifold.riemannianEDist_comm] using hp0p
    have hsum' : ENNReal.ofReal A + ENNReal.ofReal r ≤ ENNReal.ofReal R := by
      rw [← ENNReal.ofReal_add hA.le hr.le]
      exact ENNReal.ofReal_le_ofReal hAr
    exact (htriangle.trans_lt (by simpa only [edist,
      Manifold.riemannianEDist_comm] using
        (ENNReal.add_lt_add hpp0 hx))).trans_le hsum'
  have hvolp : ENNReal.ofReal v ≤ g.volumeMeasure (g.ball p R) :=
    hvol.trans (measure_mono hbase)
  have hlarge : g.ball p (2 * R) ⊆ g.ball p₀ (5 * R) := by
    intro x hx
    change g.edist p₀ x < ENNReal.ofReal (5 * R)
    have htriangle := Manifold.riemannianEDist_triangle
      (I := 𝓡 n) (x := p₀) (y := p) (z := x)
    have hsum : g.edist p₀ p + g.edist p x <
        ENNReal.ofReal A + ENNReal.ofReal (2 * R) := by
      have hp0p : g.edist p₀ p < ENNReal.ofReal A := by
        change g.edist p₀ p < ENNReal.ofReal A at hp
        exact hp
      exact ENNReal.add_lt_add hp0p hx
    have hsum' : ENNReal.ofReal A + ENNReal.ofReal (2 * R) ≤
        ENNReal.ofReal (5 * R) := by
      rw [← ENNReal.ofReal_add hA.le (mul_nonneg (by norm_num) hRpos.le)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith
    exact (htriangle.trans_lt hsum).trans_le hsum'
  have hcompactp : IsCompact (closure (g.ball p (2 * R))) :=
    hcompact.of_isClosed_subset isClosed_closure (closure_mono hlarge)
  have hcurvp : ∀ x ∈ g.ball p (2 * R), D.curvatureTensorNorm x ≤ K := by
    intro x hx
    exact hcurv x (hlarge hx)
  exact g.exists_uniform_precompact_exponential_diffeomorph D p hn hK
    hRpos hv hcompactp hcurvp hvolp

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses

open Filter





theorem eventually_uniform_exponential_diffeomorph_on_controlled_centres
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ p ∈ F.zeroBall A,
        ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        ∃ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) C.carrier ∞,
          Φ.source = Metric.ball 0 ρ ∧ Φ.target = (F.metricAt 0).ball p ρ ∧
          Φ 0 = p ∧
          (∀ a b, (F.metricAt 0).pullbackCoefficients
            (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p)
            (L a) (L b) = inner ℝ a b) ∧
          HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w))
            L.toContinuousLinearMap 0 ∧
          (∀ w ∈ Metric.ball 0 ρ,
            (F.metricAt 0).IsGeodesicOn (fun t => Φ (t • w))
              {t : ℝ | t • w ∈ Metric.ball 0 ρ}) ∧
          ∀ w ∈ Metric.ball 0 ρ,
            (F.metricAt 0).edist p (Φ w) = ENNReal.ofReal ‖w‖ := by
  obtain ⟨r₀, κ, hr₀, hκ, hvol⟩ := H.normalized_noncollapsing
  let R : ℝ := A + r₀ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨K, hK, hcurv⟩ := H.all_time_curvature_control_on_zero_ball (5 * R) (by positivity)
  let ρ := RiemannianMetric.localInjectivityRadius n K R (κ * r₀ ^ n)
  have hρR : ρ < R := RiemannianMetric.localInjectivityRadius_lt n K hR _
  refine ⟨ρ, RiemannianMetric.localInjectivityRadius_pos n K hR _, ?_⟩
  filter_upwards [hvol, hcurv, H.zero_time_ball_compact (5 * R) (by positivity)]
    with k hkvol hkcurv hkcompact
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : MeasurableSpace C.carrier := C.measurableSpace
  let : BorelSpace C.carrier := C.borelSpace
  let : T3Space C.carrier := C.t3Space
  let : SecondCountableTopology C.carrier := C.secondCountable
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  dsimp only
  intro p hp
  obtain ⟨_, _, L, Φ, hsource, htarget, hΦ0, hL, hderivΦ, hgeo, hdist⟩ :=
    RiemannianMetric.exists_uniform_precompact_exponential_diffeomorph_of_center
      (F.metricAt 0) (F.flow.connection 0) F.base p (K := K)
      (v := κ * r₀ ^ n) (A := A) (R := R) (r := r₀) hn hK hA hr₀
      (by positivity) (by dsimp [R]; linarith) (by dsimp [R]; linarith) hp
      hkcompact (hkcurv 0 H.time_bounds) hkvol
  refine ⟨L, Φ, hsource, htarget, hΦ0, hL, hderivΦ, ?_, hdist⟩
  intro w hw t ht
  exact hgeo w (Metric.ball_subset_ball hρR.le hw) t
    (Metric.ball_subset_ball hρR.le ht)

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
