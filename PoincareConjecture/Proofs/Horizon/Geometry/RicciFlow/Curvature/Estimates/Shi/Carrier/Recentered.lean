import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Carrier.BallRetention

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem metric_edist_self_local
    (g : RiemannianMetric n M) (x : M) : g.edist x x = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist (𝓡 n) x x = 0
  exact Manifold.riemannianEDist_self

private theorem metric_edist_triangle_local
    (g : RiemannianMetric n M) (x y z : M) :
    g.edist x z ≤ g.edist x y + g.edist y z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.riemannianEDist (𝓡 n) x z ≤
    Manifold.riemannianEDist (𝓡 n) x y +
      Manifold.riemannianEDist (𝓡 n) y z
  exact Manifold.riemannianEDist_triangle

theorem exists_compact_recentered_carrier_for_flow_balls [T2Space M]
    {T K alpha r q delta : ℝ} (F : RicciFlow n M (Icc 0 T))
    (hK : 0 < K) (hr : 0 < r) (hdelta : 0 < delta)
    (hT0 : 0 ≤ T) (hT : T ≤ alpha / K) (p x : M)
    (hcompact : IsCompact (closure ((F.metric 0).ball p r)))
    (hRm : ∀ t ∈ Icc 0 T, ∀ y ∈ (F.metric 0).ball p r,
      (F.connection t).curvatureTensorNorm y ≤ K)
    (hx : x ∈ (F.metric 0).ball p q)
    (hmargin : q + delta ≤ r) :
    ∃ R : ℝ, 0 < R ∧ R < 3 * delta / 4 ∧
      IsCompact {y | (F.metric 0).edist x y ≤ ENNReal.ofReal R} ∧
      {y | (F.metric 0).edist x y ≤ ENNReal.ofReal R} ⊆
        (F.metric 0).ball p (q + 3 * delta / 4) ∧
      ∀ t ∈ Icc 0 T,
        closure ((F.metric t).ball x
          (Real.exp (-(n : ℝ) * alpha) * delta / 4)) ⊆
          {y | (F.metric 0).edist x y ≤ ENNReal.ofReal R} := by
  have hx' : (F.metric 0).edist p x < ENNReal.ofReal q := hx
  have hq : 0 < q := by
    by_contra hq
    have hq0 : q ≤ 0 := le_of_not_gt hq
    have hzero : ENNReal.ofReal q = 0 := ENNReal.ofReal_eq_zero.mpr hq0
    rw [hzero] at hx'
    exact (not_lt_of_ge bot_le) hx'
  have hball : (F.metric 0).ball x delta ⊆
      (F.metric 0).ball p r := by
    intro y hy
    change (F.metric 0).edist x y < ENNReal.ofReal delta at hy
    have htri := metric_edist_triangle_local (F.metric 0) p x y
    have hsum : (F.metric 0).edist p x +
        (F.metric 0).edist x y <
        ENNReal.ofReal q + ENNReal.ofReal delta := by
      exact (ENNReal.add_lt_add_right (a := (F.metric 0).edist x y)
        (b := (F.metric 0).edist p x) (c := ENNReal.ofReal q)
        (ne_top_of_lt hy) hx').trans
        (ENNReal.add_lt_add_left (a := ENNReal.ofReal q)
          (b := (F.metric 0).edist x y) (c := ENNReal.ofReal delta)
          ENNReal.ofReal_ne_top hy)
    have hsum' : (F.metric 0).edist p x +
        (F.metric 0).edist x y < ENNReal.ofReal (q + delta) := by
      rw [← ENNReal.ofReal_add hq.le hdelta.le] at hsum
      exact hsum
    have hqr : ENNReal.ofReal (q + delta) ≤ ENNReal.ofReal r :=
      ENNReal.ofReal_le_ofReal hmargin
    change (F.metric 0).edist p y < ENNReal.ofReal r
    exact htri.trans_lt (hsum'.trans_le hqr)
  have hcompactX :
      IsCompact (closure ((F.metric 0).ball x delta)) := by
    apply hcompact.of_isClosed_subset isClosed_closure
    exact (closure_mono hball)
  have hRmX : ∀ t ∈ Icc 0 T, ∀ y ∈ (F.metric 0).ball x delta,
      (F.connection t).curvatureTensorNorm y ≤ K := by
    intro t ht y hy
    exact hRm t ht y (hball hy)
  have hxself : x ∈ (F.metric 0).ball x (delta / 2) := by
    change (F.metric 0).edist x x < ENNReal.ofReal (delta / 2)
    rw [metric_edist_self_local]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  obtain ⟨R, hRpos, hRlt, hcarrierCompact, hcarrier, hflow⟩ :=
    exists_compact_carrier_for_flow_balls F hK hdelta hT0 hT x
      hcompactX hRmX x hxself
  refine ⟨R, hRpos, hRlt, hcarrierCompact, ?_, hflow⟩
  intro y hy
  have hy' : (F.metric 0).edist x y ≤ ENNReal.ofReal R := hy
  have hRdelta : R < delta := by linarith
  have hxy : (F.metric 0).edist x y < ENNReal.ofReal (3 * delta / 4) :=
    hy'.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hRlt)
  have htri := metric_edist_triangle_local (F.metric 0) p x y
  have hsum : (F.metric 0).edist p x +
      (F.metric 0).edist x y <
      ENNReal.ofReal q + ENNReal.ofReal (3 * delta / 4) := by
    exact (ENNReal.add_lt_add_right (a := (F.metric 0).edist x y)
      (b := (F.metric 0).edist p x) (c := ENNReal.ofReal q)
      (ne_top_of_lt hxy) hx').trans
      (ENNReal.add_lt_add_left (a := ENNReal.ofReal q)
        (b := (F.metric 0).edist x y)
        (c := ENNReal.ofReal (3 * delta / 4)) ENNReal.ofReal_ne_top hxy)
  have hsum' : (F.metric 0).edist p x +
      (F.metric 0).edist x y < ENNReal.ofReal (q + 3 * delta / 4) := by
    rw [← ENNReal.ofReal_add hq.le (by positivity : 0 ≤ 3 * delta / 4)] at hsum
    exact hsum
  change (F.metric 0).edist p y < ENNReal.ofReal (q + 3 * delta / 4)
  exact htri.trans_lt hsum'

end PoincareConjecture.RicciFlowAnalysis
