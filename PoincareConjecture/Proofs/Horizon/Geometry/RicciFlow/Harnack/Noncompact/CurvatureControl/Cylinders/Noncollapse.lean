import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeRatio.Monotonicity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem asymptoticVolumeRatio_le_ball_volume_div_pow
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p : M) {r : ℝ} (hr : 0 < r) :
    g.asymptoticVolumeRatio p ≤ (g.volumeMeasure (g.ball p r)).toReal / r ^ n := by
  apply le_of_tendsto (g.tendsto_asymptoticVolumeRatio D hn hc hRic p)
  filter_upwards [eventually_ge_atTop r] with s hs
  exact g.antitoneOn_ball_volume_div_pow D hn hc hRic p hr (hr.trans_le hs) hs

theorem ball_volume_lower_bound_of_asymptoticVolumeRatio
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p y : M) (hy : g.edist p y ≠ ⊤) {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r)
    (hvolume : κ ≤ g.asymptoticVolumeRatio p) :
    ENNReal.ofReal ((κ / 2 ^ n) * r ^ n) ≤ g.volumeMeasure (g.ball y r) := by
  let R := max r (2 * (g.edist p y).toReal + 1)
  have hrR : r ≤ R := le_max_left _ _
  have hR : 0 < R := hr.trans_le hrR
  have hyR : y ∈ g.ball p (R / 2) := by
    change g.edist p y < ENNReal.ofReal (R / 2)
    rw [← ENNReal.ofReal_toReal hy]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < R / 2)).mpr
    have := le_max_right r (2 * (g.edist p y).toReal + 1)
    linarith
  have hbase : ENNReal.ofReal (κ * R ^ n) ≤ g.volumeMeasure (g.ball p R) := by
    have hratio := hvolume.trans
      (g.asymptoticVolumeRatio_le_ball_volume_div_pow D hn hc hRic p hR)
    have hreal := (le_div_iff₀ (pow_pos hR n)).mp hratio
    exact (ENNReal.ofReal_le_ofReal hreal).trans_eq
      (ENNReal.ofReal_toReal (g.ball_volume_ne_top_of_metricComplete hc p R))
  exact g.volume_lower_bound_of_center_in_half_ball D hn hc hRic p y hR hr hrR
    hκ hyR hbase

end PoincareConjecture.RiemannianMetric

theorem PoincareConjecture.RicciFlow.ball_volume_lower_bound_of_terminal_asymptoticVolumeRatio
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : PoincareConjecture.RicciFlowCurvatureTheory.{u})
    (F : PoincareConjecture.RicciFlow (m + 1) M J)
    {a b S : ℝ} (hm : 0 < m) (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, PoincareConjecture.MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hS : 0 ≤ S)
    (hscalar : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).scalarCurvature x ≤ S)
    (p : M) {κ : ℝ} (hκ : 0 < κ)
    (hvolume : κ ≤ (F.metric b).asymptoticVolumeRatio p) :
    ∀ t ∈ Icc a b, ∀ y : M, (F.metric t).edist p y ≠ ⊤ →
      ∀ r : ℝ, 0 < r →
        ENNReal.ofReal ((κ / 2 ^ (m + 1)) * r ^ (m + 1)) ≤
          (F.metric t).volumeMeasure ((F.metric t).ball y r) := by
  intro t ht y hy r hr
  have hmono := (F.asymptoticVolumeRatio_spec hC hm hJ hcomplete hoperator
    hS hscalar p).2
  apply (F.metric t).ball_volume_lower_bound_of_asymptoticVolumeRatio
    (F.connection t) (by omega) (hcomplete t ht)
    (fun x v => ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M (F.metric t) (F.connection t))
      x (hoperator t ht x) v).1) p y hy hκ.le hr
  exact hvolume.trans (hmono ht ⟨ht.1.trans ht.2, le_rfl⟩ ht.2)
