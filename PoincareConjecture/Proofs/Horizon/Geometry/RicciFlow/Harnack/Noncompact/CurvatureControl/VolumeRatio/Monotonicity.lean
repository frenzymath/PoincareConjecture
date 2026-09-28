import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.VolumeRatio.BallComparison
import Mathlib.Topology.Algebra.Order.Field

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

def RiemannianMetric.asymptoticVolumeRatio
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] (g : RiemannianMetric n M) (p : M) : ℝ :=
  limUnder atTop (fun r : ℝ => (g.volumeMeasure (g.ball p r)).toReal / r ^ n)

theorem RiemannianMetric.tendsto_asymptoticVolumeRatio
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (hn : 1 ≤ n)
    (hc : MetricComplete g)
    (hRic : ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ D.ricci x v v)
    (p : M) :
    Tendsto (fun r : ℝ => (g.volumeMeasure (g.ball p r)).toReal / r ^ n)
      atTop (𝓝 (g.asymptoticVolumeRatio p)) :=
  tendsto_nhds_limUnder (g.exists_tendsto_ball_volume_div_pow D hn hc hRic p)

private theorem tendsto_add_radius_div_pow {f : ℝ → ℝ} {V C : ℝ} {n : ℕ}
    (h : Tendsto (fun r => f r / r ^ n) atTop (𝓝 V)) :
    Tendsto (fun r => f (r + C) / r ^ n) atTop (𝓝 V) := by
  have hshift : Tendsto (fun r => f (r + C) / (r + C) ^ n) atTop (𝓝 V) :=
    h.comp (tendsto_atTop_add_const_right atTop C tendsto_id)
  have hfactor : Tendsto (fun r : ℝ => ((r + C) / r) ^ n) atTop (𝓝 1) := by
    have hz : Tendsto (fun r : ℝ => C / r) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have haux := ((tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hz).pow n
    have haux' : Tendsto (fun r : ℝ => (1 + C / r) ^ n) atTop (𝓝 1) := by
      simpa using haux
    apply haux'.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [add_div, div_self hr.ne']
  have hprod : Tendsto
      (fun r => (f (r + C) / (r + C) ^ n) * ((r + C) / r) ^ n)
      atTop (𝓝 V) := by simpa only [mul_one] using hshift.mul hfactor
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (max 0 (-C))] with r hr
  have hr0 : 0 < r := (le_max_left _ _).trans_lt hr
  have hsum : 0 < r + C := by have := (le_max_right 0 (-C)).trans_lt hr; linarith
  rw [div_pow]
  field_simp

theorem RicciFlow.asymptoticVolumeRatio_spec
    {m : ℕ} {M : Type u} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] {J : Set ℝ}
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M J)
    {a b S : ℝ} (hm : 0 < m) (hJ : Icc a b ⊆ interior J)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hoperator : ∀ t ∈ Icc a b, ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hS : 0 ≤ S)
    (hscalar : ∀ t ∈ Icc a b, ∀ x : M, (F.connection t).scalarCurvature x ≤ S)
    (p : M) :
    (∀ t ∈ Icc a b, 0 ≤ (F.metric t).asymptoticVolumeRatio p ∧
      Tendsto (fun r : ℝ =>
        ((F.metric t).volumeMeasure ((F.metric t).ball p r)).toReal / r ^ (m + 1))
        atTop (𝓝 ((F.metric t).asymptoticVolumeRatio p))) ∧
    AntitoneOn (fun t => (F.metric t).asymptoticVolumeRatio p) (Icc a b) := by
  have hlim (t : ℝ) (ht : t ∈ Icc a b) :=
    (F.metric t).tendsto_asymptoticVolumeRatio (F.connection t) (by omega)
      (hcomplete t ht)
      (fun x v => ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
        (hC.tensor_calculus (m + 1) M (F.metric t) (F.connection t))
        x (hoperator t ht x) v).1) p
  refine ⟨?_, ?_⟩
  · intro t ht
    refine ⟨ge_of_tendsto (hlim t ht) ?_, hlim t ht⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    positivity
  · intro s hs t ht hst
    have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
    have hcompare (r : ℝ) (hr : 0 < r) :=
      F.terminal_ball_volume_le_enlarged hC hm hst (hsub.trans hJ)
        (fun q hq => hcomplete q (hsub hq))
        (fun q hq => hoperator q (hsub hq)) hS
        (fun q hq => hscalar q (hsub hq)) p hr
    have hshift := tendsto_add_radius_div_pow
      (C := (4 * ((m + 1 : ℕ) : ℝ) + 8 * S) * (t - s) + 1) (hlim s hs)
    apply le_of_tendsto_of_tendsto (hlim t ht) hshift
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact div_le_div_of_nonneg_right
      (by simpa only [add_assoc] using hcompare r hr) (pow_nonneg hr.le _)

end PoincareConjecture
