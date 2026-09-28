import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.AscendingSlope
import PoincareConjecture.Proofs.Horizon.Topology.MetricSpace.GromovHausdorff.Pointed.Convergence.MovingPoints

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology

universe u

namespace Poincare.GromovHausdorff

theorem VaryingRealizationSequence.exists_sphere_distance_increment_of_pointConverges
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (S : VaryingRealizationSequence
      (fun j => (X j).toBasedMetricSpaceBundle) Y.toBasedMetricSpaceBundle)
    {p x : ∀ j, (X j).carrier} {p0 x0 : Y.carrier}
    (hp : S.PointConverges p p0) (hx : S.PointConverges x x0)
    {T c ρ σ : ℝ} (hT : 0 < T) (hc : 0 ≤ c) (hρσ : ρ < σ)
    (hcompact : IsCompact (Metric.closedBall Y.base σ))
    (hsource : ∀ j, IsCompact (Metric.closedBall (x j) T))
    (hbound : ∀ j, dist (X j).base (x j) + T ≤ ρ)
    (hascent : ∀ j, ∀ y ∈ Metric.ball (x j) T, ∀ s : ℝ, 0 < s →
      ∃ z : (X j).carrier, dist y z < s ∧
        c * dist y z < dist (p j) z - dist (p j) y) :
    ∃ q : Y.carrier, dist x0 q = T ∧ c * T ≤ dist p0 q - dist p0 x0 := by
  classical
  have hw (j : ℕ) : ∃ q : (X j).carrier,
      dist (x j) q = T ∧ c * T ≤ dist (p j) q - dist (p j) (x j) :=
    Poincare.exists_sphere_point_of_local_ascent (hsource j) hT hc
      (continuous_const.dist continuous_id).continuousOn (hascent j)
  choose q hq hgain using hw
  have hqbound (j : ℕ) : dist (X j).base (q j) ≤ ρ := by
    calc
      dist (X j).base (q j) ≤ dist (X j).base (x j) + dist (x j) (q j) :=
        dist_triangle _ _ _
      _ = dist (X j).base (x j) + T := by rw [hq j]
      _ ≤ ρ := hbound j
  obtain ⟨_, _, q0, _, φ, hφ, hq0⟩ :=
    exists_approximating_maps_and_subseq_pointConverges S hρσ hcompact q hqbound
  let Sφ := S.comp φ hφ.tendsto_atTop
  have hpφ : Sφ.PointConverges (fun j => p (φ j)) p0 :=
    hp.comp φ hφ.tendsto_atTop
  have hxφ : Sφ.PointConverges (fun j => x (φ j)) x0 :=
    hx.comp φ hφ.tendsto_atTop
  have hqφ : Sφ.PointConverges (fun j => q (φ j)) q0 := hq0
  have hdist := Sφ.tendsto_dist_of_pointConverges hxφ hqφ
  have hconst : Tendsto (fun j => dist (x (φ j)) (q (φ j))) atTop (𝓝 T) := by
    simpa only [hq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => T) atTop (𝓝 T))
  refine ⟨q0, tendsto_nhds_unique hdist hconst, ?_⟩
  exact ge_of_tendsto
    ((Sφ.tendsto_dist_of_pointConverges hpφ hqφ).sub
      (Sφ.tendsto_dist_of_pointConverges hpφ hxφ))
    (Eventually.of_forall (fun j => hgain (φ j)))

theorem VaryingRealizationSequence.local_distance_ascent_of_eventually_annular_ascent
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (S : VaryingRealizationSequence
      (fun j => (X j).toBasedMetricSpaceBundle) Y.toBasedMetricSpaceBundle)
    {p x : ∀ j, (X j).carrier} {p0 x0 : Y.carrier}
    (hp : S.PointConverges p p0) (hx : S.PointConverges x x0)
    {a b δ ρ σ c c' : ℝ} (hδ : 0 < δ) (hroom : ρ + δ < σ)
    (hc' : 0 ≤ c') (hcc' : c < c')
    (hcompact : IsCompact (Metric.closedBall Y.base σ))
    (hsource : ∀ᶠ j in atTop, IsCompact (Metric.closedBall (x j) δ))
    (hbound : ∀ᶠ j in atTop, dist (X j).base (x j) ≤ ρ)
    (hascent : ∀ᶠ j in atTop, ∀ y : (X j).carrier,
      a < dist (p j) y → dist (p j) y < b → ∀ s : ℝ, 0 < s →
        ∃ z : (X j).carrier, dist y z < s ∧
          c' * dist y z < dist (p j) z - dist (p j) y)
    (ha : a < dist p0 x0) (hb : dist p0 x0 < b) :
    ∀ s : ℝ, 0 < s → ∃ z : Y.carrier, dist x0 z < s ∧
      c * dist x0 z < dist p0 z - dist p0 x0 := by
  intro s hs
  obtain ⟨T, hT, hsmall⟩ := exists_between
    (lt_min hs (lt_min hδ (lt_min (sub_pos.mpr ha) (sub_pos.mpr hb))))
  have hTs : T < s := hsmall.trans_le (min_le_left _ _)
  have hTδ : T < δ :=
    (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_left _ _)
  have hTm : T < min (dist p0 x0 - a) (b - dist p0 x0) :=
    (hsmall.trans_le (min_le_right _ _)).trans_le (min_le_right _ _)
  have hTa : T < dist p0 x0 - a := hTm.trans_le (min_le_left _ _)
  have hTb : T < b - dist p0 x0 := hTm.trans_le (min_le_right _ _)
  have hdist := S.tendsto_dist_of_pointConverges hp hx
  have hlower : ∀ᶠ j in atTop, a + T < dist (p j) (x j) :=
    hdist.eventually_const_lt (by linarith only [hTa])
  have hupper : ∀ᶠ j in atTop, dist (p j) (x j) < b - T :=
    hdist.eventually_lt_const (by linarith only [hTb])
  have hevent : ∀ᶠ j in atTop,
      IsCompact (Metric.closedBall (x j) T) ∧
      dist (X j).base (x j) + T ≤ ρ + δ ∧
      ∀ y ∈ Metric.ball (x j) T, ∀ t : ℝ, 0 < t →
        ∃ z : (X j).carrier, dist y z < t ∧
          c' * dist y z < dist (p j) z - dist (p j) y := by
    filter_upwards [hsource, hbound, hascent, hlower, hupper] with j hjcomp hjbound hjasc hjlo hjhi
    refine ⟨hjcomp.of_isClosed_subset Metric.isClosed_closedBall
      (Metric.closedBall_subset_closedBall hTδ.le), add_le_add hjbound hTδ.le, ?_⟩
    intro y hy
    have hxy : dist (x j) y < T := by
      simpa only [Metric.mem_ball, dist_comm] using hy
    have htri : dist (p j) (x j) ≤ dist (p j) y + dist (x j) y := by
      simpa only [dist_comm] using dist_triangle (p j) y (x j)
    exact hjasc y (by linarith only [hjlo, hxy, htri])
      (by linarith only [hjhi, hxy, dist_triangle (p j) (x j) y])
  obtain ⟨φ, hφ, hφevent⟩ := Filter.extraction_of_frequently_atTop hevent.frequently
  obtain ⟨q, hq, hgain⟩ :=
    (S.comp φ hφ.tendsto_atTop).exists_sphere_distance_increment_of_pointConverges
      (hp.comp φ hφ.tendsto_atTop) (hx.comp φ hφ.tendsto_atTop) hT hc' hroom hcompact
      (fun j => (hφevent j).1) (fun j => (hφevent j).2.1)
      (fun j => (hφevent j).2.2)
  refine ⟨q, by rw [hq]; exact hTs, ?_⟩
  rw [hq]
  exact (mul_lt_mul_of_pos_right hcc' hT).trans_le hgain

end Poincare.GromovHausdorff
