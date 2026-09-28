import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.SmallComponents
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Noncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.LimitLowerBound








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable



theorem eventually_buffered_ball_volume_lower_bound_of_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    {ν δ : ℝ} (hν : 0 ≤ ν) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop, ENNReal.ofReal (ν * r ^ (m + 1)) ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) r)) :
    ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop,
      ENNReal.ofReal ((ν / 2 ^ (m + 1)) * r ^ (m + 1)) ≤
        ((F k).metric (-δ)).volumeMeasure (((F k).metric (-δ)).ball (p k) r) := by
  intro r hr
  let D : ℝ := 4 * ((m + 1 : ℕ) : ℝ) + 32
  let R : ℝ := max r (D + 1)
  have hrR : r ≤ R := le_max_left _ _
  have hR : 0 < R := hr.trans_le hrR
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hDR : D < R := lt_of_lt_of_le (lt_add_one D) (le_max_right _ _)
  filter_upwards [hA.eventually_ge_atTop 1, hL.eventually_ge_atTop (2 * R),
    hvolume R hR] with k hkA hkL hkvolume
  have hsub : Icc (-δ) 0 ⊆ Icc (-A k) 0 :=
    Icc_subset_Icc (by linarith) le_rfl
  have ht : -δ ∈ Icc (-A k) 0 := hsub ⟨le_rfl, neg_nonpos.mpr hδ⟩
  have htransfer := (F k).terminal_ball_volume_le_earlier_ball_of_cylinder hC hm
    (neg_nonpos.mpr hδ) (fun _ hs => hJ k (hsub hs))
    (fun t hs => hcomplete k t (hsub hs)) (fun t hs => hoperator k t (hsub hs))
    (by norm_num : (0 : ℝ) ≤ 4) (p k)
    (fun t hs => hscalar k t (hsub hs)) hR
    (show R + (4 * ((m + 1 : ℕ) : ℝ) + 8 * 4) * (0 - -δ) < 2 * R by
      have hprod : D * δ ≤ D := mul_le_of_le_one_right hD hδone
      dsimp only [D] at hprod hDR
      nlinarith) hkL
  have hbig : ν * R ^ (m + 1) ≤
      (((F k).metric (-δ)).volumeMeasure
        (((F k).metric (-δ)).ball (p k) (2 * R))).toReal := by
    have h := ENNReal.toReal_mono
      (((F k).metric (-δ)).ball_volume_ne_top_of_metricComplete (hcomplete k _ ht) _ _)
      (hkvolume.trans htransfer)
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hν (pow_nonneg hR.le _))] using h
  have hRic (x : (C k).carrier) (v : TangentSpace (𝓡 (m + 1)) x) :
      0 ≤ ((F k).connection (-δ)).ricci x v v :=
    (((F k).connection (-δ)).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) _ _ _) x (hoperator k _ ht x) v).1
  have hratio := ((F k).metric (-δ)).antitoneOn_ball_volume_div_pow
    ((F k).connection (-δ)) (by omega) (hcomplete k _ ht) hRic (p k)
    hr (by positivity : 0 < 2 * R) (by linarith : r ≤ 2 * R)
  have heq : ν * R ^ (m + 1) / (2 * R) ^ (m + 1) = ν / 2 ^ (m + 1) := by
    rw [mul_pow]
    field_simp
  have hsmall : (ν / 2 ^ (m + 1)) * r ^ (m + 1) ≤
      (((F k).metric (-δ)).volumeMeasure (((F k).metric (-δ)).ball (p k) r)).toReal := by
    apply (le_div_iff₀ (pow_pos hr _)).mp
    rw [← heq]
    exact (div_le_div_of_nonneg_right hbig (by positivity)).trans hratio
  exact (ENNReal.ofReal_le_ofReal hsmall).trans_eq
    (ENNReal.ofReal_toReal
      (((F k).metric (-δ)).ball_volume_ne_top_of_metricComplete (hcomplete k _ ht) _ _))

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t3Space



theorem ball_volume_lower_bound_of_metricComplete_zero
    {n : ℕ} {C : ℕ → FlowCarrier.{0} n} {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k)) {p : ∀ k, (C k).carrier} {T : ℝ}
    (G : AncientPointedGeometricConvergence C (fun k => (F k).metric) p T)
    (hT : 0 < T)
    (htime : ∀ a b : ℝ, b < T → ∀ᶠ k in atTop, Icc a b ⊆ J k)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (v : ℝ)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop, ENNReal.ofReal (v * r ^ n) ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) r)) :
    ∀ r : ℝ, 0 < r → ENNReal.ofReal (v * r ^ n) ≤
      (G.limitFlow.metric 0).volumeMeasure ((G.limitFlow.metric 0).ball G.base r) := by
  obtain ⟨a, b, ha, hb, hbT, _⟩ := exists_ancient_window_of_isCompact hT
    isCompact_singleton (singleton_subset_iff.mpr hT)
  obtain ⟨N, hN⟩ := exists_source_window_tail
    (G.subsequence_strictMono.tendsto_atTop.eventually (htime a b hbT))
  let W := G.window F (ha.trans hb) hbT.le N hN
  apply W.ball_volume_lower_bound_of_metricComplete_zero ⟨ha, hb⟩ hcomplete
  intro r hr
  exact (G.subsequence_strictMono.tendsto_atTop.comp (tendsto_add_atTop_nat N)).eventually
    (hvolume r hr)

end PoincareConjecture.AncientPointedGeometricConvergence

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold
  PoincareConjecture.smallMeasurableSpace PoincareConjecture.smallBorelSpace PoincareConjecture.smallT3Space



theorem small_ancient_limit_ball_volume_lower_bound
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
    (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
    (p : ∀ k, (C k).carrier) (A L : ℕ → ℝ)
    (hA : Tendsto A atTop atTop) (hL : Tendsto L atTop atTop)
    (hJ : ∀ k, Icc (-A k) 0 ⊆ interior (J k))
    (hcomplete : ∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t))
    (hoperator : ∀ k, ∀ t ∈ Icc (-A k) 0, ∀ x : (C k).carrier,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (hscalar : ∀ k, ∀ t ∈ Icc (-A k) 0,
      ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
        ((F k).connection t).scalarCurvature x ≤ 4)
    {ν δ : ℝ} (hν : 0 ≤ ν) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hvolume : ∀ r : ℝ, 0 < r → ∀ᶠ k in atTop, ENNReal.ofReal (ν * r ^ (m + 1)) ≤
      ((F k).metric 0).volumeMeasure (((F k).metric 0).ball (p k) r))
    (G : AncientPointedGeometricConvergence (fun k => (C k).shrink)
      (fun k t => (F k).shrink.metric (t - δ))
      (fun k => equivShrink (C k).carrier (p k)) δ)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    ∀ r : ℝ, 0 < r → ENNReal.ofReal ((ν / 2 ^ (m + 1)) * r ^ (m + 1)) ≤
      (G.limitFlow.metric 0).volumeMeasure ((G.limitFlow.metric 0).ball G.base r) := by
  apply AncientPointedGeometricConvergence.ball_volume_lower_bound_of_metricComplete_zero
    (C := fun k => (C k).shrink)
    (fun k => (F k).shrink.bufferedExpandingFlow δ) G hδ
    (eventually_buffered_time_window J A hA hJ δ) hGcomplete
  intro r hr
  have hbound := eventually_buffered_ball_volume_lower_bound_of_expanding_cylinders
    hC hm C J F p A L hA hL hJ hcomplete hoperator hscalar hν hδ.le hδone hvolume r hr
  filter_upwards [hbound] with k hk
  dsimp only [FlowCarrier.shrink, bufferedExpandingFlow_metric]
  rw [zero_sub, shrink_volumeMeasure_ball, Equiv.symm_apply_apply]
  exact hk

end PoincareConjecture.RicciFlow
