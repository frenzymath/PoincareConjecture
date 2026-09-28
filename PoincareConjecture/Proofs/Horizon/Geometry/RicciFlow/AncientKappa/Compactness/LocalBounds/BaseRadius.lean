import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.FiniteRadius
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Spheres
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Rigidity.MaximalBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_radius_calibrated_volume_eq
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M)
    {r c : ℝ} (hr : 0 < r) (_hcpos : 0 < c)
    (hcω : c < euclideanUnitBallVolume n)
    (hvolume : calibratedMetricVolume g (g.ball p r) < ENNReal.ofReal (c * r ^ n)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧
      calibratedMetricVolume g (g.ball p ρ) = ENNReal.ofReal (c * ρ ^ n) := by
  let f : ℝ → ℝ := fun s => (g.volumeMeasure (g.ball p s)).toReal / s ^ n
  have hnear : ∀ᶠ s in 𝓝[>] (0 : ℝ), c < f s :=
    (g.tendsto_ball_volume_div_pow_at_zero p).eventually (eventually_gt_nhds hcω)
  have hevent : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s < r ∧ c < f s := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hr).filter_mono nhdsWithin_le_nhds, hnear] with s hs hsr hfs
    exact ⟨hs, hsr, hfs⟩
  obtain ⟨s, hs0, hsr, hfs⟩ := hevent.exists
  have hfr : f r < c := by
    rw [calibratedMetricVolume_eq_volumeMeasure] at hvolume
    have hv := (ENNReal.lt_ofReal_iff_toReal_lt
      (g.ball_volume_ne_top_of_metricComplete hc p r)).mp hvolume
    exact (div_lt_iff₀ (pow_pos hr n)).mpr hv
  have hcont : ContinuousOn f (Icc s r) := by
    intro a ha
    have ha0 : 0 < a := hs0.trans_le ha.1
    exact ((g.continuousAt_ball_volume_toReal_of_metricComplete hc p ha0).div
      (continuousAt_id.pow n) (pow_ne_zero n ha0.ne')).continuousWithinAt
  obtain ⟨ρ, hρ, heq⟩ := intermediate_value_Icc' hsr.le hcont ⟨hfr.le, hfs.le⟩
  have hρ0 : 0 < ρ := hs0.trans_le hρ.1
  have hρr : ρ < r := lt_of_le_of_ne hρ.2 (by
    intro h
    exact hfr.ne (h ▸ heq))
  refine ⟨ρ, hρ0, hρr, ?_⟩
  rw [calibratedMetricVolume_eq_volumeMeasure,
    ← ENNReal.ofReal_toReal (g.ball_volume_ne_top_of_metricComplete hc p ρ)]
  exact congrArg ENNReal.ofReal ((div_eq_iff (pow_ne_zero n hρ0.ne')).mp heq)

end RiemannianMetric

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance baseRadiusCarrierConnected (C : FlowCarrier.{0} 3) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

theorem m23_tendsto_base_ball_volume_zero_of_unbounded_scalar
    (P : M23NormalizedKappaCompactnessPredecessors)
    (C : ℕ → FlowCarrier.{0} 3) (K : ∀ k, AncientKappaSolution 3 (C k).carrier)
    {κ : ℝ} (hκ : 0 < κ) (hkappa : ∀ k, (K k).kappa = κ)
    (p x : ∀ k, (C k).carrier) {r : ℝ} (hr : 0 < r)
    (hx : ∀ k, x k ∈ ((K k).flow.metric 0).ball (p k) r)
    (hscale : Tendsto (fun k => r ^ 2 * ((K k).flow.connection 0).scalarCurvature (x k))
      atTop atTop) :
    Tendsto (fun k => calibratedMetricVolume ((K k).flow.metric 0)
      (((K k).flow.metric 0).ball (p k) r)) atTop (𝓝 0) := by
  have hfinite (k : ℕ) : calibratedMetricVolume ((K k).flow.metric 0)
      (((K k).flow.metric 0).ball (p k) r) ≠ ⊤ := by
    rw [calibratedMetricVolume_eq_volumeMeasure]
    exact ((K k).flow.metric 0).ball_volume_ne_top_of_metricComplete
      ((K k).complete 0 le_rfl) (p k) r
  apply (ENNReal.tendsto_toReal_zero_iff hfinite).mp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun _ => ha.trans_le ENNReal.toReal_nonneg)
  · intro ε hε
    obtain ⟨A, hA, hbound⟩ := m23_exists_curvature_bound_of_volume_lower_bound
      P hκ (div_pos hε (pow_pos hr 3))
    filter_upwards [hscale.eventually_gt_atTop A] with k hk
    by_contra hn
    have hvol : ENNReal.ofReal ((ε / r ^ 3) * r ^ 3) ≤
        calibratedMetricVolume ((K k).flow.metric 0)
          (((K k).flow.metric 0).ball (p k) r) := by
      rw [div_mul_cancel₀ ε (pow_ne_zero 3 hr.ne')]
      exact (ENNReal.ofReal_le_ofReal (le_of_not_gt hn)).trans_eq
        (ENNReal.ofReal_toReal (hfinite k))
    exact hk.not_ge (hbound (C k) (K k) (hkappa k) (p k) (x k) r hr (hx k) hvol)

theorem m23_exists_half_euclidean_radii_of_volume_collapse
    (C : ℕ → FlowCarrier.{0} 3) (K : ∀ k, AncientKappaSolution 3 (C k).carrier)
    (p : ∀ k, (C k).carrier) {r : ℝ} (hr : 0 < r)
    (hvolume : Tendsto (fun k => calibratedMetricVolume ((K k).flow.metric 0)
      (((K k).flow.metric 0).ball (p k) r)) atTop (𝓝 0)) :
    ∃ N : ℕ, ∃ ρ : ℕ → ℝ,
      (∀ k, 0 < ρ k ∧ ρ k < r ∧
        calibratedMetricVolume ((K (k + N)).flow.metric 0)
          (((K (k + N)).flow.metric 0).ball (p (k + N)) (ρ k)) =
            ENNReal.ofReal ((RiemannianMetric.euclideanUnitBallVolume 3 / 2) * ρ k ^ 3)) ∧
      Tendsto ρ atTop (𝓝 0) := by
  let c : ℝ := RiemannianMetric.euclideanUnitBallVolume 3 / 2
  have hc : 0 < c := half_pos (RiemannianMetric.euclideanUnitBallVolume_pos 3)
  have hcω : c < RiemannianMetric.euclideanUnitBallVolume 3 :=
    half_lt_self (RiemannianMetric.euclideanUnitBallVolume_pos 3)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hvolume.eventually (eventually_lt_nhds
      (ENNReal.ofReal_pos.mpr (mul_pos hc (pow_pos hr 3)))))
  have hexists (k : ℕ) : ∃ ρ : ℝ, 0 < ρ ∧ ρ < r ∧
      calibratedMetricVolume ((K (k + N)).flow.metric 0)
        (((K (k + N)).flow.metric 0).ball (p (k + N)) ρ) =
          ENNReal.ofReal (c * ρ ^ 3) :=
    ((K (k + N)).flow.metric 0).exists_radius_calibrated_volume_eq
      ((K (k + N)).complete 0 le_rfl) (p (k + N)) hr hc hcω
      (hN (k + N) (Nat.le_add_left N k))
  choose ρ hρ0 hρr hρvol using hexists
  refine ⟨N, ρ, fun k => ⟨hρ0 k, hρr k, hρvol k⟩, ?_⟩
  have htail := hvolume.comp (tendsto_add_atTop_nat N)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun k => ha.trans (hρ0 k))
  · intro ε hε
    filter_upwards [htail.eventually (eventually_lt_nhds
      (ENNReal.ofReal_pos.mpr (mul_pos hc (pow_pos hε 3))))] with k hk
    by_contra hn
    have hle : ENNReal.ofReal (c * ε ^ 3) ≤ ENNReal.ofReal (c * ρ k ^ 3) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hε.le (le_of_not_gt hn) 3) hc.le)
    rw [← hρvol k] at hle
    have hsub : ((K (k + N)).flow.metric 0).ball (p (k + N)) (ρ k) ⊆
        ((K (k + N)).flow.metric 0).ball (p (k + N)) r := by
      intro x hx
      exact lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal (hρr k).le)
    exact hk.not_ge (hle.trans (MeasureTheory.measure_mono hsub))

namespace NormalizedKappaSolutionSequence

theorem exists_half_euclidean_radii_of_not_localCurvatureEstimate
    {κ : ℝ} (S : NormalizedKappaSolutionSequence κ)
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hn : ¬ M23LocalCurvatureEstimate S) :
    ∃ (j : ℕ → ℕ) (ρ : ℕ → ℝ),
      (∀ k, 0 < ρ k ∧
        calibratedMetricVolume ((S.term (j k)).flow.flow.metric 0)
          (((S.term (j k)).flow.flow.metric 0).ball (S.term (j k)).base (ρ k)) =
            ENNReal.ofReal ((RiemannianMetric.euclideanUnitBallVolume 3 / 2) * ρ k ^ 3)) ∧
      Tendsto ρ atTop (𝓝 0) := by
  classical
  have hbad : ∃ r : ℝ, 0 < r ∧ ∀ A : ℝ, 0 ≤ A →
      ∃ k : ℕ, ∃ x : (S.term k).carrier.carrier,
        x ∈ ((S.term k).flow.flow.metric 0).ball (S.term k).base r ∧
          A < ((S.term k).flow.flow.connection 0).scalarCurvature x := by
    simpa only [M23LocalCurvatureEstimate, FlowCarrier.metricBall, not_forall, not_exists, not_and,
      not_le, exists_prop] using hn
  obtain ⟨r, hr, hbad⟩ := hbad
  choose j x hx hscalar using fun k : ℕ => hbad ((k : ℝ) / r ^ 2) (by positivity)
  have hscale : Tendsto
      (fun k => r ^ 2 * ((S.term (j k)).flow.flow.connection 0).scalarCurvature (x k))
      atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro k
    have h := (div_lt_iff₀ (pow_pos hr 2)).mp (hscalar k)
    nlinarith
  have hvolume := m23_tendsto_base_ball_volume_zero_of_unbounded_scalar P
    (fun k => (S.term (j k)).carrier) (fun k => (S.term (j k)).flow)
    S.kappa_pos (fun k => (S.term (j k)).kappa_eq)
    (fun k => (S.term (j k)).base) x hr hx hscale
  obtain ⟨N, ρ, hρ, hρlim⟩ := m23_exists_half_euclidean_radii_of_volume_collapse
    (fun k => (S.term (j k)).carrier) (fun k => (S.term (j k)).flow)
    (fun k => (S.term (j k)).base) hr hvolume
  exact ⟨fun k => j (k + N), ρ, fun k => ⟨(hρ k).1, (hρ k).2.2⟩, hρlim⟩

end NormalizedKappaSolutionSequence

end PoincareConjecture
