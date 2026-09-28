import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.LocalControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Compactness

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance windowCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)

theorem ball_subset_terminal
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (k : ℕ) (t : ℝ) (ht : t ≤ 0) (q : (C k).carrier) (r : ℝ) :
    ((F k).metric t).ball q r ⊆ ((F k).metric 0).ball q r := by
  apply (F k).ball_subset_terminal_ball_of_ancient_ricci_nonneg q r ht
  intro s hs x _ v
  exact (((F k).connection s).ricci_bounds_of_nonnegative_curvatureOperator
    (P.tensor_calculus 3 (C k).carrier ((F k).metric s) ((F k).connection s))
    x (hop k s hs x) v).1

variable {δ a b : ℝ}

def shiftedWindowFlow (k : ℕ) (ha : a < 0) (hb : 0 < b) (hbδ : b ≤ δ) :
    RicciFlow 3 (C k).carrier (Ioo a b) :=
  (F k).translate (-δ)
    (by rintro _ ⟨t, ht, rfl⟩; change t + -δ ≤ 0; linarith [ht.2])
    ordConnected_Ioo
    (by refine ⟨a / 2, ⟨?_, ?_⟩, b / 2, ⟨?_, ?_⟩, ?_⟩ <;> linarith)

noncomputable def basedWindow (k : ℕ) (ha : a < 0) (hb : 0 < b) (hbδ : b ≤ δ) :
    BasedFlow 3 a b (C k) where
  base := p k
  flow := shiftedWindowFlow C F k ha hb hbδ
  volumeMeasure := (C k).metricHausdorffVolume
    ((shiftedWindowFlow C F k ha hb hbδ).metric 0)
  spacetimeVectorField := fun _ _ => (1, 0)
  spacetimeVectorField_time := fun _ _ => rfl
  spacetimeVectorField_spatial_zero := fun _ _ => rfl

theorem basedWindow_zeroBall (k : ℕ) (ha : a < 0) (hb : 0 < b) (hbδ : b ≤ δ) (r : ℝ) :
    (basedWindow C F p k ha hb hbδ).zeroBall r = ((F k).metric (-δ)).ball (p k) r := by
  simp only [BasedFlow.zeroBall, basedWindow, shiftedWindowFlow,
    RicciFlow.translate, FlowCarrier.metricBall, zero_add]

noncomputable def windowSequence (ha : a < 0) (hb : 0 < b) (hbδ : b ≤ δ) :
    PointedFlowSequence 3 a b where
  carrier := C
  flow := fun k => basedWindow C F p k ha hb hbδ

noncomputable def compactnessHypotheses
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (hκ : 0 < κ)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (hnc : ∀ k, AncientKappaNoncollapsed (F k) κ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (L k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    (ha : a < 0) (hb : 0 < b) (hbδ : b ≤ δ) :
    PointedRicciFlowCompactnessHypotheses 3 a b where
  time_bounds := ⟨ha, hb⟩
  sequence := windowSequence C F p ha hb hbδ
  volume_compatibility := fun _ => rfl
  zero_time_ball_compact := by
    intro A _
    refine Eventually.of_forall fun k => ?_
    change IsCompact (closure ((basedWindow C F p k ha hb hbδ).zeroBall A))
    rw [basedWindow_zeroBall C F p k ha hb hbδ]
    exact ((F k).metric (-δ)).isCompact_closure_ball_of_metricComplete
      (hc k (-δ) (by linarith)) (p k) A
  spacetime_control := by
    intro A hA I _ _ _ hI
    refine ⟨4, by norm_num, ?_⟩
    filter_upwards [hL.eventually_ge_atTop A] with k hk
    refine ⟨SmoothSpacetimeEmbedding.refl (basedWindow C F p k ha hb hbδ)
      (I ×ˢ (basedWindow C F p k ha hb hbδ).zeroBall A), fun _ _ => rfl,
      by norm_num, ?_⟩
    intro t ht x hx
    change x ∈ (basedWindow C F p k ha hb hbδ).zeroBall A at hx
    rw [basedWindow_zeroBall C F p k ha hb hbδ] at hx
    have hx0 := ball_subset_terminal C F P hop k (-δ) (by linarith) (p k) A hx
    exact (le_abs_self _).trans (hbound k (t - δ) (by linarith [(hI ht).2]) x
      (hx0.trans_le (ENNReal.ofReal_le_ofReal hk)))
  all_time_curvature_control := by
    intro A _
    refine ⟨4, by norm_num, ?_⟩
    filter_upwards [hL.eventually_ge_atTop A] with k hk
    dsimp only
    intro t₀ ht₀ t ht x hx
    have hx0 := ball_subset_terminal C F P hop k (t₀ - δ)
      (by linarith [ht₀.2]) (p k) A hx
    exact (le_abs_self _).trans (hbound k (t - δ) (by linarith [ht.2]) x
      (hx0.trans_le (ENNReal.ofReal_le_ofReal hk)))
  noncollapsing := by
    have hcal := ENNReal.toReal_pos (euclideanVolumeCalibration_pos 3).ne'
      (euclideanVolumeCalibration_ne_top 3)
    refine ⟨1 / 2, κ / (euclideanVolumeCalibration 3).toReal,
      by norm_num, div_pos hκ hcal, ?_⟩
    filter_upwards [hL.eventually_ge_atTop (1 / 2)] with k hk
    have hvol := hnc k (1 / 2) (by norm_num) (-δ) (by linarith) (p k)
      (1 / 2) (by norm_num) le_rfl (by
        intro s hs x hx
        have hx0 := ball_subset_terminal C F P hop k (-δ) (by linarith) (p k) (1 / 2) hx
        have h := hbound k s (by linarith [hs.2]) x
          (hx0.trans_le (ENNReal.ofReal_le_ofReal hk))
        norm_num at h ⊢
        exact h)
    have hraw := calibrated_noncollapse_to_hausdorff (C k) ((F k).metric (-δ))
      (((F k).metric (-δ)).ball (p k) (1 / 2)) hκ (by norm_num) hvol
    change ENNReal.ofReal ((κ / (euclideanVolumeCalibration 3).toReal) * (1 / 2) ^ 3) ≤
      (basedWindow C F p k ha hb hbδ).zeroBallVolume (1 / 2)
    simpa only [BasedFlow.zeroBallVolume, BasedFlow.zeroBall, FlowCarrier.metricBall,
      basedWindow, shiftedWindowFlow, RicciFlow.translate, zero_add] using hraw

end PoincareConjecture.RawAncientSequence
