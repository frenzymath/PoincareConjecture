import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Input
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Small








set_option autoImplicit false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientRescalingSequence

attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

noncomputable def smallRescalingCarrier : FlowCarrier.{0} n where
  carrier := Shrink.{0} M
  topologicalSpace := inferInstance
  measurableSpace := inferInstance
  borelSpace := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  t2Space := (Poincare.Topology.SecondCountable.homeomorphShrink M).t2Space
  t3Space := (Poincare.Topology.SecondCountable.homeomorphShrink M).t3Space
  secondCountable :=
    (Poincare.Topology.SecondCountable.homeomorphShrink M).symm.isEmbedding.secondCountableTopology
  connected := by
    simpa only [image_univ, EquivLike.range_eq_univ] using
      isConnected_univ.image (Poincare.Topology.SecondCountable.homeomorphShrink M)
        (Poincare.Topology.SecondCountable.homeomorphShrink M).continuous.continuousOn

noncomputable def smallWindowFlow (S : AncientRescalingSequence K) (j k : ℕ) :
    RicciFlow n (Shrink.{0} M)
      (Ioo (compactnessLower j + 1) (compactnessUpper j + 1)) :=
  (S.rescaling k).flow.shrink.translate (-1)
    (by
      rintro t ⟨s, hs, rfl⟩
      have := compactnessUpper_neg j
      change s + -1 < 0
      linarith [hs.2])
    ordConnected_Ioo
    (by
      refine ⟨0, ⟨?_, ?_⟩, (compactnessUpper j + 1) / 2, ⟨?_, ?_⟩, ?_⟩
      all_goals have := compactnessLower_le j
      all_goals have := compactnessUpper_base j
      all_goals linarith)

noncomputable def smallBasedWindow (S : AncientRescalingSequence K) (j k : ℕ) :
    BasedFlow n (compactnessLower j + 1) (compactnessUpper j + 1)
      (smallRescalingCarrier (M := M)) where
  base := equivShrink M (S.base k)
  flow := S.smallWindowFlow j k
  volumeMeasure := (smallRescalingCarrier (M := M)).metricHausdorffVolume
    ((S.smallWindowFlow j k).metric 0)
  spacetimeVectorField := fun _ _ ↦ (1, 0)
  spacetimeVectorField_time := fun _ _ ↦ rfl
  spacetimeVectorField_spatial_zero := fun _ _ ↦ rfl

noncomputable def smallWindowSequence (S : AncientRescalingSequence K) (j : ℕ) :
    PointedFlowSequence n (compactnessLower j + 1) (compactnessUpper j + 1) where
  carrier := fun _ ↦ smallRescalingCarrier (M := M)
  flow := S.smallBasedWindow j

theorem smallBasedWindow_volumeCompatible (S : AncientRescalingSequence K) (j k : ℕ) :
    (S.smallBasedWindow j k).volumeCompatible := rfl

theorem smallBasedWindow_mem_ballAt (S : AncientRescalingSequence K) (j k : ℕ)
    (t r : ℝ) (x : Shrink.{0} M) :
    x ∈ (S.smallBasedWindow j k).ballAt t r ↔
      (equivShrink M).symm x ∈
        ((S.rescaling k).flow.metric (t - 1)).ball (S.base k) r := by
  change ((S.rescaling k).flow.shrink.metric (t - 1)).edist
    (equivShrink M (S.base k)) x < _ ↔ _
  rw [RicciFlow.shrink_edist, Equiv.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem small_window_noncollapsing (S : AncientRescalingSequence K) (j : ℕ)
    (hcurv : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ t ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ x ∈ ((S.rescaling k).flow.metric (-1)).ball (S.base k) 1,
        ((S.rescaling k).flow.connection t).curvatureTensorNorm x ≤ C) :
    ∃ r κ : ℝ, 0 < r ∧ 0 < κ ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (κ * r ^ n) ≤ (S.smallBasedWindow j k).zeroBallVolume r := by
  obtain ⟨C, hC, hbound⟩ := hcurv
  let r : ℝ := (C + 1)⁻¹
  have hCp : 0 < C + 1 := by linarith
  have hr : 0 < r := inv_pos.mpr hCp
  have hr1 : r ≤ 1 := (inv_le_one₀ hCp).2 (by linarith)
  have hrC : C ≤ r⁻¹ ^ 2 := by
    dsimp [r]
    rw [inv_inv]
    nlinarith
  have hcal := ENNReal.toReal_pos (euclideanVolumeCalibration_pos n).ne'
    (euclideanVolumeCalibration_ne_top n)
  refine ⟨r, K.kappa / (euclideanVolumeCalibration n).toReal, hr,
    div_pos K.kappa_pos hcal, ?_⟩
  filter_upwards [hbound] with k hk
  have hnc := (S.rescaling k).noncollapsed (-1) (by norm_num) (S.base k) r hr
    (by
      intro t ht x hx
      have htime : t ∈ Icc (compactnessLower j) (compactnessUpper j) := by
        constructor
        · have := compactnessLower_le j
          nlinarith [ht.1]
        · exact ht.2.trans (compactnessUpper_base j).le
      have hx1 : x ∈ ((S.rescaling k).flow.metric (-1)).ball (S.base k) 1 :=
        lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hr1)
      rw [abs_of_nonneg (show 0 ≤ ((S.rescaling k).flow.connection t).curvatureTensorNorm x
        from Real.sqrt_nonneg _)]
      exact (hk t htime x hx1).trans hrC)
  have hsmall : ENNReal.ofReal (K.kappa * r ^ n) ≤
      calibratedMetricVolume ((S.rescaling k).flow.shrink.metric (-1))
        (((S.rescaling k).flow.shrink.metric (-1)).ball (equivShrink M (S.base k)) r) := by
    rw [calibratedMetricVolume_eq_volumeMeasure, RicciFlow.shrink_volumeMeasure_ball,
      Equiv.symm_apply_apply, ← calibratedMetricVolume_eq_volumeMeasure]
    exact hnc
  have hvol := calibrated_noncollapse_to_hausdorff (smallRescalingCarrier (M := M))
    ((S.rescaling k).flow.shrink.metric (-1))
    (((S.rescaling k).flow.shrink.metric (-1)).ball (equivShrink M (S.base k)) r)
    K.kappa_pos hr hsmall
  simpa only [BasedFlow.zeroBallVolume, BasedFlow.zeroBall, FlowCarrier.metricBall,
    smallBasedWindow, smallWindowFlow, RicciFlow.translate, zero_add,
    smallRescalingCarrier] using hvol

set_option maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
noncomputable def smallCompactnessHypotheses (S : AncientRescalingSequence K) (j : ℕ)
    (hcurv : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ t₀ ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ t ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ x ∈ ((S.rescaling k).flow.metric t₀).ball (S.base k) A,
        ((S.rescaling k).flow.connection t).curvatureTensorNorm x ≤ C) :
    PointedRicciFlowCompactnessHypotheses n
      (compactnessLower j + 1) (compactnessUpper j + 1) where
  time_bounds := by
    have := compactnessLower_le j
    have := compactnessUpper_base j
    constructor <;> linarith
  sequence := S.smallWindowSequence j
  volume_compatibility := by
    change ∀ k, (S.smallBasedWindow j k).volumeCompatible
    exact S.smallBasedWindow_volumeCompatible j
  zero_time_ball_compact := by
    intro A _
    apply Filter.Eventually.of_forall
    intro k
    change IsCompact (closure
      (((S.rescaling k).flow.shrink.metric (0 + -1)).ball (equivShrink M (S.base k)) A))
    rw [zero_add]
    have hcomplete : MetricComplete ((S.rescaling k).flow.shrink.metric (-1)) :=
      ((S.rescaling k).flow.shrink_metricComplete_iff (-1)).2
        ((S.rescaling k).complete (-1) (by norm_num))
    exact ((S.rescaling k).flow.shrink.metric (-1)).isCompact_closure_ball_of_metricComplete
      hcomplete (equivShrink M (S.base k)) A
  spacetime_control := by
    intro A hA I _ _ _ hI
    obtain ⟨C, hC, hbound⟩ := hcurv A hA
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with k hk
    refine ⟨SmoothSpacetimeEmbedding.refl (S.smallBasedWindow j k)
      (I ×ˢ (S.smallBasedWindow j k).zeroBall A), fun _ _ ↦ rfl, hC, ?_⟩
    intro t ht x hx
    change ((S.rescaling k).flow.shrink.connection (t - 1)).curvatureTensorNorm x ≤ C
    rw [RicciFlow.shrink_curvatureTensorNorm]
    apply hk (-1)
    · exact ⟨(compactnessLower_le j).trans (by norm_num), (compactnessUpper_base j).le⟩
    · have ht' := hI ht
      constructor <;> linarith [ht'.1, ht'.2]
    · simpa only [zero_sub] using (S.smallBasedWindow_mem_ballAt j k 0 A x).mp hx
  all_time_curvature_control := by
    intro A hA
    obtain ⟨C, hC, hbound⟩ := hcurv A hA
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with k hk
    dsimp only
    intro t₀ ht₀ t ht x hx
    change ((S.rescaling k).flow.shrink.connection (t - 1)).curvatureTensorNorm x ≤ C
    rw [RicciFlow.shrink_curvatureTensorNorm]
    exact hk (t₀ - 1) ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
      (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩ ((equivShrink M).symm x)
      ((S.smallBasedWindow_mem_ballAt j k t₀ A x).mp hx)
  noncollapsing := by
    apply S.small_window_noncollapsing j
    obtain ⟨C, hC, hbound⟩ := hcurv 1 (by norm_num)
    refine ⟨C, hC, hbound.mono fun k hk ↦ ?_⟩
    exact hk (-1) ⟨(compactnessLower_le j).trans (by norm_num),
      (compactnessUpper_base j).le⟩

theorem smallCompactnessConclusion (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ)
    (hcurv : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ t₀ ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ t ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ x ∈ ((S.rescaling k).flow.metric t₀).ball (S.base k) A,
        ((S.rescaling k).flow.connection t).curvatureTensorNorm x ≤ C) :
    Nonempty (PointedRicciFlowCompactnessConclusion (S.smallCompactnessHypotheses j hcurv)) :=
  P.pointed_compactness (S.smallCompactnessHypotheses j hcurv).time_bounds.1
    (S.smallCompactnessHypotheses j hcurv).time_bounds.2 (S.smallCompactnessHypotheses j hcurv)

end PoincareConjecture.AncientRescalingSequence
