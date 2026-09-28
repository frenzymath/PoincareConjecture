import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Windows
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Calibration

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientRescalingSequence

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M}

theorem window_noncollapsing (S : AncientRescalingSequence K) (j : ℕ)
    (hcurv : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ t ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ x ∈ ((S.rescaling k).flow.metric (-1)).ball (S.base k) 1,
        ((S.rescaling k).flow.connection t).curvatureTensorNorm x ≤ C) :
    ∃ r κ : ℝ, 0 < r ∧ 0 < κ ∧ ∀ᶠ k in atTop,
      ENNReal.ofReal (κ * r ^ n) ≤ (S.basedWindow j k).zeroBallVolume r := by
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
      have hx1 : x ∈ ((S.rescaling k).flow.metric (-1)).ball (S.base k) 1 := by
        exact lt_of_lt_of_le hx (ENNReal.ofReal_le_ofReal hr1)
      rw [abs_of_nonneg (show 0 ≤ ((S.rescaling k).flow.connection t).curvatureTensorNorm x
        from Real.sqrt_nonneg _)]
      exact (hk t htime x hx1).trans hrC)
  have hvol := calibrated_noncollapse_to_hausdorff (sourceCarrier (M := M))
    ((S.rescaling k).flow.metric (-1))
    (((S.rescaling k).flow.metric (-1)).ball (S.base k) r) K.kappa_pos hr hnc
  simpa only [BasedFlow.zeroBallVolume, BasedFlow.zeroBall, FlowCarrier.metricBall,
    basedWindow, shiftedWindowFlow, RicciFlow.translate, zero_add] using hvol

noncomputable def compactnessHypotheses (S : AncientRescalingSequence K) (j : ℕ)
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
  sequence := S.windowSequence j
  volume_compatibility := S.basedWindow_volumeCompatible j
  zero_time_ball_compact := fun A _ ↦ Filter.Eventually.of_forall fun k ↦
    S.basedWindow_zeroBall_compact j k A
  spacetime_control := by
    intro A hA I _ _ _ hI
    obtain ⟨C, hC, hbound⟩ := hcurv A hA
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with k hk
    refine ⟨SmoothSpacetimeEmbedding.refl (S.basedWindow j k)
      (I ×ˢ (S.basedWindow j k).zeroBall A), fun _ _ ↦ rfl, hC, ?_⟩
    intro t ht x hx
    change ((S.rescaling k).flow.connection (t - 1)).curvatureTensorNorm x ≤ C
    apply hk (-1)
    · exact ⟨(compactnessLower_le j).trans (by norm_num), (compactnessUpper_base j).le⟩
    · have ht' := hI ht
      constructor <;> linarith [ht'.1, ht'.2]
    · exact (S.basedWindow_zeroBall j k A) ▸ hx
  all_time_curvature_control := by
    intro A hA
    obtain ⟨C, hC, hbound⟩ := hcurv A hA
    refine ⟨C, hC, ?_⟩
    filter_upwards [hbound] with k hk
    dsimp only
    intro t₀ ht₀ t ht x hx
    exact hk (t₀ - 1) ⟨by linarith [ht₀.1], by linarith [ht₀.2]⟩
      (t - 1) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x hx
  noncollapsing := by
    apply S.window_noncollapsing j
    obtain ⟨C, hC, hbound⟩ := hcurv 1 (by norm_num)
    refine ⟨C, hC, hbound.mono fun k hk ↦ ?_⟩
    exact hk (-1) ⟨(compactnessLower_le j).trans (by norm_num),
      (compactnessUpper_base j).le⟩

theorem compactnessConclusion (S : AncientRescalingSequence K)
    (P : AncientAsymptoticSolitonPredecessors K) (j : ℕ)
    (hcurv : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop,
      ∀ t₀ ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ t ∈ Icc (compactnessLower j) (compactnessUpper j),
      ∀ x ∈ ((S.rescaling k).flow.metric t₀).ball (S.base k) A,
        ((S.rescaling k).flow.connection t).curvatureTensorNorm x ≤ C) :
    Nonempty (PointedRicciFlowCompactnessConclusion (S.compactnessHypotheses j hcurv)) :=
  P.pointed_compactness (S.compactnessHypotheses j hcurv).time_bounds.1
    (S.compactnessHypotheses j hcurv).time_bounds.2 (S.compactnessHypotheses j hcurv)

end PoincareConjecture.AncientRescalingSequence
