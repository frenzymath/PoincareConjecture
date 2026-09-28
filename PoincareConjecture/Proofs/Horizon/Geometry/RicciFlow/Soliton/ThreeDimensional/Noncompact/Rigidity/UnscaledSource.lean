import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.SourceNoncollapse
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.ScalarBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Small








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

noncomputable section

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S)


def unscaledSourceFlow : RicciFlow 3 M (Iio 1) :=
  G.flow.translate (-1)
    (by rintro _ ⟨t, ht, rfl⟩; change t + -1 < 0; linarith [show t < 1 from ht])
    ordConnected_Iio ⟨-1, by simp, 0, by simp, by norm_num⟩

theorem unscaledSourceFlow_metric_zero : G.unscaledSourceFlow.metric 0 = S.metric := by
  simpa only [unscaledSourceFlow, RicciFlow.translate, zero_add] using G.at_minus_one

theorem unscaledSourceFlow_metric_eq_ancientSourceFlow (t : ℝ) :
    G.unscaledSourceFlow.metric t = G.ancientSourceFlow.metric t := rfl

theorem unscaledSourceFlow_homothetic (t : ℝ) (ht : t < 1) :
    Nonempty (HomotheticMetricSlice S.metric (G.unscaledSourceFlow.metric t) (1 - t)) := by
  have ht' : t + -1 < 0 := by linarith
  have heq : |t + -1| = 1 - t := by rw [abs_of_neg ht']; ring
  simpa only [unscaledSourceFlow, RicciFlow.translate, heq] using
    G.self_similar (t + -1) ht'

theorem unscaledSourceFlow_complete (t : ℝ) (ht : t < 1) :
    MetricComplete (G.unscaledSourceFlow.metric t) := by
  obtain ⟨E⟩ := G.unscaledSourceFlow_homothetic t ht
  exact E.metricComplete (sub_pos.mpr ht) S.complete

theorem unscaledSourceFlow_nonnegativeCurvatureOperator (t : ℝ) (ht : t < 1) (x : M) :
    (G.unscaledSourceFlow.connection t).NonnegativeCurvatureOperator x := by
  obtain ⟨E⟩ := G.unscaledSourceFlow_homothetic t ht
  exact E.nonnegativeCurvatureOperator (sub_pos.mpr ht) S.connection
    (G.unscaledSourceFlow.connection t) S.nonnegative_curvature x

theorem unscaledSourceFlow_metricKappaNoncollapsed (t : ℝ) (ht : t < 1) :
    MetricKappaNoncollapsed (G.unscaledSourceFlow.metric t)
      (G.unscaledSourceFlow.connection t) S.kappa := by
  obtain ⟨E⟩ := G.unscaledSourceFlow_homothetic t ht
  exact E.kappaNoncollapsed (sub_pos.mpr ht) S.connection
    (G.unscaledSourceFlow.connection t) S.kappa_noncollapsed


theorem unscaledSourceFlow_curvature_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, t < 1 → ∀ x : M,
      |(G.unscaledSourceFlow.connection t).curvatureTensorNorm x| ≤ B / (1 - t) := by
  obtain ⟨B, hB, hbound⟩ := S.bounded_curvature
  refine ⟨B, hB, fun t ht x => ?_⟩
  obtain ⟨E⟩ := G.unscaledSourceFlow_homothetic t ht
  rw [E.curvatureNorm (sub_pos.mpr ht) S.connection, abs_mul,
    abs_of_pos (inv_pos.mpr (sub_pos.mpr ht)), div_eq_mul_inv, mul_comm B]
  exact mul_le_mul_of_nonneg_left (hbound _) (inv_nonneg.mpr (sub_pos.mpr ht).le)


theorem unscaledSourceFlow_scalar_lower_bound (hC : RicciFlowCurvatureTheory.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, t < 1 → ∀ x : M,
      c / (1 - t) ≤ (G.unscaledSourceFlow.connection t).scalarCurvature x := by
  obtain ⟨c, hc, hlower⟩ := S.exists_uniform_positive_scalar_lower_bound hC
  refine ⟨c, hc, fun t ht x => ?_⟩
  obtain ⟨E⟩ := G.unscaledSourceFlow_homothetic t ht
  rw [E.scalarCurvature (sub_pos.mpr ht) S.connection, div_eq_mul_inv, mul_comm c]
  exact mul_le_mul_of_nonneg_left (hlower _) (inv_nonneg.mpr (sub_pos.mpr ht).le)

theorem unscaledSourceFlow_past_curvature_bound (b : ℝ) (hb : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≤ b → ∀ x : M,
      |(G.unscaledSourceFlow.connection t).curvatureTensorNorm x| ≤ C := by
  obtain ⟨B, hB, hbound⟩ := G.unscaledSourceFlow_curvature_bound
  refine ⟨B / (1 - b), div_nonneg hB (sub_pos.mpr hb).le, fun t ht x => ?_⟩
  exact (hbound t (ht.trans_lt hb) x).trans
    (div_le_div_of_nonneg_left hB (sub_pos.mpr hb) (by linarith))

attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold RicciFlow.smallT3Space RicciFlow.smallMeasurableSpace
  RicciFlow.smallBorelSpace


def unscaledWindowFlow (a b : ℝ) (ha : a < 0) (hb : 0 < b) (hb1 : b < 1) :
    RicciFlow 3 (Shrink.{0} M) (Ioo a b) :=
  Poincare.Geometry.RicciFlow.Harnack.restrictFlow G.unscaledSourceFlow.shrink
    (fun _ ht => ht.2.trans hb1)
    ordConnected_Ioo ⟨0, ⟨ha, hb⟩, b / 2, ⟨by linarith, by linarith⟩, by linarith⟩

theorem unscaledWindowFlow_metric (a b : ℝ) (ha : a < 0) (hb : 0 < b) (hb1 : b < 1)
    (t : ℝ) : (G.unscaledWindowFlow a b ha hb hb1).metric t =
      G.unscaledSourceFlow.shrink.metric t := rfl

def unscaledBasedWindow (q : ℕ → M) (a b : ℝ) (ha : a < 0) (hb : 0 < b)
    (hb1 : b < 1) (k : ℕ) :
    BasedFlow 3 a b (AncientRescalingSequence.smallRescalingCarrier (M := M)) where
  base := equivShrink M (q k)
  flow := G.unscaledWindowFlow a b ha hb hb1
  volumeMeasure := (AncientRescalingSequence.smallRescalingCarrier (M := M)).metricHausdorffVolume
    ((G.unscaledWindowFlow a b ha hb hb1).metric 0)
  spacetimeVectorField := fun _ _ => (1, 0)
  spacetimeVectorField_time := fun _ _ => rfl
  spacetimeVectorField_spatial_zero := fun _ _ => rfl

def unscaledWindowSequence (q : ℕ → M) (a b : ℝ) (ha : a < 0) (hb : 0 < b)
    (hb1 : b < 1) : PointedFlowSequence 3 a b where
  carrier := fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M)
  flow := G.unscaledBasedWindow q a b ha hb hb1



def unscaledCompactnessHypotheses (q : ℕ → M) (a b : ℝ) (ha : a < 0) (hb : 0 < b)
    (hb1 : b < 1) : PointedRicciFlowCompactnessHypotheses 3 a b where
  time_bounds := ⟨ha, hb⟩
  sequence := G.unscaledWindowSequence q a b ha hb hb1
  volume_compatibility := fun _ => rfl
  zero_time_ball_compact := by
    intro A _
    apply Filter.Eventually.of_forall
    intro k
    change IsCompact (closure ((G.unscaledSourceFlow.shrink.metric 0).ball
      (equivShrink M (q k)) A))
    exact (G.unscaledSourceFlow.shrink.metric 0).isCompact_closure_ball_of_metricComplete
      ((G.unscaledSourceFlow.shrink_metricComplete_iff 0).mpr
        (G.unscaledSourceFlow_complete 0 (by norm_num))) (equivShrink M (q k)) A
  spacetime_control := by
    intro A _ I _ _ _ hI
    obtain ⟨C, hC, hbound⟩ := G.unscaledSourceFlow_past_curvature_bound b hb1
    refine ⟨C, hC, Filter.Eventually.of_forall fun k => ?_⟩
    refine ⟨SmoothSpacetimeEmbedding.refl (G.unscaledBasedWindow q a b ha hb hb1 k)
      (I ×ˢ (G.unscaledBasedWindow q a b ha hb hb1 k).zeroBall A),
      fun _ _ => rfl, hC, ?_⟩
    intro t ht x _
    change (G.unscaledSourceFlow.shrink.connection t).curvatureTensorNorm x ≤ C
    rw [RicciFlow.shrink_curvatureTensorNorm]
    exact (le_abs_self _).trans (hbound t (hI ht).2.le _)
  all_time_curvature_control := by
    intro A _
    obtain ⟨C, hC, hbound⟩ := G.unscaledSourceFlow_past_curvature_bound b hb1
    refine ⟨C, hC, Filter.Eventually.of_forall fun k => ?_⟩
    dsimp only
    intro t₀ _ t ht x _
    change (G.unscaledSourceFlow.shrink.connection t).curvatureTensorNorm x ≤ C
    rw [RicciFlow.shrink_curvatureTensorNorm]
    exact (le_abs_self _).trans (hbound t ht.2.le _)
  noncollapsing := by
    obtain ⟨B, hB, hbound⟩ := G.unscaledSourceFlow_past_curvature_bound 0 (by norm_num)
    let r : ℝ := (B + 1)⁻¹
    have hr : 0 < r := inv_pos.mpr (by linarith)
    have hrB : B ≤ r⁻¹ ^ 2 := by dsimp [r]; rw [inv_inv]; nlinarith
    have hcal := ENNReal.toReal_pos (euclideanVolumeCalibration_pos 3).ne'
      (euclideanVolumeCalibration_ne_top 3)
    refine ⟨r, S.kappa / (euclideanVolumeCalibration 3).toReal, hr,
      div_pos S.kappa_pos hcal, Filter.Eventually.of_forall fun k => ?_⟩
    have hκ := G.unscaledSourceFlow.metricKappaNoncollapsed_shrink 0
      (G.unscaledSourceFlow_metricKappaNoncollapsed 0 (by norm_num))
    have hsmall := hκ.2 (equivShrink M (q k)) r hr (by
      intro x _
      rw [RicciFlow.shrink_curvatureTensorNorm]
      exact (hbound 0 le_rfl _).trans hrB)
    have hvol := calibrated_noncollapse_to_hausdorff
      (AncientRescalingSequence.smallRescalingCarrier (M := M))
      (G.unscaledSourceFlow.shrink.metric 0)
      ((G.unscaledSourceFlow.shrink.metric 0).ball (equivShrink M (q k)) r)
      S.kappa_pos hr hsmall
    simpa only [BasedFlow.zeroBallVolume, BasedFlow.zeroBall, FlowCarrier.metricBall,
      unscaledWindowSequence, unscaledBasedWindow, unscaledWindowFlow,
      Poincare.Geometry.RicciFlow.Harnack.restrictFlow,
      AncientRescalingSequence.smallRescalingCarrier] using hvol

end PoincareConjecture.ShrinkingSolitonFlow
