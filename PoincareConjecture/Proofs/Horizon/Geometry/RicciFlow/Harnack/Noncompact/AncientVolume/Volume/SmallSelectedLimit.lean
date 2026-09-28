import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SmallRescaledLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.RescaledLimit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.AsymptoticRatio
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Lift

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold
  smallT3Space smallMeasurableSpace smallBorelSpace

private theorem ricci_nonneg_small
    {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {J : Set ℝ} (F : RicciFlow n M J)
    (t : ℝ) (hoperator : ∀ x, (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ x : M, ∀ v : TangentSpace (𝓡 n) x, 0 ≤ (F.connection t).ricci x v v := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} M) :=
    Poincare.Manifold.uliftChartedSpace _ M
  let : IsManifold (𝓡 n) ∞ (ULift.{u} M) :=
    Poincare.Manifold.uliftIsManifold (𝓡 n) M
  let H : RicciFlow n (ULift.{u} M) J := F.ulift
  let e := Poincare.Manifold.uliftDiffeomorph (𝓡 n) M
  intro x v
  let z : ULift.{u} M := ULift.up x
  obtain ⟨w, hw⟩ := (e.mfderivToContinuousLinearEquiv (by simp) z).surjective v
  change mfderiv (𝓡 n) (𝓡 n) e z w = v at hw
  have hnonneg := ((H.connection t).ricci_bounds_of_nonnegative_curvatureOperator
    (hC.tensor_calculus n (ULift.{u} M) (H.metric t) (H.connection t)) z
    ((F.ulift_nonnegativeCurvatureOperator_iff t z).mpr (hoperator x)) w).1
  change 0 ≤ ((F.pullbackDiffeomorph e).connection t).ricci z w w at hnonneg
  rw [F.pullbackDiffeomorph_ricci, hw] at hnonneg
  exact hnonneg

theorem asymptoticVolumeRatio_pos_of_small_buffered_ancient_rescalings
    {m : ℕ} (hm : 0 < m) {M : Type u}
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {t₀ t₁ : ℝ} (ht₀ : t₀ < 0) (ht₁ : t₁ ≤ 0) (htimeOrder : t₀ ≤ t₁)
    (p : M) (hvolume : 0 < (F.metric t₁).asymptoticVolumeRatio p)
    (q : ℕ → M) (Q : ℕ → ℝ) (hQ : ∀ k, 0 < Q k)
    {δ : ℝ} (hδ : 0 < δ)
    (G : AncientPointedGeometricConvergence
      (fun _ => (FlowCarrier.ofConnectedManifold (m + 1) M).shrink)
      (fun k t => (F.interiorAncientRescaleAt (Q k) (hQ k) t₀).shrink.metric (t - δ))
      (fun k => equivShrink M (q k)) δ)
    (hlimitComplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    0 < (G.limitFlow.metric 0).asymptoticVolumeRatio G.base := by
  let H := fun k => F.interiorAncientRescaleAt (Q k) (hQ k) t₀
  let Fseq := fun k => (H k).shrink.bufferedExpandingFlow δ
  have htime : ∀ a b : ℝ, b < δ → ∀ᶠ k in atTop,
      Icc a b ⊆ (fun t : ℝ => t - δ) ⁻¹' Iio (-t₀ * Q k) := by
    intro a b hb
    exact Eventually.of_forall (fun k t ht =>
      (sub_neg.mpr (ht.2.trans_lt hb)).trans
        (mul_pos (neg_pos.mpr ht₀) (hQ k)))
  have hsourceTime (k : ℕ) {t : ℝ} (ht : t < δ) :
      t₀ + (t - δ) / Q k ≤ 0 := by
    have hdiv := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht.le) (hQ k).le
    linarith
  have hlimitOperator : ∀ t ∈ Iio δ, ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).NonnegativeCurvatureOperator x := by
    apply AncientPointedGeometricConvergence.nonnegativeCurvatureOperator_of_eventually
      (C := fun _ => (FlowCarrier.ofConnectedManifold (m + 1) M).shrink) Fseq G hδ htime
    intro t ht
    apply Eventually.of_forall
    intro k x
    change ((H k).shrink.connection (t - δ)).NonnegativeCurvatureOperator x
    rw [shrink_nonnegativeCurvatureOperator_iff]
    apply F.parabolicRescale_nonnegativeCurvatureOperator
    exact hoperator _ (hsourceTime k ht) _
  have hRic : ∀ x : G.limitCarrier.carrier, ∀ w : TangentSpace (𝓡 (m + 1)) x,
      0 ≤ (G.limitFlow.connection 0).ricci x w w :=
    ricci_nonneg_small hC G.limitFlow 0 (hlimitOperator 0 hδ)
  let v := (F.metric t₁).asymptoticVolumeRatio p / 2 ^ (m + 1)
  have hv : 0 < v := div_pos hvolume (by positivity)
  apply AncientPointedGeometricConvergence.asymptoticVolumeRatio_pos_of_source_ball_volume_lower_bound
    (C := fun _ => (FlowCarrier.ofConnectedManifold (m + 1) M).shrink) Fseq G
      (by omega) hδ htime hlimitComplete hRic hv
  intro r hr
  apply Eventually.of_forall
  intro k
  let τ := t₀ + (0 - δ) / Q k
  have hτ₀ : τ ≤ 0 := hsourceTime k hδ
  have hτ₁ : τ ≤ t₁ := by
    have hdiv := div_nonpos_of_nonpos_of_nonneg
      (show 0 - δ ≤ 0 by linarith) (hQ k).le
    dsimp [τ]
    linarith
  have hratio : (F.metric t₁).asymptoticVolumeRatio p ≤
      (F.metric τ).asymptoticVolumeRatio p :=
    F.antitoneOn_asymptoticVolumeRatio_of_bounded_ancient hC hm
      hcomplete hoperator hK hbound p hτ₀ ht₁ hτ₁
  have hscaled := (F.metric τ).rescaled_ball_volume_lower_bound_of_asymptoticVolumeRatio
    (F.connection τ) (by omega) (hcomplete τ hτ₀)
    (fun x w => ((F.connection τ).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M (F.metric τ) (F.connection τ))
        x (hoperator τ hτ₀ x) w).1)
    p (q k) ((F.metric τ).edist_ne_top p (q k)) (hvolume.trans_le hratio)
    (Q k) (hQ k) hr
  change ENNReal.ofReal (v * r ^ (m + 1)) ≤
    ((H k).shrink.metric (0 - δ)).volumeMeasure
      (((H k).shrink.metric (0 - δ)).ball (equivShrink M (q k)) r)
  rw [shrink_volumeMeasure_ball, Equiv.symm_apply_apply]
  exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hratio (by positivity : (0 : ℝ) ≤ 2 ^ (m + 1)))
      (pow_nonneg hr.le (m + 1)))).trans hscaled

end PoincareConjecture.RicciFlow
