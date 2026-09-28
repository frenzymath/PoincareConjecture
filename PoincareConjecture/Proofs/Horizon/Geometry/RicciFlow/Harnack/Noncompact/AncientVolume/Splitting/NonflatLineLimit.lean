import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SelectedComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SmallSurfaceLine
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Volume.SmallSelectedLimit













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold

private theorem small_scalarCurvature_pos_of_nonflat_operator
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M J)
    (t : ℝ) (p : M) (hop : (F.connection t).NonnegativeCurvatureOperator p)
    (hnonflat : 0 < (F.connection t).curvatureTensorNorm p) :
    0 < (F.connection t).scalarCurvature p := by
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) (ULift.{u} M) :=
    Poincare.Manifold.uliftChartedSpace _ M
  let : IsManifold (𝓡 n) ∞ (ULift.{u} M) :=
    Poincare.Manifold.uliftIsManifold (𝓡 n) M
  let H : RicciFlow n (ULift.{u} M) J := F.ulift
  have hD := hC.tensor_calculus n (ULift.{u} M) (H.metric t) (H.connection t)
  have hbound := (H.connection t).curvatureTensorNorm_le_scalarCurvature hD
    (ULift.up.{u} p) ((F.ulift_nonnegativeCurvatureOperator_iff t (ULift.up.{u} p)).mpr hop)
  simp only [H, F.ulift_curvatureTensorNorm, F.ulift_scalarCurvature] at hbound
  by_contra! h
  exact (not_lt_of_ge (hbound.trans (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h))) hnonflat

set_option maxHeartbeats 800000 in



theorem exists_nonflat_small_ancient_limit_with_line_of_unbounded_scalar_ratio
    {m : ℕ} (hm : 0 < m) {M : Type u}
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow (m + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ (m + 1)) ≤
        (F.metric t).volumeMeasure ((F.metric t).ball x r))
    {t₀ t₁ : ℝ} (ht₀ : t₀ < 0) (ht₁ : t₁ ≤ 0) (htimeOrder : t₀ ≤ t₁)
    (p : M) (hvolume : 0 < (F.metric t₁).asymptoticVolumeRatio p)
    (hunbounded : ¬ BddAbove (range (fun x =>
      ((F.metric t₀).edist p x).toReal ^ 2 * (F.connection t₀).scalarCurvature x))) :
    ∃ C : FlowCarrier.{0} (m + 1), ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∃ Flim : RicciFlow (m + 1) C.carrier (Iio δ), ∃ base : C.carrier,
        (∀ t ∈ Iio δ, C.metricComplete (Flim.metric t)) ∧
        (∀ t ∈ Iio δ, ∀ x, (Flim.connection t).NonnegativeCurvatureOperator x) ∧
        (∀ t ∈ Iio δ, ∀ x,
          (Flim.connection t).curvatureTensorNorm x ≤ 4 * (((m + 1 : ℕ) : ℝ)) ^ 2) ∧
        0 < (Flim.connection 0).scalarCurvature base ∧
        0 < (Flim.metric 0).asymptoticVolumeRatio base ∧
        (letI := C.metricSpaceOf (Flim.metric 0)
         ∃ γ : ℝ → C.carrier, Isometry γ ∧ γ 0 = base) := by
  obtain ⟨q, r, hQ, hcontrol, hd, _, hL, hdQ, hratio, _, _, _, _, _, _, _,
      ν, _, _, δ, hδ, hδone, G, hGcomplete, hnonflat, hGnorm, hGoperator⟩ :=
    exists_nonflat_small_ancient_rescaled_limit_of_unbounded_scalar_ratio hm hC F
      hcomplete hoperator hK hbound hκ hnoncollapse t₀ ht₀ p hunbounded
  let Q := fun i => (F.connection t₀).scalarCurvature (q i)
  have hline := exists_isometric_line_of_selected_small_rescalings hC hm F
    hcomplete hoperator hK hbound t₀ ht₀ p q r Q
    (fun i => (hcontrol i).1) hQ (fun i => (hcontrol i).2.1)
    hd hdQ hL hratio hδ G (hGcomplete 0 hδ)
  have hAVR := asymptoticVolumeRatio_pos_of_small_buffered_ancient_rescalings hm hC F
    hcomplete hoperator hK hbound ht₀ ht₁ htimeOrder p hvolume q Q hQ hδ G
    (hGcomplete 0 hδ)
  have hscalar := small_scalarCurvature_pos_of_nonflat_operator hC G.limitFlow 0 G.base
    (hGoperator 0 hδ G.base) hnonflat
  exact ⟨G.limitCarrier, δ, hδ, hδone, G.limitFlow, G.base,
    hGcomplete, hGoperator, hGnorm, hscalar, hAVR, hline⟩



theorem false_of_surface_unbounded_scalar_ratio_and_positive_volume
    {M : Type u} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 2 M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 2) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    {t₀ t₁ : ℝ} (ht₀ : t₀ < 0) (ht₁ : t₁ ≤ 0) (htimeOrder : t₀ ≤ t₁)
    (p : M) (hvolume : 0 < (F.metric t₁).asymptoticVolumeRatio p)
    (hunbounded : ¬ BddAbove (range (fun x =>
      ((F.metric t₀).edist p x).toReal ^ 2 * (F.connection t₀).scalarCurvature x))) :
    False := by
  obtain ⟨C, δ, hδ, _, Flim, base, hc, hop, _, hscalar, _, hline⟩ :=
    exists_nonflat_small_ancient_limit_with_line_of_unbounded_scalar_ratio
      (m := 1) (by norm_num) hC F hcomplete hoperator hK hbound hκ hnoncollapse
      ht₀ ht₁ htimeOrder p hvolume hunbounded
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let := C.metricSpaceOf (Flim.metric 0)
  obtain ⟨γ, hγ, _⟩ := hline
  apply Flim.not_minimizing_line_of_nonflat_small_surface hC 0 (hc 0 hδ)
    (hop 0 hδ) ⟨base, hscalar⟩ γ
  intro s t
  change edist (γ s) (γ t) = ENNReal.ofReal |s - t|
  rw [hγ.edist_eq, edist_dist, Real.dist_eq]

end PoincareConjecture.RicciFlow
