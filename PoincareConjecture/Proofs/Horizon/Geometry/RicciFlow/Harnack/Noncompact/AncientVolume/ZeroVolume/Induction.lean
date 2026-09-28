import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.DimensionReduction











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable




theorem zero_volume_of_unbounded_scalar_ratio_in_all_dimensions
    (hC : RicciFlowCurvatureTheory.{u})
    (hASCR : ∀ d : ℕ, 2 ≤ d → ∀ C : FlowCarrier.{u} d,
      NoncompactSpace C.carrier → ∀ G : RicciFlow d C.carrier (Iic 0),
      (∀ t ≤ 0, MetricComplete (G.metric t)) →
      (∀ t ≤ 0, ∀ x, (G.connection t).NonnegativeCurvatureOperator x) →
      ∀ K : ℝ, 0 ≤ K →
      (∀ t ≤ 0, ∀ x, (G.connection t).curvatureTensorNorm x ≤ K) →
      ∀ κ : ℝ, 0 < κ →
      (∀ t ≤ 0, ∀ x, ∀ r : ℝ, 0 < r →
        (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (G.metric t).ball x r,
          (G.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
        ENNReal.ofReal (κ * r ^ d) ≤ (G.metric t).volumeMeasure ((G.metric t).ball x r)) →
      (∃ q, 0 < (G.connection 0).scalarCurvature q) →
      ∀ t : ℝ, t < 0 → ∀ p,
        ¬ BddAbove (range (fun x =>
          ((G.metric t).edist p x).toReal ^ 2 * (G.connection t).scalarCurvature x)))
    {n : ℕ} (hn : 2 ≤ n) {M : Type u}
    [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [NoncompactSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hnonflat : ∃ q, 0 < (F.connection 0).scalarCurvature q) :
    ∀ t ≤ 0, ∀ p : M, (F.metric t).asymptoticVolumeRatio p = 0 ∧
      Tendsto (fun r : ℝ =>
        ((F.metric t).volumeMeasure ((F.metric t).ball p r)).toReal / r ^ n)
        atTop (𝓝 0) := by
  have hnoPositive : ∀ d : ℕ, 2 ≤ d → ∀ C : FlowCarrier.{u} d,
      NoncompactSpace C.carrier → ∀ G : RicciFlow d C.carrier (Iic 0),
      (∀ t ≤ 0, MetricComplete (G.metric t)) →
      (∀ t ≤ 0, ∀ x, (G.connection t).NonnegativeCurvatureOperator x) →
      ∀ K : ℝ, 0 ≤ K →
      (∀ t ≤ 0, ∀ x, (G.connection t).curvatureTensorNorm x ≤ K) →
      ∀ κ : ℝ, 0 < κ →
      (∀ t ≤ 0, ∀ x, ∀ r : ℝ, 0 < r →
        (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (G.metric t).ball x r,
          (G.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
        ENNReal.ofReal (κ * r ^ d) ≤ (G.metric t).volumeMeasure ((G.metric t).ball x r)) →
      (∃ q, 0 < (G.connection 0).scalarCurvature q) →
      ∀ t ≤ 0, ∀ p, ¬ 0 < (G.metric t).asymptoticVolumeRatio p := by
    apply Nat.le_induction
    · intro C hNC G hc hop K hK hb κ hκ hcollapse hflat t ht p hv
      let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      let : NoncompactSpace C.carrier := hNC
      have hunbounded := hASCR 2 le_rfl C hNC G hc hop K hK hb κ hκ hcollapse hflat
        (t - 1) (by linarith) p
      exact false_of_surface_unbounded_scalar_ratio_and_positive_volume hC G hc hop
        hK hb hκ hcollapse (by linarith : t - 1 < 0) ht (by linarith : t - 1 ≤ t)
        p hv hunbounded
    · intro d hd ih C hNC G hc hop K hK hb κ hκ hcollapse hflat t ht p hv
      let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
      let : NoncompactSpace C.carrier := hNC
      have hunbounded := hASCR (d + 1) (by omega) C hNC G hc hop K hK hb κ hκ
        hcollapse hflat (t - 1) (by linarith) p
      obtain ⟨D, hDNC, H, base, κ', hκ', hcomp, hcurv, hnorm, hscalar, hvolume,
          _, hparabolic⟩ :=
        exists_lower_dimensional_ancient_flow_of_unbounded_scalar_ratio (by omega)
          hC G hc hop hK hb hκ hcollapse (by linarith : t - 1 < 0) ht
          (by linarith : t - 1 ≤ t) p hv hunbounded
      exact ih D hDNC H hcomp hcurv (4 * (((d + 1 : ℕ) : ℝ)) ^ 2) (by positivity)
        hnorm κ' hκ' hparabolic ⟨base, hscalar⟩ 0 le_rfl base hvolume
  let C : FlowCarrier.{u} n := FlowCarrier.ofConnectedManifold n M
  have hno := hnoPositive n hn C (show NoncompactSpace M from inferInstance)
    F hcomplete hoperator K hK hbound κ hκ hnoncollapse hnonflat
  intro t ht p
  have hRic (x : M) (v : TangentSpace (𝓡 n) x) :
      0 ≤ (F.connection t).ricci x v v :=
    ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus n M (F.metric t) (F.connection t)) x (hoperator t ht x) v).1
  have hlimit := (F.metric t).tendsto_asymptoticVolumeRatio (F.connection t)
    (by omega) (hcomplete t ht) hRic p
  have hnonnegative : 0 ≤ (F.metric t).asymptoticVolumeRatio p := by
    apply ge_of_tendsto hlimit
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    positivity
  have hzero := le_antisymm (le_of_not_gt (hno t ht p)) hnonnegative
  exact ⟨hzero, by simpa only [hzero] using hlimit⟩

end PoincareConjecture.RicciFlow
